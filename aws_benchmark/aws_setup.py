# run wait_start then
# run setup first, then run refresh to update all nodes with the new config file

import boto3
import json
import os
import multiprocessing
import paramiko

# parser = argparse.ArgumentParser(description="This program autocreates, starts, and stop Amazon EC2 Instancess.")
# parser.add_argument("-create", default=0, help="Number of new instances to create")
# parser.add_argument("-start", default=0, help="Number of new instances to start")
# parser.add_argument("-stop", default=0, help="Number of new instances to stop")
# parser.add_argument("-terminate", default=0, help="Number of new instances to terminate")
# parser.add_argument("-stats", default=False, help="Number of new instances to terminate")
# parser.add_argument("-run", default=True, help="Command to run on running instances")
# parser.add_argument("-setup", default=False, help="Setup instances")
# parser.add_argument("-hostname", default=False, help="Print all hostnames of running instances")
# parser.add_argument("-verify", default=False, help="verify setup")

ec2_resource = boto3.resource("ec2",
                              aws_access_key_id=os.environ["AWS_ACCESS_KEY_ID"],
                              aws_secret_access_key=os.environ["AWS_SECRET_ACCESS_KEY"],
                              region_name="us-east-2")


def create_instances(num):
    instances = ec2_resource.create_instances(ImageId="ami-05b63781e32145c7f",
                                              InstanceType="t2.micro",
                                              KeyName="the-key-to-her-heart",
                                              MinCount=1,
                                              MaxCount=num,
                                              Monitoring={"Enabled": False},
                                              SecurityGroups=[
                                                  "circ4mpc"]
                                              )
    print("Created {} instances".format(num))


def start_instances(num):
    stopped_instances = list(ec2_resource.instances.filter(
        Filters=[{"Name": "instance-state-name", "Values": ["stopped"]}]))
    count = 0
    num = min(num, len(stopped_instances))
    for i in range(num):
        instance = stopped_instances[i]
        ec2_resource.instances.filter(InstanceIds=[instance.id]).start()
        count += 1
    print("Started {} instances".format(count))


def stop_instances(num):
    running_instances = list(ec2_resource.instances.filter(
        Filters=[{"Name": "instance-state-name", "Values": ["running"]}]))
    count = 0
    num = min(num, len(running_instances))
    for i in range(num):
        instance = running_instances[i]
        print("Stopping", instance.public_dns_name)
        ec2_resource.instances.filter(InstanceIds=[instance.id]).stop()
        count += 1
    print("Stopped {} instances".format(count))


def terminate_instances(num):
    instances = list(ec2_resource.instances.filter(
        Filters=[{"Name": "instance-state-name", "Values": ["running", "stopped"]}]))
    count = 0
    num = min(num, len(instances))
    for i in range(num):
        instance = instances[i]
        count += 1
        ec2_resource.instances.filter(InstanceIds=[instance.id]).terminate()
    print("Terminated {} instances".format(count))


def get_stats():
    stats = {}
    stats["total"] = len(list(ec2_resource.instances.filter(Filters=[
                         {"Name": "instance-state-name", "Values": ["running", "stopped", "pending", "stopping"]}])))
    stats["running"] = len(list(ec2_resource.instances.filter(
        Filters=[{"Name": "instance-state-name", "Values": ["running"]}])))
    stats["stopped"] = len(list(ec2_resource.instances.filter(
        Filters=[{"Name": "instance-state-name", "Values": ["stopped"]}])))
    stats["pending"] = len(list(ec2_resource.instances.filter(
        Filters=[{"Name": "instance-state-name", "Values": ["pending"]}])))
    stats["stopping"] = len(list(ec2_resource.instances.filter(
        Filters=[{"Name": "instance-state-name", "Values": ["stopping"]}])))
    print(json.dumps(stats, indent=4))

    print(list(ec2_resource.instances.filter(
        Filters=[{"Name": "instance-state-name", "Values": ["running"]}])))

    instances = list(ec2_resource.instances.filter(
        Filters=[{"Name": "instance-state-name", "Values": ["running"]}]))

    for i in instances:
        print(i.private_ip_address)


def setup_instances(num):
    running_instances = list(ec2_resource.instances.filter(
        Filters=[{"Name": "instance-state-name", "Values": ["running"]}]))
    if len(running_instances) < num:
        print("Not all instances are up yet!")
        return

    running_instance_ips = [
        instance.public_dns_name for instance in running_instances]

    pool = multiprocessing.Pool(len(running_instance_ips))
    pool.map(setup_worker, running_instance_ips)


def setup_worker(ip):
    print("Setting up", ip)
    key = paramiko.RSAKey.from_private_key_file("the-key-to-her-heart.pem")
    client = paramiko.SSHClient()
    client.set_missing_host_key_policy(paramiko.AutoAddPolicy())
    client.connect(hostname=ip, username="ubuntu", pkey=key)

    stdin, stdout, stderr = client.exec_command(
        "cd ~ && git clone https://github.com/circify/circ.git && cd ~/circ && git checkout mpc_aws && cd ~ && chmod 700 ./circ/aws_benchmark/setup.sh && ./circ/aws_benchmark/setup.sh")
    stdin.flush()

    if stdout.channel.recv_exit_status():
        print(ip, " failed setup")

    client.close()


def run_benchmarks(num):
    assert(num == 2)
    running_instances = list(ec2_resource.instances.filter(
        Filters=[{"Name": "instance-state-name", "Values": ["running"]}]))
    if len(running_instances) < num:
        print("Not all instances are up yet!")
        return

    running_instance_ips = [
        instance.public_dns_name for instance in running_instances]
    running_instance_private_ips = [
        running_instances[0].private_ip_address for _ in running_instances]
    roles = [0, 1]
    pool = multiprocessing.Pool(len(running_instance_ips))
    pool.map(setup_worker, running_instance_ips,
             running_instance_private_ips, roles)


def benchmark_worker(ip, connect_ip, role):
    print("Running benchmark", ip)
    key = paramiko.RSAKey.from_private_key_file("the-key-to-her-heart.pem")
    client = paramiko.SSHClient()
    client.set_missing_host_key_policy(paramiko.AutoAddPolicy())
    client.connect(hostname=ip, username="ubuntu", pkey=key)

    stdin, stdout, stderr = client.exec_command(
        "cd ~ && chmod 700 ./circ/aws_benchmark/benchmark.sh && ./circ/aws_benchmark/benchmark.sh {} {} > benchmark.log".format(connect_ip, role))
    stdin.flush()

    if stdout.channel.recv_exit_status():
        print(ip, " failed running benchmark")

    client.close()


# create_instances(2)
# setup_instances(2)
run_benchmarks(2)


# stop_instances(4)
# terminate_instances(4)

# get_stats()

# setup_instances(1)

# stop_instances(2)
# terminate_instances(2)
