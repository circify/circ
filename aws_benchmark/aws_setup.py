import boto3
import json
import os
import multiprocessing
import paramiko
import subprocess
import sys

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


def stats():
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


def hosts():
    running_instances = list(ec2_resource.instances.filter(
        Filters=[{"Name": "instance-state-name", "Values": ["running"]}]))
    running_instance_ips = [
        instance.public_dns_name for instance in running_instances]

    for ip in running_instance_ips:
        print("ssh -i \"the-key-to-her-heart.pem\" ubuntu@{}".format(ip))


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

    _, stdout, _ = client.exec_command("cd ~/ABY")
    if stdout.channel.recv_exit_status():
        _, stdout, _ = client.exec_command(
            "cd ~ && git clone https://github.com/circify/circ.git && cd ~/circ && git checkout mpc_aws && cd ~ && chmod 700 ./circ/aws_benchmark/setup.sh && ./circ/aws_benchmark/setup.sh")
        if stdout.channel.recv_exit_status():
            print(ip, " failed setup")

    print("Set up:", ip)
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
    pool.starmap(benchmark_worker,  zip(running_instance_ips,
                                        running_instance_private_ips, roles))


def benchmark_worker(ip, connect_ip, role):
    print("Running benchmark:\nip: {}\nconnect: {}\nrole: {}\n".format(
        ip, connect_ip, role))
    key = paramiko.RSAKey.from_private_key_file("the-key-to-her-heart.pem")
    client = paramiko.SSHClient()
    client.set_missing_host_key_policy(paramiko.AutoAddPolicy())
    client.connect(hostname=ip, username="ubuntu", pkey=key)

    _, stdout, _ = client.exec_command(
        "cd ~ && chmod 700 ./circ/aws_benchmark/benchmark.sh && ./circ/aws_benchmark/benchmark.sh {} {} > benchmark.log".format(connect_ip, role))

    if stdout.channel.recv_exit_status():
        print(ip, " failed running benchmark")

    client.close()


def refresh_instances():
    running_instances = list(ec2_resource.instances.filter(
        Filters=[{"Name": "instance-state-name", "Values": ["running"]}]))
    running_instance_ips = [
        instance.public_dns_name for instance in running_instances]
    pool = multiprocessing.Pool(len(running_instance_ips))
    pool.map(refresh_worker, running_instance_ips)


def refresh_worker(ip):
    print("Refreshing: {}".format(ip))
    key = paramiko.RSAKey.from_private_key_file("the-key-to-her-heart.pem")
    client = paramiko.SSHClient()
    client.set_missing_host_key_policy(paramiko.AutoAddPolicy())
    client.connect(hostname=ip, username="ubuntu", pkey=key)

    _, stdout, _ = client.exec_command(
        "cd ~/ABY && git pull && cd ~/ABY/build && make && cd ~/circ && git pull")

    if stdout.channel.recv_exit_status():
        print(ip, " failed running benchmark")

    client.close()


def logs():
    running_instances = list(ec2_resource.instances.filter(
        Filters=[{"Name": "instance-state-name", "Values": ["running"]}]))
    running_instance_ips = [
        instance.public_dns_name for instance in running_instances]

    for dns_name in running_instance_ips:
        if not os.path.exists("./logs/"):
            os.mkdir("./logs/")
        if not os.path.exists("./logs/"+dns_name):
            os.mkdir("./logs/"+dns_name)

        subprocess.call("scp -o StrictHostKeyChecking=no -i the-key-to-her-heart.pem ubuntu@" +
                        dns_name+":~/*.log ./logs/"+dns_name, shell=True)

        key = paramiko.RSAKey.from_private_key_file("the-key-to-her-heart.pem")
        client = paramiko.SSHClient()
        client.set_missing_host_key_policy(paramiko.AutoAddPolicy())

        client.connect(hostname=dns_name, username="ubuntu", pkey=key)
        _, stdout, _ = client.exec_command(
            "rm -rf ./*.log")

        if stdout.channel.recv_exit_status():
            print(dns_name, " failed to remove logs.")
        client.close()


if __name__ == "__main__":
    last_cmd = ""
    while True:
        cmds = input("> ").split(" ")
        cmd_type = cmds[0]

        # press enter to redo
        if cmd_type == "" and last_cmd != "":
            cmd_type = last_cmd
        else:
            last_cmd = cmd_type

        if cmd_type == "help":
            print("Not again... oh well here you go\n")
            print("EC2: \tcreate start stop terminate stats")
            print("Setup: \tsetup refresh")
            print("Run: \tbenchmark")
            print("Logs: \tlogs")
            print("Misc: \tstats hosts")
            print("Quit: \tquit q")
        elif cmd_type == "create":
            create_instances(2)
        elif cmd_type == "start":
            start_instances(2)
        elif cmd_type == "setup":
            setup_instances(2)
        elif cmd_type == "benchmark":
            run_benchmarks(2)
        elif cmd_type == "stop":
            stop_instances(2)
        elif cmd_type == "terminate":
            terminate_instances(2)
        elif cmd_type == "stats":
            stats()
        elif cmd_type == "hosts":
            hosts()
        elif cmd_type == "refresh":
            refresh_instances()
        elif cmd_type == "logs":
            logs()
        elif cmd_type in ["quit", "q", "exit"]:
            sys.exit(0)
        else:
            print("unlucky, not a cmd")
