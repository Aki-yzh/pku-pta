FROM eclipse-temurin:17-jdk
RUN apt-get update -y && apt-get install -y python3 python3-pip unzip
RUN pip3 install psutil --break-system-packages

RUN useradd -m student
RUN chmod 700 /mnt

ADD --chown=student:student java-benchmarks /home/student/java-benchmarks

COPY main.py /root/main.py

CMD python3 -u /root/main.py 2>&1 | tee -a /root/main.stdout
