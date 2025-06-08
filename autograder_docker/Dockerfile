FROM eecsautograder/ubuntu24:latest

RUN apt-get update --fix-missing 

# Install python and dependencies
RUN apt-get install -y python3.12-full
RUN apt-get install -y python3-lark

RUN apt-get install -y wget
RUN apt-get install -y unzip

# download and install deduce
RUN wget https://github.com/jsiek/deduce/releases/latest/download/deduce-release.zip 
RUN unzip deduce-release.zip
RUN python3.12 deduce/deduce.py --version

# Cache library files
RUN python3.12 deduce/deduce.py deduce/lib 