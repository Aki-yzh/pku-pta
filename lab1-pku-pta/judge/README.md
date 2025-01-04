`lab1_submitter` 是评测机源码。

请安装 Docker，然后运行 `init.sh` 来构建评测环境。如果在构建过程中遇到网络问题，可以尝试使用VPN或更换Docker的镜像源。

要测试 JAR，请放到 `user/submission_jar/submission.jar`，然后运行 `run_jar.sh`。

要测试 ZIP，请放到 `user/submission_zip/submission.zip`，然后运行 `run_zip.sh`。

如果想重新评测，删除提交目录下的 `result.json` 然后重新运行对应命令即可。