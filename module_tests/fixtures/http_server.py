import http.server
import json
import sys
import time


class Handler(http.server.BaseHTTPRequestHandler):
    def respond(self):
        if self.path == "/slow":
            time.sleep(0.2)
        length = int(self.headers.get("Content-Length", "0"))
        body = self.rfile.read(length).decode("utf-8")
        headers = {k.lower(): v for k, v in self.headers.items()}
        response = json.dumps(
            {"method": self.command, "body": body, "headers": headers}
        ).encode("utf-8")
        self.send_response(404 if self.path == "/missing" else 200)
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(response)))
        self.send_header("X-Test", "fixture")
        self.end_headers()
        try:
            self.wfile.write(response)
        except (BrokenPipeError, ConnectionResetError):
            pass

    do_GET = respond
    do_POST = respond
    do_PUT = respond

    def log_message(self, *args):
        pass


try:
    server = http.server.ThreadingHTTPServer(("127.0.0.1", 0), Handler)
except OSError as error:
    print("Could not start the local HTTP fixture: " + str(error), file=sys.stderr)
    raise SystemExit(1)
print(server.server_address[1], flush=True)
server.serve_forever()
