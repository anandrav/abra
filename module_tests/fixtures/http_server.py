import http.server
import json
import sys
import time
from urllib.parse import parse_qs, urlsplit


class Handler(http.server.BaseHTTPRequestHandler):
    def respond(self):
        url = urlsplit(self.path)
        if url.path in ("/stream", "/stall", "/truncated"):
            if url.path == "/stream":
                chunks = [b"\x00\xff", b"\xc3", b"\xa9\x80\x2a"]
            else:
                chunks = [b"x"]
            self.send_response(200)
            self.send_header("Content-Type", "application/octet-stream")
            length = sum(len(chunk) for chunk in chunks)
            if url.path == "/truncated":
                length += 1
            self.send_header("Content-Length", str(length))
            self.end_headers()
            try:
                if url.path == "/stall":
                    time.sleep(0.5)
                for i, chunk in enumerate(chunks):
                    if i:
                        time.sleep(0.35)
                    self.wfile.write(chunk)
                    self.wfile.flush()
            except (BrokenPipeError, ConnectionResetError):
                pass
            self.close_connection = True
            return
        if url.path == "/slow":
            time.sleep(0.2)
        length = int(self.headers.get("Content-Length", "0"))
        body = self.rfile.read(length).decode("utf-8")
        headers = {k.lower(): v for k, v in self.headers.items()}
        response = json.dumps(
            {
                "method": self.command,
                "body": body,
                "headers": headers,
                "query": parse_qs(url.query, keep_blank_values=True),
            }
        ).encode("utf-8")
        self.send_response(404 if url.path == "/missing" else 200)
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
