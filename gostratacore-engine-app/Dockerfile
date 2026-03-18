FROM golang:1.25-alpine AS builder

WORKDIR /build

RUN apk add --no-cache git

RUN git clone -b main https://github.com/GoStrataCore/gostratumengine.git

WORKDIR /build/gostratumengine

RUN go build -o gostratumengine ./cmd/gostratumengine

FROM alpine:3.19

WORKDIR /app

# Binary
COPY --from=builder /build/gostratumengine/gostratumengine .

# ✅ Runtime files (CRITICAL)
# ✅ Use REAL config
COPY config.json /app/config.json
COPY --from=builder /build/gostratumengine/templates /app/templates
COPY --from=builder /build/gostratumengine/simple-web-ui /app/simple-web-ui

# Directories
RUN mkdir -p /pool/coins
RUN mkdir -p /pool/logs

# Start script
COPY start.sh /app/start.sh
RUN chmod +x /app/start.sh

CMD ["/app/start.sh"]
