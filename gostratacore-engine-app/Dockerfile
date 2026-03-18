FROM golang:1.25-alpine AS builder

WORKDIR /build

RUN apk add --no-cache git

RUN git clone https://github.com/GoStrataCore/gostratumengine.git

WORKDIR /build/gostratumengine

RUN go build -o gostratumengine ./cmd/gostratumengine

FROM alpine:3.19

WORKDIR /app

COPY --from=builder /build/gostratumengine/gostratumengine .

RUN mkdir -p /pool/coins
RUN mkdir -p /pool/logs

COPY start.sh /app/start.sh

RUN chmod +x /app/start.sh

CMD ["/app/start.sh"]
