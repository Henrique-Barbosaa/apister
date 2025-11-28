package app.core;

import java.io.Externalizable;
import java.io.IOException;
import java.io.ObjectInput;
import java.io.ObjectOutput;
import java.time.Instant;

import javafx.beans.property.SimpleStringProperty;
import javafx.beans.property.StringProperty;

//@ nullable_by_default
public class Response implements Externalizable {
    private /*@ spec_public @*/ StringProperty message;
    private /*@ spec_public @*/ StringProperty header;
    private /*@ spec_public @*/ String url;
    private /*@ spec_public @*/ StatusCode statusCode;
    private /*@ spec_public @*/ Instant requestedAt;
    private /*@ spec_public @*/ Instant receivedAt;
    
    public Response() {
        this.message = new SimpleStringProperty("");
        this.header = new SimpleStringProperty("");
    };

    //@ skipesc
    public Response(
        Instant requestedAt,
        String url, 
        String message,
        String header,
        StatusCode statusCode
    ) {
        this.requestedAt = requestedAt;
        this.url = url;
        this.message = new SimpleStringProperty(message);
        this.header = new SimpleStringProperty(header);
        this.statusCode = statusCode;
        this.receivedAt = Instant.now();
    };

    //#region Externalizable
    //@ skipesc
    @Override
    public void writeExternal(ObjectOutput out) throws IOException {
        out.writeUTF(this.message.get());
        out.writeUTF(this.header.get());
        out.writeUTF(this.url);
        out.writeUTF(this.statusCode.name());
        out.writeObject(this.requestedAt);
        out.writeObject(this.receivedAt);
    };

    //@ skipesc
    @Override
    public void readExternal(ObjectInput in) throws IOException, ClassNotFoundException {
        this.message.set(in.readUTF());
        this.header.set(in.readUTF());
        this.url = in.readUTF();
        this.statusCode = StatusCode.valueOf(in.readUTF());
        this.requestedAt = (Instant) in.readObject();
        this.receivedAt = (Instant) in.readObject();
    };
    //#endregion
    //#region Getters and setters

    /*@ public normal_behavior
      @   ensures \result == this.message;
      @   pure
      @*/
    public StringProperty messageProperty() {
        return this.message;
    };

    /*@ public normal_behavior
      @   ensures \result == this.header;
      @   pure
      @*/
    public StringProperty headerProperty() {
        return this.header;
    };

    /*@ public normal_behavior
      @   ensures this.url == url;
      @   pure
      @*/
    public String getUrl() {
        return this.url;
    };

    /*@ public normal_behavior
      @   ensures this.url == url;
      @   requires url != null;
      @*/
    public void setUrl(String url) {
        this.url = url;
    };

    /*@ public normal_behavior
      @   ensures \result == this.statusCode;
      @   pure
      @*/
    public StatusCode getStatusCode() {
        return this.statusCode;
    };

    /*@ public normal_behavior
      @   ensures this.statusCode == statusCode;
      @   requires statusCode != null;
      @*/
    public void setStatusCode(StatusCode statusCode) {
        this.statusCode = statusCode;
    };

    /*@ public normal_behavior
      @   ensures \result == this.requestedAt;
      @   pure
      @*/
    public Instant getRequestedAt() {
        return this.requestedAt;
    };
    
    /*@ public normal_behavior
      @   ensures this.requestedAt == requestedAt;
      @   requires requestedAt != null;
      @*/
    public void setRequestedAt(Instant requestedAt) {
        this.requestedAt = requestedAt;
    };

    /*@ public normal_behavior
      @   ensures \result == this.receivedAt;
      @   pure
      @*/
    public Instant getReceivedAt() {
        return this.receivedAt;
    };

    /*@ public normal_behavior
      @   ensures this.receivedAt == receivedAt;
      @   requires receivedAt != null;
      @*/
    public void setReceivedAt(Instant receivedAt) {
        this.receivedAt = receivedAt;
    };
    //#endregion
};
