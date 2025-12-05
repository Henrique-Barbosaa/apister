package app.core;

import java.io.Externalizable;
import java.io.IOException;
import java.io.ObjectInput;
import java.io.ObjectOutput;

import javafx.beans.property.SimpleStringProperty;
import javafx.beans.property.StringProperty;

//@ nullable_by_default
public class HeaderEntry implements Externalizable {
    private /*@ spec_public non_null @*/ final StringProperty key;
    private /*@ spec_public non_null @*/ final StringProperty value;

    //@ public constraint key == \old(key);
    //@ public constraint value == \old(value);

    /*@ public normal_behavior
      @   assignable \everything;
      @   ensures this.key != null;
      @   ensures this.value != null;
      @*/
    //@ skipesc
    public HeaderEntry() {
        this.key = new SimpleStringProperty("");
        this.value = new SimpleStringProperty("");
    };

    /*@ public normal_behavior
      @   assignable \everything;
      @   requires key != null;
      @   requires value != null;
      @   ensures this.key != null;
      @   ensures this.value != null;
      @*/
    //@ skipesc
    public HeaderEntry(String key, String value) {
        this.key = new SimpleStringProperty(key);
        this.value = new SimpleStringProperty(value);
    };
    
    //#region Externalizable
    /*@ also public exceptional_behavior
      @   assignable \nothing;
      @   signals_only IOException;
      @*/
    //@ skipesc
    @Override
    public void writeExternal(ObjectOutput out) throws IOException {
        out.writeUTF(this.getKey());
        out.writeUTF(this.getValue());
    };

    /*@ also public normal_behavior
      @   assignable key, value;
      @
      @ also
      @
      @ public exceptional_behavior
      @   signals_only IOException, ClassNotFoundException;
      @*/
    //@ skipesc
    @Override
    public void readExternal(ObjectInput in) throws IOException, ClassNotFoundException {
        this.setKey(in.readUTF());
        this.setValue(in.readUTF());
    };
    //#endregion
    //#region Getters and setters

    /*@ public normal_behavior
      @   pure
      @*/
    //@ skipesc
    public String getKey() {
        return this.key.get();
    };

    /*@ public normal_behavior
      @   assignable \everything;
      @*/
    //@ skipesc
    public void setKey(String key) {
        this.key.set(key);
    };

    /*@ public normal_behavior
      @   ensures \result == this.key;
      @   ensures \result != null;
      @   pure
      @*/
    public StringProperty keyProperty() {
        return this.key;
    };

    /*@ public normal_behavior
      @   pure
      @*/
    //@ skipesc
    public String getValue() {
        return this.value.get();
    };

    /*@ public normal_behavior
      @   assignable \everything;
      @*/
    //@ skipesc
    public void setValue(String value) {
        this.value.set(value);
    };

    /*@ public normal_behavior
      @   ensures \result == this.value;
      @   ensures \result != null;
      @   pure
      @*/
    public StringProperty valueProperty() {
        return this.value;
    };
    //#endregion
};
