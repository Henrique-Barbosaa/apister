package app.core;

import java.io.Externalizable;
import java.io.IOException;
import java.io.ObjectInput;
import java.io.ObjectOutput;

import javafx.beans.property.SimpleStringProperty;
import javafx.beans.property.StringProperty;

//@ nullable_by_default
public class HeaderEntry implements Externalizable {
    private StringProperty key;
    private StringProperty value;  

    //@ skipesc
    public HeaderEntry() {
        this.key = new SimpleStringProperty("");
        this.value = new SimpleStringProperty("");
    };

    //@ skipesc
    public HeaderEntry(String key, String value) {
        this.key = new SimpleStringProperty(key);
        this.value = new SimpleStringProperty(value);
    };
    
    //#region Externalizable
    
    //@ skipesc
    @Override
    public void writeExternal(ObjectOutput out) throws IOException {
        out.writeUTF(this.getKey());
        out.writeUTF(this.getValue());
    };

    //@ skipesc
    @Override
    public void readExternal(ObjectInput in) throws IOException, ClassNotFoundException {
        this.setKey(in.readUTF());
        this.setValue(in.readUTF());
    };
    //#endregion
    //#region Getters and setters

    //@ skipesc
    public String getKey() {
        return this.key.get();
    };

    //@ skipesc
    public void setKey(String key) {
        this.key.set(key);
    };

    //@ skipesc
    public StringProperty keyProperty() {
        return this.key;
    };

    //@ skipesc
    public String getValue() {
        return this.value.get();
    };

    //@ skipesc
    public void setValue(String value) {
        this.value.set(value);
    };

    //@ skipesc
    public StringProperty valueProperty() {
        return this.value;
    };
    //#endregion
};
