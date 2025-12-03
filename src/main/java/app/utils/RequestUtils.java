package app.utils;

import java.net.http.HttpHeaders;
import java.util.List;
import java.util.Map.Entry;

import app.core.StatusCode;

//@ nullable_by_default
public class RequestUtils {
    //#region Header
    //@ skipesc
    public static String createHeader(
        StatusCode statusCode
    ) {
        StringBuilder header = new StringBuilder();
        String status = statusCode.getValue() + 
            " " + 
            statusCode.name().replace('_', ' ') + 
            "\n";
        
        header.append(status);
        header.append("=".repeat(status.length() - 1));

        return header.toString();
    };
    //@ skipesc
    public static String convertHttpHeader(
        HttpHeaders headers,
        StatusCode statusCode
    ) {
        StringBuilder header = new StringBuilder();

        String status = statusCode.getValue() + 
            " " + 
            statusCode.name().replace('_', ' ') + 
            "\n";
        
        header.append(status);
        header.append("=".repeat(status.length() - 1) + "\n");

        for(Entry<String, List<String>> entry : headers.map().entrySet()) {
            if(entry.getKey().equals(":status")) continue;

            header.append(entry.getKey() + ": ");

            for(int i = 0; i < entry.getValue().size(); i++) {
                header.append(entry.getValue().get(i));
                if(i < entry.getValue().size() - 1) header.append(", ");
            };

            header.append("\n");
        };

        return header.toString().trim();
    };
    //#endregion
};
