
This scripts are recipes to help in the preparation of the demo of the security scanner.

Finding roots
=============

The doGet, doPost, doDelete, doOptions, doPut, doTrace, and service methods of
classes that extend HttpServlet are potential roots for security scanner.
The script find_servlet.sh helps you find such classes
It seems to work well for Alfresco, DSpace, jforum3, Red5, Sakai, SocialSDK.
But not Encuestame, Ginco, Onyx, Openolat (no results).
Not sure about Libresonic (only one result)


Finding sources
===============

Calls to methods of the class javax.servlet.http.HttpServletRequest
are possible sources
The script find_request.sh helps you find such calls


Finding sinks
=============

Calls to methods of the class javax.servlet.http.HttpServletResponse are possible sinks
The script find_response.sh helps you find such calls

