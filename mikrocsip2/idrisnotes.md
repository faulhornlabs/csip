The Idris implementation was a neat experience. The two different type systems, Agda vs Idris, has different tradeoffs. But for the development, there are some crucial points, that were missing from Idris2, that made it very hard to implement mikrocsip2 in it:

 - There are no eta-rules for Pi (dependent function) and Sigma (dependent sum)
 - The implicit paramater resolution is different, and a lot of times, Idris were unable to find the right parameter
   - Trying to use `auto` did help with the error messages, but made the code to robust (as you can see in the last state of the files)

When mikrocsip2 solidifies in Agda, it would make a nice exercise to port it to Idris2, but until then, this implementation remains like this.
