%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:22 EST 2020

% Result     : CounterSatisfiable 3.81s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:57:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.81/1.69  
% 3.81/1.69  % SZS status CounterSatisfiable for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.81/1.69  
% 3.81/1.69  Inference rules
% 3.81/1.69  ----------------------
% 3.81/1.69  #Ref     : 0
% 3.81/1.69  #Sup     : 605
% 3.81/1.69  #Fact    : 0
% 3.81/1.69  #Define  : 0
% 3.81/1.69  #Split   : 1
% 3.81/1.69  #Chain   : 0
% 3.81/1.69  #Close   : 0
% 3.81/1.69  
% 3.81/1.69  Ordering : KBO
% 3.81/1.69  
% 3.81/1.69  Simplification rules
% 3.81/1.69  ----------------------
% 3.81/1.69  #Subsume      : 285
% 3.81/1.69  #Demod        : 349
% 3.81/1.69  #Tautology    : 248
% 3.81/1.69  #SimpNegUnit  : 30
% 3.81/1.69  #BackRed      : 15
% 3.81/1.69  
% 3.81/1.69  #Partial instantiations: 0
% 3.81/1.69  #Strategies tried      : 1
% 3.81/1.69  
% 3.81/1.69  Timing (in seconds)
% 3.81/1.69  ----------------------
% 3.81/1.69  Preprocessing        : 0.33
% 3.81/1.69  Parsing              : 0.18
% 3.81/1.69  CNF conversion       : 0.02
% 3.81/1.69  Main loop            : 0.61
% 3.81/1.69  Inferencing          : 0.22
% 3.81/1.69  Reduction            : 0.23
% 3.81/1.69  Demodulation         : 0.18
% 3.81/1.69  BG Simplification    : 0.02
% 3.81/1.69  Subsumption          : 0.10
% 3.81/1.69  Abstraction          : 0.03
% 3.81/1.70  MUC search           : 0.00
% 3.81/1.70  Cooper               : 0.00
% 3.81/1.70  Total                : 0.95
% 3.81/1.70  Index Insertion      : 0.00
% 3.81/1.70  Index Deletion       : 0.00
% 3.81/1.70  Index Matching       : 0.00
% 3.81/1.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
