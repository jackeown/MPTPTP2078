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
% DateTime   : Thu Dec  3 10:19:06 EST 2020

% Result     : CounterSatisfiable 4.81s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:16:46 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.81/1.87  
% 4.81/1.87  % SZS status CounterSatisfiable for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.81/1.87  
% 4.81/1.87  Inference rules
% 4.81/1.87  ----------------------
% 4.81/1.87  #Ref     : 0
% 4.81/1.87  #Sup     : 776
% 4.81/1.87  #Fact    : 0
% 4.81/1.87  #Define  : 0
% 4.81/1.88  #Split   : 5
% 4.81/1.88  #Chain   : 0
% 4.81/1.88  #Close   : 0
% 4.81/1.88  
% 4.81/1.88  Ordering : KBO
% 4.81/1.88  
% 4.81/1.88  Simplification rules
% 4.81/1.88  ----------------------
% 4.81/1.88  #Subsume      : 45
% 4.81/1.88  #Demod        : 2421
% 4.81/1.88  #Tautology    : 697
% 4.81/1.88  #SimpNegUnit  : 11
% 4.81/1.88  #BackRed      : 21
% 4.81/1.88  
% 4.81/1.88  #Partial instantiations: 0
% 4.81/1.88  #Strategies tried      : 1
% 4.81/1.88  
% 4.81/1.88  Timing (in seconds)
% 4.81/1.88  ----------------------
% 4.81/1.88  Preprocessing        : 0.31
% 4.81/1.88  Parsing              : 0.17
% 4.81/1.88  CNF conversion       : 0.02
% 4.81/1.88  Main loop            : 0.83
% 4.81/1.88  Inferencing          : 0.24
% 4.81/1.88  Reduction            : 0.42
% 4.81/1.88  Demodulation         : 0.36
% 4.81/1.88  BG Simplification    : 0.03
% 4.81/1.88  Subsumption          : 0.09
% 4.81/1.88  Abstraction          : 0.06
% 4.81/1.88  MUC search           : 0.00
% 4.81/1.88  Cooper               : 0.00
% 4.81/1.88  Total                : 1.14
% 4.81/1.88  Index Insertion      : 0.00
% 4.81/1.88  Index Deletion       : 0.00
% 4.81/1.88  Index Matching       : 0.00
% 4.81/1.88  BG Taut test         : 0.00
%------------------------------------------------------------------------------
