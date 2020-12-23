%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:11 EST 2020

% Result     : CounterSatisfiable 3.95s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:28:50 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.95/1.66  
% 3.95/1.66  % SZS status CounterSatisfiable for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.95/1.66  
% 3.95/1.66  Inference rules
% 3.95/1.66  ----------------------
% 3.95/1.66  #Ref     : 0
% 3.95/1.66  #Sup     : 188
% 3.95/1.66  #Fact    : 0
% 3.95/1.66  #Define  : 0
% 3.95/1.66  #Split   : 1
% 3.95/1.66  #Chain   : 0
% 3.95/1.66  #Close   : 0
% 3.95/1.66  
% 3.95/1.66  Ordering : KBO
% 3.95/1.66  
% 3.95/1.66  Simplification rules
% 3.95/1.66  ----------------------
% 3.95/1.66  #Subsume      : 38
% 3.95/1.66  #Demod        : 0
% 3.95/1.66  #Tautology    : 73
% 3.95/1.66  #SimpNegUnit  : 0
% 3.95/1.66  #BackRed      : 0
% 3.95/1.66  
% 3.95/1.66  #Partial instantiations: 0
% 3.95/1.66  #Strategies tried      : 1
% 3.95/1.66  
% 3.95/1.66  Timing (in seconds)
% 3.95/1.66  ----------------------
% 3.95/1.67  Preprocessing        : 0.28
% 3.95/1.67  Parsing              : 0.15
% 3.95/1.67  CNF conversion       : 0.02
% 3.95/1.67  Main loop            : 0.65
% 3.95/1.67  Inferencing          : 0.26
% 3.95/1.67  Reduction            : 0.12
% 3.95/1.67  Demodulation         : 0.07
% 3.95/1.67  BG Simplification    : 0.03
% 3.95/1.67  Subsumption          : 0.21
% 3.95/1.67  Abstraction          : 0.03
% 3.95/1.67  MUC search           : 0.00
% 3.95/1.67  Cooper               : 0.00
% 3.95/1.67  Total                : 0.94
% 3.95/1.67  Index Insertion      : 0.00
% 3.95/1.67  Index Deletion       : 0.00
% 3.95/1.67  Index Matching       : 0.00
% 3.95/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
