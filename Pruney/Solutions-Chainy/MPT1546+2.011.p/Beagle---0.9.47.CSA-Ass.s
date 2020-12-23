%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:01 EST 2020

% Result     : CounterSatisfiable 3.90s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:24:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.90/2.02  
% 3.90/2.02  % SZS status CounterSatisfiable for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.90/2.02  
% 3.90/2.02  Inference rules
% 3.90/2.02  ----------------------
% 3.90/2.02  #Ref     : 0
% 3.90/2.03  #Sup     : 80
% 3.90/2.03  #Fact    : 0
% 3.90/2.03  #Define  : 0
% 3.90/2.03  #Split   : 4
% 3.90/2.03  #Chain   : 0
% 3.90/2.03  #Close   : 0
% 3.90/2.03  
% 3.90/2.03  Ordering : KBO
% 3.90/2.03  
% 3.90/2.03  Simplification rules
% 3.90/2.03  ----------------------
% 3.90/2.03  #Subsume      : 28
% 3.90/2.03  #Demod        : 73
% 3.90/2.03  #Tautology    : 22
% 3.90/2.03  #SimpNegUnit  : 6
% 3.90/2.03  #BackRed      : 0
% 3.90/2.03  
% 3.90/2.03  #Partial instantiations: 0
% 3.90/2.03  #Strategies tried      : 1
% 3.90/2.03  
% 3.90/2.03  Timing (in seconds)
% 3.90/2.03  ----------------------
% 3.90/2.03  Preprocessing        : 0.52
% 3.90/2.03  Parsing              : 0.28
% 3.90/2.03  CNF conversion       : 0.04
% 3.90/2.03  Main loop            : 0.64
% 3.90/2.03  Inferencing          : 0.25
% 3.90/2.03  Reduction            : 0.14
% 3.90/2.03  Demodulation         : 0.10
% 3.90/2.03  BG Simplification    : 0.03
% 3.90/2.03  Subsumption          : 0.17
% 3.90/2.03  Abstraction          : 0.02
% 3.90/2.03  MUC search           : 0.00
% 3.90/2.03  Cooper               : 0.00
% 3.90/2.03  Total                : 1.18
% 3.90/2.03  Index Insertion      : 0.00
% 3.90/2.03  Index Deletion       : 0.00
% 3.90/2.03  Index Matching       : 0.00
% 3.90/2.03  BG Taut test         : 0.00
%------------------------------------------------------------------------------
