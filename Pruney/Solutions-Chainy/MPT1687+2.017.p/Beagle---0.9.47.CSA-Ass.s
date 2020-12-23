%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:05 EST 2020

% Result     : CounterSatisfiable 3.63s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:21:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.63/1.86  
% 3.63/1.86  % SZS status CounterSatisfiable for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.63/1.86  
% 3.63/1.86  Inference rules
% 3.63/1.86  ----------------------
% 3.63/1.86  #Ref     : 0
% 3.63/1.86  #Sup     : 46
% 3.63/1.86  #Fact    : 0
% 3.63/1.86  #Define  : 0
% 3.63/1.86  #Split   : 2
% 3.63/1.86  #Chain   : 0
% 3.63/1.86  #Close   : 0
% 3.63/1.86  
% 3.63/1.86  Ordering : KBO
% 3.63/1.86  
% 3.63/1.86  Simplification rules
% 3.63/1.86  ----------------------
% 3.63/1.86  #Subsume      : 16
% 3.63/1.86  #Demod        : 28
% 3.63/1.86  #Tautology    : 14
% 3.63/1.86  #SimpNegUnit  : 1
% 3.63/1.86  #BackRed      : 0
% 3.63/1.86  
% 3.63/1.86  #Partial instantiations: 0
% 3.63/1.86  #Strategies tried      : 1
% 3.63/1.86  
% 3.63/1.86  Timing (in seconds)
% 3.63/1.86  ----------------------
% 3.63/1.87  Preprocessing        : 0.55
% 3.63/1.87  Parsing              : 0.29
% 3.63/1.87  CNF conversion       : 0.04
% 3.63/1.87  Main loop            : 0.52
% 3.63/1.87  Inferencing          : 0.19
% 3.63/1.87  Reduction            : 0.14
% 3.63/1.87  Demodulation         : 0.10
% 3.63/1.87  BG Simplification    : 0.03
% 3.63/1.87  Subsumption          : 0.13
% 3.63/1.87  Abstraction          : 0.03
% 3.63/1.87  MUC search           : 0.00
% 3.63/1.87  Cooper               : 0.00
% 3.63/1.87  Total                : 1.09
% 3.63/1.87  Index Insertion      : 0.00
% 3.63/1.87  Index Deletion       : 0.00
% 3.63/1.87  Index Matching       : 0.00
% 3.63/1.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
