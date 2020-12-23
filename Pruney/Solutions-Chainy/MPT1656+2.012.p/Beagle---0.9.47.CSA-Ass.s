%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:56 EST 2020

% Result     : CounterSatisfiable 3.24s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:41:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.24/1.48  
% 3.24/1.48  % SZS status CounterSatisfiable for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.24/1.48  
% 3.24/1.48  Inference rules
% 3.24/1.48  ----------------------
% 3.24/1.48  #Ref     : 0
% 3.24/1.48  #Sup     : 77
% 3.24/1.48  #Fact    : 0
% 3.24/1.48  #Define  : 0
% 3.24/1.48  #Split   : 4
% 3.24/1.48  #Chain   : 0
% 3.24/1.48  #Close   : 0
% 3.24/1.48  
% 3.24/1.48  Ordering : KBO
% 3.24/1.48  
% 3.24/1.48  Simplification rules
% 3.24/1.48  ----------------------
% 3.24/1.48  #Subsume      : 55
% 3.24/1.48  #Demod        : 75
% 3.24/1.48  #Tautology    : 7
% 3.24/1.48  #SimpNegUnit  : 6
% 3.24/1.48  #BackRed      : 0
% 3.24/1.48  
% 3.24/1.48  #Partial instantiations: 0
% 3.24/1.48  #Strategies tried      : 1
% 3.24/1.48  
% 3.24/1.48  Timing (in seconds)
% 3.24/1.48  ----------------------
% 3.24/1.48  Preprocessing        : 0.31
% 3.24/1.48  Parsing              : 0.17
% 3.24/1.48  CNF conversion       : 0.03
% 3.24/1.48  Main loop            : 0.42
% 3.24/1.48  Inferencing          : 0.18
% 3.24/1.48  Reduction            : 0.11
% 3.32/1.48  Demodulation         : 0.07
% 3.32/1.48  BG Simplification    : 0.02
% 3.32/1.48  Subsumption          : 0.09
% 3.32/1.48  Abstraction          : 0.02
% 3.32/1.48  MUC search           : 0.00
% 3.32/1.48  Cooper               : 0.00
% 3.32/1.48  Total                : 0.74
% 3.32/1.48  Index Insertion      : 0.00
% 3.32/1.48  Index Deletion       : 0.00
% 3.32/1.48  Index Matching       : 0.00
% 3.32/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
