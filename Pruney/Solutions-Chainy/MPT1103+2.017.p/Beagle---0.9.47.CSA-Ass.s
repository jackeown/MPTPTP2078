%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:34 EST 2020

% Result     : CounterSatisfiable 2.83s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:40:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.83/1.50  
% 2.83/1.50  % SZS status CounterSatisfiable for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.83/1.50  
% 2.83/1.50  Inference rules
% 2.83/1.50  ----------------------
% 2.83/1.50  #Ref     : 0
% 2.83/1.50  #Sup     : 297
% 2.83/1.50  #Fact    : 0
% 2.83/1.50  #Define  : 0
% 2.83/1.50  #Split   : 1
% 2.83/1.50  #Chain   : 0
% 2.83/1.50  #Close   : 0
% 2.83/1.50  
% 2.83/1.50  Ordering : KBO
% 2.83/1.50  
% 2.83/1.50  Simplification rules
% 2.83/1.50  ----------------------
% 2.83/1.50  #Subsume      : 2
% 2.83/1.50  #Demod        : 132
% 2.83/1.50  #Tautology    : 250
% 2.83/1.50  #SimpNegUnit  : 2
% 2.83/1.50  #BackRed      : 7
% 2.83/1.50  
% 2.83/1.50  #Partial instantiations: 0
% 2.83/1.50  #Strategies tried      : 1
% 2.83/1.50  
% 2.83/1.50  Timing (in seconds)
% 2.83/1.50  ----------------------
% 2.83/1.50  Preprocessing        : 0.29
% 2.83/1.50  Parsing              : 0.15
% 2.83/1.50  CNF conversion       : 0.02
% 2.83/1.50  Main loop            : 0.42
% 2.83/1.50  Inferencing          : 0.17
% 2.83/1.50  Reduction            : 0.14
% 2.83/1.50  Demodulation         : 0.10
% 2.83/1.51  BG Simplification    : 0.02
% 2.83/1.51  Subsumption          : 0.05
% 2.83/1.51  Abstraction          : 0.02
% 2.83/1.51  MUC search           : 0.00
% 2.83/1.51  Cooper               : 0.00
% 2.83/1.51  Total                : 0.71
% 2.83/1.51  Index Insertion      : 0.00
% 2.83/1.51  Index Deletion       : 0.00
% 2.83/1.51  Index Matching       : 0.00
% 2.83/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
