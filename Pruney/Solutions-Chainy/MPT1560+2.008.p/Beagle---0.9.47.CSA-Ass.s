%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:05 EST 2020

% Result     : CounterSatisfiable 1.91s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n023.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 15:10:21 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.91/1.21  
% 1.91/1.21  % SZS status CounterSatisfiable for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.21  
% 1.91/1.21  Inference rules
% 1.91/1.21  ----------------------
% 1.91/1.21  #Ref     : 0
% 1.91/1.21  #Sup     : 22
% 1.91/1.21  #Fact    : 0
% 1.91/1.21  #Define  : 0
% 1.91/1.21  #Split   : 2
% 1.91/1.21  #Chain   : 0
% 1.91/1.21  #Close   : 0
% 1.91/1.21  
% 1.91/1.21  Ordering : KBO
% 1.91/1.21  
% 1.91/1.21  Simplification rules
% 1.91/1.21  ----------------------
% 1.91/1.21  #Subsume      : 0
% 1.91/1.21  #Demod        : 4
% 1.91/1.21  #Tautology    : 18
% 1.91/1.21  #SimpNegUnit  : 2
% 1.91/1.21  #BackRed      : 1
% 1.91/1.21  
% 1.91/1.21  #Partial instantiations: 0
% 1.91/1.21  #Strategies tried      : 1
% 1.91/1.21  
% 1.91/1.21  Timing (in seconds)
% 1.91/1.21  ----------------------
% 1.91/1.21  Preprocessing        : 0.30
% 1.91/1.21  Parsing              : 0.16
% 1.91/1.21  CNF conversion       : 0.02
% 1.91/1.21  Main loop            : 0.13
% 1.91/1.21  Inferencing          : 0.05
% 1.91/1.21  Reduction            : 0.04
% 1.91/1.21  Demodulation         : 0.02
% 1.91/1.21  BG Simplification    : 0.01
% 1.91/1.21  Subsumption          : 0.01
% 1.91/1.21  Abstraction          : 0.01
% 1.91/1.21  MUC search           : 0.00
% 1.91/1.21  Cooper               : 0.00
% 1.91/1.21  Total                : 0.45
% 1.91/1.21  Index Insertion      : 0.00
% 1.91/1.21  Index Deletion       : 0.00
% 1.91/1.21  Index Matching       : 0.00
% 1.91/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
