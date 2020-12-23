%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:57 EST 2020

% Result     : CounterSatisfiable 2.07s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:53:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.07/1.21  
% 2.07/1.21  % SZS status CounterSatisfiable for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.21  
% 2.07/1.21  Inference rules
% 2.07/1.21  ----------------------
% 2.07/1.21  #Ref     : 0
% 2.07/1.21  #Sup     : 33
% 2.07/1.21  #Fact    : 0
% 2.07/1.21  #Define  : 0
% 2.07/1.21  #Split   : 1
% 2.07/1.21  #Chain   : 0
% 2.07/1.21  #Close   : 0
% 2.07/1.21  
% 2.07/1.21  Ordering : KBO
% 2.07/1.21  
% 2.07/1.21  Simplification rules
% 2.07/1.21  ----------------------
% 2.07/1.21  #Subsume      : 3
% 2.07/1.21  #Demod        : 48
% 2.07/1.21  #Tautology    : 23
% 2.07/1.21  #SimpNegUnit  : 7
% 2.07/1.21  #BackRed      : 0
% 2.07/1.21  
% 2.07/1.21  #Partial instantiations: 0
% 2.07/1.21  #Strategies tried      : 1
% 2.07/1.21  
% 2.07/1.21  Timing (in seconds)
% 2.07/1.21  ----------------------
% 2.07/1.21  Preprocessing        : 0.30
% 2.07/1.21  Parsing              : 0.16
% 2.07/1.21  CNF conversion       : 0.02
% 2.07/1.21  Main loop            : 0.16
% 2.07/1.21  Inferencing          : 0.07
% 2.07/1.21  Reduction            : 0.05
% 2.07/1.21  Demodulation         : 0.03
% 2.07/1.21  BG Simplification    : 0.01
% 2.07/1.21  Subsumption          : 0.02
% 2.07/1.21  Abstraction          : 0.01
% 2.07/1.21  MUC search           : 0.00
% 2.07/1.21  Cooper               : 0.00
% 2.07/1.21  Total                : 0.47
% 2.07/1.21  Index Insertion      : 0.00
% 2.07/1.21  Index Deletion       : 0.00
% 2.07/1.21  Index Matching       : 0.00
% 2.07/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
