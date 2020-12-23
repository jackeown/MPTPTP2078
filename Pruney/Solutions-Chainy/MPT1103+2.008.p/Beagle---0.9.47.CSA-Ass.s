%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:33 EST 2020

% Result     : CounterSatisfiable 5.03s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:17:15 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.03/1.95  
% 5.03/1.95  % SZS status CounterSatisfiable for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.03/1.95  
% 5.03/1.95  Inference rules
% 5.03/1.95  ----------------------
% 5.03/1.95  #Ref     : 0
% 5.03/1.95  #Sup     : 743
% 5.03/1.95  #Fact    : 0
% 5.03/1.95  #Define  : 0
% 5.03/1.95  #Split   : 1
% 5.03/1.95  #Chain   : 0
% 5.03/1.95  #Close   : 0
% 5.03/1.95  
% 5.03/1.95  Ordering : KBO
% 5.03/1.95  
% 5.03/1.95  Simplification rules
% 5.03/1.95  ----------------------
% 5.03/1.95  #Subsume      : 34
% 5.03/1.95  #Demod        : 70
% 5.03/1.95  #Tautology    : 632
% 5.03/1.95  #SimpNegUnit  : 12
% 5.03/1.95  #BackRed      : 2
% 5.03/1.95  
% 5.03/1.95  #Partial instantiations: 0
% 5.03/1.95  #Strategies tried      : 1
% 5.03/1.95  
% 5.03/1.95  Timing (in seconds)
% 5.03/1.95  ----------------------
% 5.03/1.95  Preprocessing        : 0.33
% 5.03/1.96  Parsing              : 0.17
% 5.03/1.96  CNF conversion       : 0.02
% 5.03/1.96  Main loop            : 0.87
% 5.03/1.96  Inferencing          : 0.34
% 5.03/1.96  Reduction            : 0.25
% 5.03/1.96  Demodulation         : 0.18
% 5.03/1.96  BG Simplification    : 0.06
% 5.03/1.96  Subsumption          : 0.17
% 5.03/1.96  Abstraction          : 0.06
% 5.03/1.96  MUC search           : 0.00
% 5.03/1.96  Cooper               : 0.00
% 5.03/1.96  Total                : 1.22
% 5.03/1.96  Index Insertion      : 0.00
% 5.03/1.96  Index Deletion       : 0.00
% 5.03/1.96  Index Matching       : 0.00
% 5.03/1.96  BG Taut test         : 0.00
%------------------------------------------------------------------------------
