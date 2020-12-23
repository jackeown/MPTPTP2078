%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:51 EST 2020

% Result     : CounterSatisfiable 5.06s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:08:10 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.06/1.95  
% 5.06/1.95  % SZS status CounterSatisfiable for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.06/1.95  
% 5.06/1.95  Inference rules
% 5.06/1.95  ----------------------
% 5.06/1.95  #Ref     : 5
% 5.06/1.95  #Sup     : 673
% 5.06/1.95  #Fact    : 0
% 5.06/1.95  #Define  : 0
% 5.06/1.95  #Split   : 2
% 5.06/1.95  #Chain   : 0
% 5.06/1.95  #Close   : 0
% 5.06/1.95  
% 5.06/1.95  Ordering : KBO
% 5.06/1.95  
% 5.06/1.95  Simplification rules
% 5.06/1.95  ----------------------
% 5.06/1.95  #Subsume      : 214
% 5.06/1.95  #Demod        : 271
% 5.06/1.95  #Tautology    : 414
% 5.06/1.95  #SimpNegUnit  : 0
% 5.06/1.95  #BackRed      : 1
% 5.06/1.95  
% 5.06/1.95  #Partial instantiations: 0
% 5.06/1.95  #Strategies tried      : 1
% 5.06/1.95  
% 5.06/1.95  Timing (in seconds)
% 5.06/1.95  ----------------------
% 5.06/1.96  Preprocessing        : 0.29
% 5.06/1.96  Parsing              : 0.15
% 5.06/1.96  CNF conversion       : 0.02
% 5.06/1.96  Main loop            : 0.93
% 5.06/1.96  Inferencing          : 0.33
% 5.06/1.96  Reduction            : 0.35
% 5.06/1.96  Demodulation         : 0.29
% 5.06/1.96  BG Simplification    : 0.05
% 5.06/1.96  Subsumption          : 0.17
% 5.06/1.96  Abstraction          : 0.08
% 5.06/1.96  MUC search           : 0.00
% 5.06/1.96  Cooper               : 0.00
% 5.06/1.96  Total                : 1.23
% 5.06/1.96  Index Insertion      : 0.00
% 5.06/1.96  Index Deletion       : 0.00
% 5.06/1.96  Index Matching       : 0.00
% 5.06/1.96  BG Taut test         : 0.00
%------------------------------------------------------------------------------
