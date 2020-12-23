%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:35 EST 2020

% Result     : CounterSatisfiable 3.77s
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
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:57:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.77/1.96  
% 3.77/1.96  % SZS status CounterSatisfiable for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.77/1.96  
% 3.77/1.96  Inference rules
% 3.77/1.96  ----------------------
% 3.77/1.96  #Ref     : 0
% 3.77/1.96  #Sup     : 260
% 3.77/1.96  #Fact    : 0
% 3.77/1.96  #Define  : 0
% 3.77/1.96  #Split   : 4
% 3.77/1.96  #Chain   : 0
% 3.77/1.96  #Close   : 0
% 3.77/1.96  
% 3.77/1.96  Ordering : KBO
% 3.77/1.96  
% 3.77/1.96  Simplification rules
% 3.77/1.96  ----------------------
% 3.77/1.96  #Subsume      : 121
% 3.77/1.96  #Demod        : 60
% 3.77/1.96  #Tautology    : 112
% 3.77/1.96  #SimpNegUnit  : 32
% 3.77/1.96  #BackRed      : 28
% 3.77/1.96  
% 3.77/1.96  #Partial instantiations: 0
% 3.77/1.96  #Strategies tried      : 1
% 3.77/1.96  
% 3.77/1.96  Timing (in seconds)
% 3.77/1.96  ----------------------
% 3.77/1.96  Preprocessing        : 0.48
% 3.77/1.96  Parsing              : 0.25
% 3.77/1.96  CNF conversion       : 0.03
% 3.77/1.97  Main loop            : 0.67
% 3.77/1.97  Inferencing          : 0.25
% 3.77/1.97  Reduction            : 0.17
% 3.77/1.97  Demodulation         : 0.13
% 3.77/1.97  BG Simplification    : 0.03
% 3.77/1.97  Subsumption          : 0.18
% 3.77/1.97  Abstraction          : 0.03
% 3.77/1.97  MUC search           : 0.00
% 3.77/1.97  Cooper               : 0.00
% 3.77/1.97  Total                : 1.17
% 3.77/1.97  Index Insertion      : 0.00
% 3.77/1.97  Index Deletion       : 0.00
% 3.77/1.97  Index Matching       : 0.00
% 3.77/1.97  BG Taut test         : 0.00
%------------------------------------------------------------------------------
