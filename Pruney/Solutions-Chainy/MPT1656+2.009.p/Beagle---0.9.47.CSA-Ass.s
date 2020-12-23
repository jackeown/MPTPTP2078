%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:56 EST 2020

% Result     : CounterSatisfiable 5.08s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:44:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.08/1.96  
% 5.08/1.96  % SZS status CounterSatisfiable for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.08/1.96  
% 5.08/1.96  Inference rules
% 5.08/1.96  ----------------------
% 5.08/1.96  #Ref     : 0
% 5.08/1.96  #Sup     : 231
% 5.08/1.96  #Fact    : 0
% 5.08/1.96  #Define  : 0
% 5.08/1.96  #Split   : 7
% 5.08/1.96  #Chain   : 0
% 5.08/1.96  #Close   : 0
% 5.08/1.96  
% 5.08/1.96  Ordering : KBO
% 5.08/1.96  
% 5.08/1.96  Simplification rules
% 5.08/1.96  ----------------------
% 5.08/1.96  #Subsume      : 144
% 5.08/1.96  #Demod        : 123
% 5.08/1.96  #Tautology    : 6
% 5.08/1.96  #SimpNegUnit  : 0
% 5.08/1.96  #BackRed      : 0
% 5.08/1.96  
% 5.08/1.96  #Partial instantiations: 0
% 5.08/1.96  #Strategies tried      : 1
% 5.08/1.96  
% 5.08/1.96  Timing (in seconds)
% 5.08/1.96  ----------------------
% 5.08/1.97  Preprocessing        : 0.29
% 5.08/1.97  Parsing              : 0.16
% 5.08/1.97  CNF conversion       : 0.02
% 5.08/1.97  Main loop            : 0.93
% 5.08/1.97  Inferencing          : 0.31
% 5.08/1.97  Reduction            : 0.19
% 5.08/1.97  Demodulation         : 0.12
% 5.08/1.97  BG Simplification    : 0.02
% 5.08/1.97  Subsumption          : 0.36
% 5.08/1.97  Abstraction          : 0.03
% 5.08/1.97  MUC search           : 0.00
% 5.08/1.97  Cooper               : 0.00
% 5.08/1.97  Total                : 1.23
% 5.08/1.97  Index Insertion      : 0.00
% 5.08/1.97  Index Deletion       : 0.00
% 5.08/1.97  Index Matching       : 0.00
% 5.08/1.97  BG Taut test         : 0.00
%------------------------------------------------------------------------------
