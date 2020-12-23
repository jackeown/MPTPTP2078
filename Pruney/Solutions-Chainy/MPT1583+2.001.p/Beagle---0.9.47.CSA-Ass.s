%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:17 EST 2020

% Result     : CounterSatisfiable 7.86s
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
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:08:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.86/2.88  
% 7.86/2.89  % SZS status CounterSatisfiable for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.86/2.89  
% 7.86/2.89  Inference rules
% 7.86/2.89  ----------------------
% 7.86/2.89  #Ref     : 0
% 7.86/2.89  #Sup     : 1048
% 7.86/2.89  #Fact    : 0
% 7.86/2.89  #Define  : 0
% 7.86/2.89  #Split   : 13
% 7.86/2.89  #Chain   : 0
% 7.86/2.89  #Close   : 0
% 7.86/2.89  
% 7.86/2.89  Ordering : KBO
% 7.86/2.89  
% 7.86/2.89  Simplification rules
% 7.86/2.89  ----------------------
% 7.86/2.89  #Subsume      : 511
% 7.86/2.89  #Demod        : 268
% 7.86/2.89  #Tautology    : 296
% 7.86/2.89  #SimpNegUnit  : 99
% 7.86/2.89  #BackRed      : 0
% 7.86/2.89  
% 7.86/2.89  #Partial instantiations: 0
% 7.86/2.89  #Strategies tried      : 1
% 7.86/2.89  
% 7.86/2.89  Timing (in seconds)
% 7.86/2.89  ----------------------
% 7.86/2.89  Preprocessing        : 0.31
% 7.86/2.89  Parsing              : 0.16
% 7.86/2.89  CNF conversion       : 0.03
% 7.86/2.89  Main loop            : 1.84
% 7.86/2.89  Inferencing          : 0.56
% 7.86/2.89  Reduction            : 0.42
% 7.86/2.89  Demodulation         : 0.26
% 7.86/2.89  BG Simplification    : 0.04
% 7.86/2.89  Subsumption          : 0.74
% 7.86/2.89  Abstraction          : 0.05
% 7.86/2.89  MUC search           : 0.00
% 7.86/2.89  Cooper               : 0.00
% 7.86/2.89  Total                : 2.17
% 7.86/2.89  Index Insertion      : 0.00
% 7.86/2.89  Index Deletion       : 0.00
% 7.86/2.89  Index Matching       : 0.00
% 7.86/2.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------
