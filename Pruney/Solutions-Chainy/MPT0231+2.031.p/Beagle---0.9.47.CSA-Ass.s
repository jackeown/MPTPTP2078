%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:18 EST 2020

% Result     : CounterSatisfiable 1.78s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:37:14 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.78/1.06  
% 1.78/1.06  % SZS status CounterSatisfiable for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.78/1.06  
% 1.78/1.06  Inference rules
% 1.78/1.06  ----------------------
% 1.78/1.06  #Ref     : 0
% 1.78/1.06  #Sup     : 22
% 1.78/1.06  #Fact    : 0
% 1.78/1.06  #Define  : 0
% 1.78/1.06  #Split   : 1
% 1.78/1.06  #Chain   : 0
% 1.78/1.06  #Close   : 0
% 1.78/1.06  
% 1.78/1.06  Ordering : KBO
% 1.78/1.06  
% 1.78/1.06  Simplification rules
% 1.78/1.06  ----------------------
% 1.78/1.06  #Subsume      : 0
% 1.78/1.06  #Demod        : 3
% 1.78/1.06  #Tautology    : 21
% 1.78/1.06  #SimpNegUnit  : 0
% 1.78/1.06  #BackRed      : 1
% 1.78/1.06  
% 1.78/1.06  #Partial instantiations: 0
% 1.78/1.06  #Strategies tried      : 1
% 1.78/1.06  
% 1.78/1.06  Timing (in seconds)
% 1.78/1.06  ----------------------
% 1.78/1.07  Preprocessing        : 0.29
% 1.78/1.07  Parsing              : 0.15
% 1.78/1.07  CNF conversion       : 0.02
% 1.78/1.07  Main loop            : 0.12
% 1.78/1.07  Inferencing          : 0.05
% 1.78/1.07  Reduction            : 0.04
% 1.78/1.07  Demodulation         : 0.03
% 1.78/1.07  BG Simplification    : 0.01
% 1.78/1.07  Subsumption          : 0.02
% 1.78/1.07  Abstraction          : 0.01
% 1.78/1.07  MUC search           : 0.00
% 1.78/1.07  Cooper               : 0.00
% 1.78/1.07  Total                : 0.42
% 1.78/1.07  Index Insertion      : 0.00
% 1.78/1.07  Index Deletion       : 0.00
% 1.78/1.07  Index Matching       : 0.00
% 1.78/1.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------
