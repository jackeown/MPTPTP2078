%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:55 EST 2020

% Result     : CounterSatisfiable 3.74s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:13:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.74/1.57  
% 3.74/1.57  % SZS status CounterSatisfiable for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.74/1.57  
% 3.74/1.57  Inference rules
% 3.74/1.57  ----------------------
% 3.74/1.57  #Ref     : 0
% 3.74/1.57  #Sup     : 165
% 3.74/1.57  #Fact    : 0
% 3.74/1.57  #Define  : 0
% 3.74/1.57  #Split   : 5
% 3.74/1.57  #Chain   : 0
% 3.74/1.57  #Close   : 0
% 3.74/1.57  
% 3.74/1.57  Ordering : KBO
% 3.74/1.57  
% 3.74/1.57  Simplification rules
% 3.74/1.57  ----------------------
% 3.74/1.57  #Subsume      : 127
% 3.74/1.57  #Demod        : 139
% 3.74/1.57  #Tautology    : 11
% 3.74/1.57  #SimpNegUnit  : 8
% 3.74/1.57  #BackRed      : 0
% 3.74/1.57  
% 3.74/1.57  #Partial instantiations: 0
% 3.74/1.57  #Strategies tried      : 1
% 3.74/1.57  
% 3.74/1.57  Timing (in seconds)
% 3.74/1.57  ----------------------
% 3.74/1.57  Preprocessing        : 0.29
% 3.74/1.57  Parsing              : 0.16
% 3.74/1.57  CNF conversion       : 0.02
% 3.74/1.57  Main loop            : 0.53
% 3.74/1.57  Inferencing          : 0.21
% 3.74/1.57  Reduction            : 0.14
% 3.74/1.57  Demodulation         : 0.09
% 3.74/1.57  BG Simplification    : 0.02
% 3.74/1.57  Subsumption          : 0.12
% 3.74/1.57  Abstraction          : 0.02
% 3.74/1.57  MUC search           : 0.00
% 3.74/1.57  Cooper               : 0.00
% 3.74/1.57  Total                : 0.83
% 3.74/1.57  Index Insertion      : 0.00
% 3.74/1.57  Index Deletion       : 0.00
% 3.74/1.57  Index Matching       : 0.00
% 3.74/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
