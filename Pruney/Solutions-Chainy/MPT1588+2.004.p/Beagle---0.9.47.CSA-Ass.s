%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:18 EST 2020

% Result     : CounterSatisfiable 1.91s
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
% 0.13/0.33  % Computer   : n023.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:06:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.91/1.20  
% 1.91/1.20  % SZS status CounterSatisfiable for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.20  
% 1.91/1.20  Inference rules
% 1.91/1.20  ----------------------
% 1.91/1.20  #Ref     : 0
% 1.91/1.20  #Sup     : 1
% 1.91/1.20  #Fact    : 0
% 1.91/1.20  #Define  : 0
% 1.91/1.20  #Split   : 1
% 1.91/1.20  #Chain   : 0
% 1.91/1.20  #Close   : 0
% 1.91/1.20  
% 1.91/1.20  Ordering : KBO
% 1.91/1.20  
% 1.91/1.20  Simplification rules
% 1.91/1.20  ----------------------
% 1.91/1.20  #Subsume      : 0
% 1.91/1.20  #Demod        : 0
% 1.91/1.20  #Tautology    : 0
% 1.91/1.20  #SimpNegUnit  : 0
% 1.91/1.20  #BackRed      : 0
% 1.91/1.20  
% 1.91/1.20  #Partial instantiations: 0
% 1.91/1.20  #Strategies tried      : 1
% 1.91/1.20  
% 1.91/1.20  Timing (in seconds)
% 1.91/1.20  ----------------------
% 1.91/1.20  Preprocessing        : 0.32
% 1.91/1.20  Parsing              : 0.17
% 1.91/1.20  CNF conversion       : 0.02
% 1.91/1.20  Main loop            : 0.11
% 1.91/1.21  Inferencing          : 0.05
% 1.91/1.21  Reduction            : 0.03
% 1.91/1.21  Demodulation         : 0.02
% 1.91/1.21  BG Simplification    : 0.01
% 1.91/1.21  Subsumption          : 0.01
% 1.91/1.21  Abstraction          : 0.00
% 1.91/1.21  MUC search           : 0.00
% 1.91/1.21  Cooper               : 0.00
% 1.91/1.21  Total                : 0.44
% 1.91/1.21  Index Insertion      : 0.00
% 1.91/1.21  Index Deletion       : 0.00
% 1.91/1.21  Index Matching       : 0.00
% 1.91/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
