%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:02 EST 2020

% Result     : CounterSatisfiable 3.05s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:54:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.05/1.48  
% 3.05/1.48  % SZS status CounterSatisfiable for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.05/1.48  
% 3.05/1.48  Inference rules
% 3.05/1.48  ----------------------
% 3.05/1.48  #Ref     : 0
% 3.05/1.48  #Sup     : 38
% 3.05/1.48  #Fact    : 0
% 3.05/1.48  #Define  : 0
% 3.05/1.48  #Split   : 1
% 3.05/1.48  #Chain   : 0
% 3.05/1.48  #Close   : 0
% 3.05/1.48  
% 3.05/1.48  Ordering : KBO
% 3.05/1.48  
% 3.05/1.48  Simplification rules
% 3.05/1.48  ----------------------
% 3.05/1.48  #Subsume      : 16
% 3.05/1.48  #Demod        : 1
% 3.05/1.48  #Tautology    : 10
% 3.05/1.48  #SimpNegUnit  : 0
% 3.05/1.48  #BackRed      : 0
% 3.05/1.48  
% 3.05/1.48  #Partial instantiations: 0
% 3.05/1.48  #Strategies tried      : 1
% 3.05/1.48  
% 3.05/1.48  Timing (in seconds)
% 3.05/1.48  ----------------------
% 3.05/1.49  Preprocessing        : 0.38
% 3.05/1.49  Parsing              : 0.20
% 3.05/1.49  CNF conversion       : 0.03
% 3.05/1.49  Main loop            : 0.35
% 3.05/1.49  Inferencing          : 0.15
% 3.05/1.49  Reduction            : 0.08
% 3.05/1.49  Demodulation         : 0.06
% 3.05/1.49  BG Simplification    : 0.03
% 3.05/1.49  Subsumption          : 0.08
% 3.05/1.49  Abstraction          : 0.02
% 3.05/1.49  MUC search           : 0.00
% 3.05/1.49  Cooper               : 0.00
% 3.05/1.49  Total                : 0.74
% 3.05/1.49  Index Insertion      : 0.00
% 3.05/1.49  Index Deletion       : 0.00
% 3.05/1.49  Index Matching       : 0.00
% 3.05/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
