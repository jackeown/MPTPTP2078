%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:14 EST 2020

% Result     : CounterSatisfiable 1.76s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n019.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 17:59:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.76/1.22  
% 1.76/1.22  % SZS status CounterSatisfiable for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.76/1.22  
% 1.76/1.22  Inference rules
% 1.76/1.22  ----------------------
% 1.76/1.22  #Ref     : 0
% 1.76/1.22  #Sup     : 27
% 1.76/1.22  #Fact    : 0
% 1.76/1.22  #Define  : 0
% 1.76/1.22  #Split   : 1
% 1.76/1.22  #Chain   : 0
% 1.76/1.22  #Close   : 0
% 1.76/1.22  
% 1.76/1.22  Ordering : KBO
% 1.76/1.22  
% 1.76/1.22  Simplification rules
% 1.76/1.22  ----------------------
% 1.76/1.22  #Subsume      : 0
% 1.76/1.22  #Demod        : 8
% 1.76/1.22  #Tautology    : 23
% 1.76/1.22  #SimpNegUnit  : 1
% 1.76/1.22  #BackRed      : 1
% 1.76/1.22  
% 1.76/1.22  #Partial instantiations: 0
% 1.76/1.22  #Strategies tried      : 1
% 1.76/1.22  
% 1.76/1.22  Timing (in seconds)
% 1.76/1.22  ----------------------
% 1.76/1.23  Preprocessing        : 0.30
% 1.76/1.23  Parsing              : 0.17
% 1.76/1.23  CNF conversion       : 0.02
% 1.76/1.23  Main loop            : 0.12
% 1.76/1.23  Inferencing          : 0.04
% 1.76/1.23  Reduction            : 0.04
% 1.76/1.23  Demodulation         : 0.03
% 1.76/1.23  BG Simplification    : 0.01
% 1.76/1.23  Subsumption          : 0.01
% 1.76/1.23  Abstraction          : 0.01
% 1.76/1.23  MUC search           : 0.00
% 1.76/1.23  Cooper               : 0.00
% 1.76/1.23  Total                : 0.43
% 1.76/1.23  Index Insertion      : 0.00
% 1.76/1.23  Index Deletion       : 0.00
% 1.76/1.23  Index Matching       : 0.00
% 1.76/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
