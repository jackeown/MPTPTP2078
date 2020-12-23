%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:07 EST 2020

% Result     : CounterSatisfiable 2.34s
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
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:32:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.34/1.35  
% 2.34/1.35  % SZS status CounterSatisfiable for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.34/1.35  
% 2.34/1.35  Inference rules
% 2.34/1.35  ----------------------
% 2.34/1.35  #Ref     : 0
% 2.34/1.35  #Sup     : 18
% 2.34/1.35  #Fact    : 0
% 2.34/1.35  #Define  : 0
% 2.34/1.35  #Split   : 2
% 2.34/1.35  #Chain   : 0
% 2.34/1.35  #Close   : 0
% 2.34/1.35  
% 2.34/1.35  Ordering : KBO
% 2.34/1.35  
% 2.34/1.35  Simplification rules
% 2.34/1.35  ----------------------
% 2.34/1.35  #Subsume      : 10
% 2.34/1.35  #Demod        : 0
% 2.34/1.35  #Tautology    : 10
% 2.34/1.35  #SimpNegUnit  : 1
% 2.34/1.35  #BackRed      : 0
% 2.34/1.35  
% 2.34/1.35  #Partial instantiations: 0
% 2.34/1.35  #Strategies tried      : 1
% 2.34/1.35  
% 2.34/1.35  Timing (in seconds)
% 2.34/1.35  ----------------------
% 2.34/1.35  Preprocessing        : 0.34
% 2.34/1.35  Parsing              : 0.18
% 2.34/1.35  CNF conversion       : 0.03
% 2.34/1.35  Main loop            : 0.23
% 2.34/1.35  Inferencing          : 0.09
% 2.34/1.35  Reduction            : 0.05
% 2.34/1.35  Demodulation         : 0.03
% 2.34/1.35  BG Simplification    : 0.02
% 2.34/1.35  Subsumption          : 0.06
% 2.34/1.35  Abstraction          : 0.01
% 2.34/1.35  MUC search           : 0.00
% 2.34/1.35  Cooper               : 0.00
% 2.34/1.35  Total                : 0.57
% 2.34/1.35  Index Insertion      : 0.00
% 2.34/1.35  Index Deletion       : 0.00
% 2.34/1.35  Index Matching       : 0.00
% 2.34/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
