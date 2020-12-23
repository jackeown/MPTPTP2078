%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:35 EST 2020

% Result     : CounterSatisfiable 1.91s
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
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:36:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.91/1.22  
% 1.91/1.22  % SZS status CounterSatisfiable for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.22  
% 1.91/1.22  Inference rules
% 1.91/1.22  ----------------------
% 1.91/1.22  #Ref     : 0
% 1.91/1.22  #Sup     : 88
% 1.91/1.22  #Fact    : 0
% 1.91/1.22  #Define  : 0
% 1.91/1.22  #Split   : 1
% 1.91/1.22  #Chain   : 0
% 1.91/1.22  #Close   : 0
% 1.91/1.22  
% 1.91/1.22  Ordering : KBO
% 1.91/1.22  
% 1.91/1.22  Simplification rules
% 1.91/1.22  ----------------------
% 1.91/1.22  #Subsume      : 0
% 1.91/1.22  #Demod        : 17
% 1.91/1.22  #Tautology    : 69
% 1.91/1.22  #SimpNegUnit  : 2
% 1.91/1.22  #BackRed      : 2
% 1.91/1.22  
% 1.91/1.22  #Partial instantiations: 0
% 1.91/1.22  #Strategies tried      : 1
% 1.91/1.22  
% 1.91/1.22  Timing (in seconds)
% 1.91/1.22  ----------------------
% 1.91/1.22  Preprocessing        : 0.28
% 1.91/1.22  Parsing              : 0.15
% 1.91/1.22  CNF conversion       : 0.02
% 1.91/1.22  Main loop            : 0.20
% 1.91/1.22  Inferencing          : 0.08
% 1.91/1.22  Reduction            : 0.06
% 1.91/1.22  Demodulation         : 0.05
% 1.91/1.22  BG Simplification    : 0.01
% 1.91/1.22  Subsumption          : 0.03
% 1.91/1.22  Abstraction          : 0.01
% 1.91/1.22  MUC search           : 0.00
% 1.91/1.22  Cooper               : 0.00
% 1.91/1.23  Total                : 0.49
% 1.91/1.23  Index Insertion      : 0.00
% 1.91/1.23  Index Deletion       : 0.00
% 1.91/1.23  Index Matching       : 0.00
% 1.91/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
