%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:56 EST 2020

% Result     : CounterSatisfiable 2.15s
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
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:12:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.15/1.21  
% 2.15/1.21  % SZS status CounterSatisfiable for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.15/1.21  
% 2.15/1.21  Inference rules
% 2.15/1.21  ----------------------
% 2.15/1.21  #Ref     : 0
% 2.15/1.21  #Sup     : 14
% 2.15/1.21  #Fact    : 0
% 2.15/1.21  #Define  : 0
% 2.15/1.21  #Split   : 3
% 2.15/1.21  #Chain   : 0
% 2.15/1.21  #Close   : 0
% 2.15/1.21  
% 2.15/1.21  Ordering : KBO
% 2.15/1.21  
% 2.15/1.21  Simplification rules
% 2.15/1.21  ----------------------
% 2.15/1.21  #Subsume      : 1
% 2.15/1.21  #Demod        : 0
% 2.15/1.21  #Tautology    : 2
% 2.15/1.21  #SimpNegUnit  : 0
% 2.15/1.21  #BackRed      : 0
% 2.15/1.21  
% 2.15/1.21  #Partial instantiations: 0
% 2.15/1.21  #Strategies tried      : 1
% 2.15/1.21  
% 2.15/1.21  Timing (in seconds)
% 2.15/1.21  ----------------------
% 2.15/1.22  Preprocessing        : 0.28
% 2.15/1.22  Parsing              : 0.15
% 2.15/1.22  CNF conversion       : 0.03
% 2.15/1.22  Main loop            : 0.20
% 2.15/1.22  Inferencing          : 0.10
% 2.15/1.22  Reduction            : 0.04
% 2.15/1.22  Demodulation         : 0.02
% 2.15/1.22  BG Simplification    : 0.02
% 2.15/1.22  Subsumption          : 0.03
% 2.15/1.22  Abstraction          : 0.01
% 2.15/1.22  MUC search           : 0.00
% 2.15/1.22  Cooper               : 0.00
% 2.15/1.22  Total                : 0.48
% 2.30/1.22  Index Insertion      : 0.00
% 2.30/1.22  Index Deletion       : 0.00
% 2.30/1.22  Index Matching       : 0.00
% 2.30/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
