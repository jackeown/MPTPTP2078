%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:19 EST 2020

% Result     : CounterSatisfiable 2.14s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:44:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.14/1.22  
% 2.14/1.22  % SZS status CounterSatisfiable for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.22  
% 2.14/1.22  Inference rules
% 2.14/1.22  ----------------------
% 2.14/1.22  #Ref     : 0
% 2.14/1.22  #Sup     : 35
% 2.14/1.22  #Fact    : 0
% 2.14/1.22  #Define  : 0
% 2.14/1.22  #Split   : 3
% 2.14/1.22  #Chain   : 0
% 2.14/1.22  #Close   : 0
% 2.14/1.22  
% 2.14/1.22  Ordering : KBO
% 2.14/1.22  
% 2.14/1.22  Simplification rules
% 2.14/1.22  ----------------------
% 2.14/1.22  #Subsume      : 4
% 2.14/1.22  #Demod        : 9
% 2.14/1.22  #Tautology    : 19
% 2.14/1.22  #SimpNegUnit  : 2
% 2.14/1.22  #BackRed      : 0
% 2.14/1.22  
% 2.14/1.22  #Partial instantiations: 0
% 2.14/1.22  #Strategies tried      : 1
% 2.14/1.22  
% 2.14/1.22  Timing (in seconds)
% 2.14/1.22  ----------------------
% 2.14/1.23  Preprocessing        : 0.30
% 2.14/1.23  Parsing              : 0.16
% 2.14/1.23  CNF conversion       : 0.03
% 2.14/1.23  Main loop            : 0.18
% 2.14/1.23  Inferencing          : 0.06
% 2.14/1.23  Reduction            : 0.06
% 2.14/1.23  Demodulation         : 0.04
% 2.14/1.23  BG Simplification    : 0.01
% 2.14/1.23  Subsumption          : 0.03
% 2.14/1.23  Abstraction          : 0.01
% 2.14/1.23  MUC search           : 0.00
% 2.14/1.23  Cooper               : 0.00
% 2.14/1.23  Total                : 0.48
% 2.14/1.23  Index Insertion      : 0.00
% 2.14/1.23  Index Deletion       : 0.00
% 2.14/1.23  Index Matching       : 0.00
% 2.14/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
