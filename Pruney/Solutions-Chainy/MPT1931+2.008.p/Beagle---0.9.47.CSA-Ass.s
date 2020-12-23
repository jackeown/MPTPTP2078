%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:48 EST 2020

% Result     : CounterSatisfiable 2.18s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:42:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.18/1.22  
% 2.18/1.22  % SZS status CounterSatisfiable for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.22  
% 2.18/1.22  Inference rules
% 2.18/1.22  ----------------------
% 2.18/1.22  #Ref     : 0
% 2.18/1.22  #Sup     : 12
% 2.18/1.22  #Fact    : 0
% 2.18/1.22  #Define  : 0
% 2.18/1.22  #Split   : 0
% 2.18/1.22  #Chain   : 0
% 2.18/1.22  #Close   : 0
% 2.18/1.22  
% 2.18/1.22  Ordering : KBO
% 2.18/1.22  
% 2.18/1.22  Simplification rules
% 2.18/1.22  ----------------------
% 2.18/1.22  #Subsume      : 4
% 2.18/1.22  #Demod        : 2
% 2.18/1.22  #Tautology    : 1
% 2.18/1.22  #SimpNegUnit  : 2
% 2.18/1.22  #BackRed      : 0
% 2.18/1.22  
% 2.18/1.22  #Partial instantiations: 0
% 2.18/1.22  #Strategies tried      : 1
% 2.18/1.22  
% 2.18/1.22  Timing (in seconds)
% 2.18/1.22  ----------------------
% 2.18/1.23  Preprocessing        : 0.29
% 2.18/1.23  Parsing              : 0.16
% 2.18/1.23  CNF conversion       : 0.03
% 2.18/1.23  Main loop            : 0.18
% 2.18/1.23  Inferencing          : 0.09
% 2.18/1.23  Reduction            : 0.04
% 2.18/1.23  Demodulation         : 0.03
% 2.18/1.23  BG Simplification    : 0.02
% 2.18/1.23  Subsumption          : 0.03
% 2.18/1.23  Abstraction          : 0.01
% 2.18/1.23  MUC search           : 0.00
% 2.18/1.23  Cooper               : 0.00
% 2.18/1.23  Total                : 0.48
% 2.18/1.23  Index Insertion      : 0.00
% 2.18/1.23  Index Deletion       : 0.00
% 2.18/1.23  Index Matching       : 0.00
% 2.18/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
