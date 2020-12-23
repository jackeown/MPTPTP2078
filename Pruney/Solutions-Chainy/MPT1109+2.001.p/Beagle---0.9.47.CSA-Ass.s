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
% DateTime   : Thu Dec  3 10:18:57 EST 2020

% Result     : CounterSatisfiable 14.73s
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
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:19:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.73/7.72  
% 14.73/7.73  % SZS status CounterSatisfiable for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.73/7.73  
% 14.73/7.73  Inference rules
% 14.73/7.73  ----------------------
% 14.73/7.73  #Ref     : 10
% 14.73/7.73  #Sup     : 3406
% 14.73/7.73  #Fact    : 8
% 14.73/7.73  #Define  : 0
% 14.73/7.73  #Split   : 17
% 14.73/7.73  #Chain   : 0
% 14.73/7.73  #Close   : 0
% 14.73/7.73  
% 14.73/7.73  Ordering : KBO
% 14.73/7.73  
% 14.73/7.73  Simplification rules
% 14.73/7.73  ----------------------
% 14.73/7.73  #Subsume      : 2366
% 14.73/7.73  #Demod        : 4973
% 14.73/7.73  #Tautology    : 708
% 14.73/7.73  #SimpNegUnit  : 854
% 14.73/7.73  #BackRed      : 14
% 14.73/7.73  
% 14.73/7.73  #Partial instantiations: 0
% 14.73/7.73  #Strategies tried      : 1
% 14.73/7.73  
% 14.73/7.73  Timing (in seconds)
% 14.73/7.73  ----------------------
% 14.73/7.73  Preprocessing        : 0.33
% 14.73/7.73  Parsing              : 0.17
% 14.73/7.73  CNF conversion       : 0.03
% 14.73/7.73  Main loop            : 6.57
% 14.73/7.73  Inferencing          : 1.16
% 14.73/7.73  Reduction            : 1.40
% 14.73/7.73  Demodulation         : 0.87
% 14.73/7.73  BG Simplification    : 0.12
% 14.73/7.73  Subsumption          : 3.72
% 14.73/7.73  Abstraction          : 0.26
% 14.73/7.73  MUC search           : 0.00
% 14.73/7.73  Cooper               : 0.00
% 14.73/7.73  Total                : 6.90
% 14.73/7.73  Index Insertion      : 0.00
% 14.73/7.73  Index Deletion       : 0.00
% 14.73/7.73  Index Matching       : 0.00
% 14.73/7.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
