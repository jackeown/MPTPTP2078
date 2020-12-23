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
% DateTime   : Thu Dec  3 10:18:28 EST 2020

% Result     : CounterSatisfiable 3.82s
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
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:01:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.82/1.98  
% 3.82/1.98  % SZS status CounterSatisfiable for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.82/1.98  
% 3.82/1.98  Inference rules
% 3.82/1.98  ----------------------
% 3.82/1.98  #Ref     : 0
% 3.82/1.98  #Sup     : 244
% 3.82/1.98  #Fact    : 0
% 3.82/1.98  #Define  : 0
% 3.82/1.98  #Split   : 0
% 3.82/1.98  #Chain   : 0
% 3.82/1.98  #Close   : 0
% 3.82/1.98  
% 3.82/1.98  Ordering : KBO
% 3.82/1.98  
% 3.82/1.98  Simplification rules
% 3.82/1.98  ----------------------
% 3.82/1.98  #Subsume      : 10
% 3.82/1.98  #Demod        : 139
% 3.82/1.98  #Tautology    : 180
% 3.82/1.98  #SimpNegUnit  : 0
% 3.82/1.98  #BackRed      : 7
% 3.82/1.98  
% 3.82/1.98  #Partial instantiations: 0
% 3.82/1.98  #Strategies tried      : 1
% 3.82/1.98  
% 3.82/1.98  Timing (in seconds)
% 3.82/1.98  ----------------------
% 3.82/1.99  Preprocessing        : 0.48
% 3.82/1.99  Parsing              : 0.25
% 3.82/1.99  CNF conversion       : 0.03
% 3.82/1.99  Main loop            : 0.69
% 3.82/1.99  Inferencing          : 0.27
% 3.82/1.99  Reduction            : 0.23
% 3.82/1.99  Demodulation         : 0.18
% 3.82/1.99  BG Simplification    : 0.03
% 3.82/1.99  Subsumption          : 0.10
% 3.82/1.99  Abstraction          : 0.04
% 3.82/1.99  MUC search           : 0.00
% 3.82/1.99  Cooper               : 0.00
% 3.82/1.99  Total                : 1.18
% 3.82/1.99  Index Insertion      : 0.00
% 3.82/1.99  Index Deletion       : 0.00
% 3.82/1.99  Index Matching       : 0.00
% 3.82/1.99  BG Taut test         : 0.00
%------------------------------------------------------------------------------
