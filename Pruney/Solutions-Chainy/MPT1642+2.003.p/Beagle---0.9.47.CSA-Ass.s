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
% DateTime   : Thu Dec  3 10:25:50 EST 2020

% Result     : CounterSatisfiable 2.58s
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
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:37:05 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.58/1.66  
% 2.58/1.66  % SZS status CounterSatisfiable for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.58/1.66  
% 2.58/1.66  Inference rules
% 2.58/1.66  ----------------------
% 2.58/1.66  #Ref     : 0
% 2.58/1.66  #Sup     : 17
% 2.58/1.66  #Fact    : 0
% 2.58/1.66  #Define  : 0
% 2.58/1.66  #Split   : 0
% 2.58/1.66  #Chain   : 0
% 2.58/1.66  #Close   : 0
% 2.58/1.66  
% 2.58/1.66  Ordering : KBO
% 2.58/1.66  
% 2.58/1.66  Simplification rules
% 2.58/1.66  ----------------------
% 2.58/1.66  #Subsume      : 2
% 2.58/1.66  #Demod        : 4
% 2.58/1.66  #Tautology    : 2
% 2.58/1.66  #SimpNegUnit  : 0
% 2.58/1.66  #BackRed      : 0
% 2.58/1.66  
% 2.58/1.66  #Partial instantiations: 0
% 2.58/1.66  #Strategies tried      : 1
% 2.58/1.66  
% 2.58/1.66  Timing (in seconds)
% 2.58/1.66  ----------------------
% 2.58/1.67  Preprocessing        : 0.45
% 2.58/1.67  Parsing              : 0.24
% 2.58/1.67  CNF conversion       : 0.04
% 2.58/1.67  Main loop            : 0.32
% 2.58/1.67  Inferencing          : 0.15
% 2.58/1.67  Reduction            : 0.07
% 2.58/1.67  Demodulation         : 0.06
% 2.58/1.67  BG Simplification    : 0.02
% 2.58/1.67  Subsumption          : 0.06
% 2.58/1.67  Abstraction          : 0.01
% 2.58/1.67  MUC search           : 0.00
% 2.58/1.67  Cooper               : 0.00
% 2.58/1.67  Total                : 0.78
% 2.58/1.67  Index Insertion      : 0.00
% 2.58/1.67  Index Deletion       : 0.00
% 2.58/1.67  Index Matching       : 0.00
% 2.58/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
