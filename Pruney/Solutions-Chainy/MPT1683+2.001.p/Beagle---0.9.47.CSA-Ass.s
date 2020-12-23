%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:03 EST 2020

% Result     : CounterSatisfiable 4.91s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 14:58:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.91/1.88  
% 4.91/1.88  % SZS status CounterSatisfiable for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.91/1.88  
% 4.91/1.88  Inference rules
% 4.91/1.88  ----------------------
% 4.91/1.88  #Ref     : 0
% 4.91/1.88  #Sup     : 355
% 4.91/1.88  #Fact    : 0
% 4.91/1.88  #Define  : 0
% 4.91/1.88  #Split   : 3
% 4.91/1.88  #Chain   : 0
% 4.91/1.88  #Close   : 0
% 4.91/1.88  
% 4.91/1.88  Ordering : KBO
% 4.91/1.88  
% 4.91/1.88  Simplification rules
% 4.91/1.88  ----------------------
% 4.91/1.88  #Subsume      : 124
% 4.91/1.88  #Demod        : 532
% 4.91/1.88  #Tautology    : 170
% 4.91/1.88  #SimpNegUnit  : 163
% 4.91/1.88  #BackRed      : 0
% 4.91/1.88  
% 4.91/1.88  #Partial instantiations: 0
% 4.91/1.88  #Strategies tried      : 1
% 4.91/1.88  
% 4.91/1.88  Timing (in seconds)
% 4.91/1.88  ----------------------
% 4.91/1.89  Preprocessing        : 0.32
% 4.91/1.89  Parsing              : 0.17
% 4.91/1.89  CNF conversion       : 0.03
% 4.91/1.89  Main loop            : 0.88
% 4.91/1.89  Inferencing          : 0.35
% 4.91/1.89  Reduction            : 0.27
% 4.91/1.89  Demodulation         : 0.18
% 4.91/1.89  BG Simplification    : 0.04
% 4.91/1.89  Subsumption          : 0.18
% 4.91/1.89  Abstraction          : 0.05
% 4.91/1.89  MUC search           : 0.00
% 4.91/1.89  Cooper               : 0.00
% 4.91/1.89  Total                : 1.21
% 4.91/1.89  Index Insertion      : 0.00
% 4.91/1.89  Index Deletion       : 0.00
% 4.91/1.89  Index Matching       : 0.00
% 4.91/1.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------
