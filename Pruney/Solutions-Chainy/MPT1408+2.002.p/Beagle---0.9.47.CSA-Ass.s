%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:35 EST 2020

% Result     : CounterSatisfiable 3.36s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 14:56:29 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.36/1.55  
% 3.36/1.55  % SZS status CounterSatisfiable for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.36/1.55  
% 3.36/1.55  Inference rules
% 3.36/1.55  ----------------------
% 3.36/1.55  #Ref     : 0
% 3.36/1.55  #Sup     : 174
% 3.36/1.55  #Fact    : 0
% 3.36/1.55  #Define  : 0
% 3.36/1.55  #Split   : 9
% 3.36/1.55  #Chain   : 0
% 3.36/1.55  #Close   : 0
% 3.36/1.55  
% 3.36/1.55  Ordering : KBO
% 3.36/1.55  
% 3.36/1.55  Simplification rules
% 3.36/1.55  ----------------------
% 3.36/1.55  #Subsume      : 3
% 3.36/1.55  #Demod        : 177
% 3.36/1.55  #Tautology    : 112
% 3.36/1.55  #SimpNegUnit  : 60
% 3.36/1.55  #BackRed      : 1
% 3.36/1.55  
% 3.36/1.55  #Partial instantiations: 0
% 3.36/1.55  #Strategies tried      : 1
% 3.36/1.55  
% 3.36/1.55  Timing (in seconds)
% 3.36/1.55  ----------------------
% 3.36/1.55  Preprocessing        : 0.37
% 3.36/1.55  Parsing              : 0.19
% 3.36/1.55  CNF conversion       : 0.03
% 3.36/1.55  Main loop            : 0.41
% 3.36/1.55  Inferencing          : 0.15
% 3.36/1.55  Reduction            : 0.13
% 3.36/1.55  Demodulation         : 0.09
% 3.36/1.55  BG Simplification    : 0.03
% 3.36/1.55  Subsumption          : 0.07
% 3.36/1.55  Abstraction          : 0.02
% 3.36/1.55  MUC search           : 0.00
% 3.36/1.55  Cooper               : 0.00
% 3.36/1.55  Total                : 0.79
% 3.36/1.55  Index Insertion      : 0.00
% 3.36/1.55  Index Deletion       : 0.00
% 3.36/1.55  Index Matching       : 0.00
% 3.36/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
