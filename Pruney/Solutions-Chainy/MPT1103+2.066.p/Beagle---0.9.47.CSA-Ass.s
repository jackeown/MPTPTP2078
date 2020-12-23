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
% DateTime   : Thu Dec  3 10:18:39 EST 2020

% Result     : CounterSatisfiable 2.46s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:40:21 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.46/1.41  
% 2.46/1.41  % SZS status CounterSatisfiable for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.46/1.41  
% 2.46/1.41  Inference rules
% 2.46/1.41  ----------------------
% 2.46/1.41  #Ref     : 0
% 2.46/1.41  #Sup     : 179
% 2.46/1.41  #Fact    : 0
% 2.46/1.41  #Define  : 0
% 2.46/1.41  #Split   : 3
% 2.46/1.41  #Chain   : 0
% 2.46/1.41  #Close   : 0
% 2.46/1.41  
% 2.46/1.41  Ordering : KBO
% 2.46/1.41  
% 2.46/1.41  Simplification rules
% 2.46/1.41  ----------------------
% 2.46/1.41  #Subsume      : 0
% 2.46/1.41  #Demod        : 68
% 2.46/1.41  #Tautology    : 146
% 2.46/1.41  #SimpNegUnit  : 2
% 2.46/1.41  #BackRed      : 4
% 2.46/1.41  
% 2.46/1.41  #Partial instantiations: 0
% 2.46/1.41  #Strategies tried      : 1
% 2.46/1.41  
% 2.46/1.41  Timing (in seconds)
% 2.46/1.41  ----------------------
% 2.46/1.41  Preprocessing        : 0.33
% 2.46/1.41  Parsing              : 0.18
% 2.46/1.41  CNF conversion       : 0.02
% 2.46/1.41  Main loop            : 0.27
% 2.46/1.41  Inferencing          : 0.10
% 2.46/1.41  Reduction            : 0.09
% 2.46/1.41  Demodulation         : 0.07
% 2.46/1.41  BG Simplification    : 0.02
% 2.46/1.41  Subsumption          : 0.04
% 2.46/1.41  Abstraction          : 0.02
% 2.46/1.41  MUC search           : 0.00
% 2.46/1.41  Cooper               : 0.00
% 2.46/1.41  Total                : 0.62
% 2.46/1.41  Index Insertion      : 0.00
% 2.46/1.41  Index Deletion       : 0.00
% 2.46/1.41  Index Matching       : 0.00
% 2.46/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
