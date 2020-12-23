%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:51 EST 2020

% Result     : CounterSatisfiable 4.99s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:58:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.99/2.01  
% 4.99/2.01  % SZS status CounterSatisfiable for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.99/2.01  
% 4.99/2.01  Inference rules
% 4.99/2.01  ----------------------
% 4.99/2.01  #Ref     : 6
% 4.99/2.01  #Sup     : 726
% 4.99/2.01  #Fact    : 0
% 4.99/2.01  #Define  : 0
% 4.99/2.01  #Split   : 4
% 4.99/2.01  #Chain   : 0
% 4.99/2.01  #Close   : 0
% 4.99/2.01  
% 4.99/2.01  Ordering : KBO
% 4.99/2.01  
% 4.99/2.01  Simplification rules
% 4.99/2.01  ----------------------
% 4.99/2.01  #Subsume      : 194
% 4.99/2.01  #Demod        : 307
% 4.99/2.01  #Tautology    : 471
% 4.99/2.01  #SimpNegUnit  : 4
% 4.99/2.01  #BackRed      : 1
% 4.99/2.01  
% 4.99/2.01  #Partial instantiations: 0
% 4.99/2.01  #Strategies tried      : 1
% 4.99/2.01  
% 4.99/2.01  Timing (in seconds)
% 4.99/2.01  ----------------------
% 4.99/2.01  Preprocessing        : 0.33
% 4.99/2.01  Parsing              : 0.17
% 4.99/2.01  CNF conversion       : 0.02
% 4.99/2.01  Main loop            : 0.90
% 4.99/2.01  Inferencing          : 0.29
% 4.99/2.01  Reduction            : 0.34
% 4.99/2.01  Demodulation         : 0.28
% 4.99/2.01  BG Simplification    : 0.05
% 4.99/2.01  Subsumption          : 0.18
% 4.99/2.01  Abstraction          : 0.06
% 4.99/2.01  MUC search           : 0.00
% 4.99/2.01  Cooper               : 0.00
% 4.99/2.01  Total                : 1.23
% 4.99/2.01  Index Insertion      : 0.00
% 4.99/2.01  Index Deletion       : 0.00
% 4.99/2.01  Index Matching       : 0.00
% 4.99/2.01  BG Taut test         : 0.00
%------------------------------------------------------------------------------
