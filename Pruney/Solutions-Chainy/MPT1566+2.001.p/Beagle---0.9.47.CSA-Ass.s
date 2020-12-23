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
% DateTime   : Thu Dec  3 10:25:12 EST 2020

% Result     : CounterSatisfiable 2.95s
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
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:16:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.38  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.95/1.56  
% 2.95/1.56  % SZS status CounterSatisfiable for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.95/1.56  
% 2.95/1.56  Inference rules
% 2.95/1.56  ----------------------
% 2.95/1.56  #Ref     : 0
% 2.95/1.56  #Sup     : 69
% 2.95/1.56  #Fact    : 0
% 2.95/1.56  #Define  : 0
% 2.95/1.56  #Split   : 1
% 2.95/1.56  #Chain   : 0
% 2.95/1.56  #Close   : 0
% 2.95/1.56  
% 2.95/1.56  Ordering : KBO
% 2.95/1.56  
% 2.95/1.56  Simplification rules
% 2.95/1.56  ----------------------
% 2.95/1.56  #Subsume      : 5
% 2.95/1.56  #Demod        : 15
% 2.95/1.56  #Tautology    : 39
% 2.95/1.56  #SimpNegUnit  : 4
% 2.95/1.56  #BackRed      : 0
% 2.95/1.56  
% 2.95/1.56  #Partial instantiations: 0
% 2.95/1.56  #Strategies tried      : 1
% 2.95/1.56  
% 2.95/1.56  Timing (in seconds)
% 2.95/1.56  ----------------------
% 2.95/1.56  Preprocessing        : 0.37
% 2.95/1.56  Parsing              : 0.20
% 2.95/1.56  CNF conversion       : 0.03
% 2.95/1.56  Main loop            : 0.34
% 2.95/1.56  Inferencing          : 0.13
% 2.95/1.56  Reduction            : 0.08
% 2.95/1.56  Demodulation         : 0.05
% 2.95/1.56  BG Simplification    : 0.02
% 2.95/1.56  Subsumption          : 0.08
% 2.95/1.56  Abstraction          : 0.02
% 2.95/1.56  MUC search           : 0.00
% 2.95/1.56  Cooper               : 0.00
% 2.95/1.56  Total                : 0.71
% 2.95/1.56  Index Insertion      : 0.00
% 2.95/1.56  Index Deletion       : 0.00
% 2.95/1.56  Index Matching       : 0.00
% 2.95/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
