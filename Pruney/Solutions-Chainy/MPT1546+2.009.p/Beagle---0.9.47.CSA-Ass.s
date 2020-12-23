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
% DateTime   : Thu Dec  3 10:25:01 EST 2020

% Result     : CounterSatisfiable 1.95s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:12:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.95/1.30  
% 1.95/1.30  % SZS status CounterSatisfiable for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.30  
% 1.95/1.30  Inference rules
% 1.95/1.30  ----------------------
% 1.95/1.30  #Ref     : 0
% 1.95/1.30  #Sup     : 10
% 1.95/1.30  #Fact    : 0
% 1.95/1.30  #Define  : 0
% 1.95/1.30  #Split   : 3
% 1.95/1.30  #Chain   : 0
% 1.95/1.30  #Close   : 0
% 1.95/1.30  
% 1.95/1.30  Ordering : KBO
% 1.95/1.30  
% 1.95/1.30  Simplification rules
% 1.95/1.30  ----------------------
% 1.95/1.30  #Subsume      : 1
% 1.95/1.30  #Demod        : 5
% 1.95/1.30  #Tautology    : 5
% 1.95/1.30  #SimpNegUnit  : 2
% 1.95/1.30  #BackRed      : 0
% 1.95/1.30  
% 1.95/1.30  #Partial instantiations: 0
% 1.95/1.30  #Strategies tried      : 1
% 1.95/1.30  
% 1.95/1.30  Timing (in seconds)
% 1.95/1.30  ----------------------
% 1.95/1.30  Preprocessing        : 0.33
% 1.95/1.30  Parsing              : 0.17
% 1.95/1.30  CNF conversion       : 0.02
% 1.95/1.30  Main loop            : 0.16
% 1.95/1.30  Inferencing          : 0.06
% 1.95/1.30  Reduction            : 0.04
% 1.95/1.30  Demodulation         : 0.03
% 1.95/1.30  BG Simplification    : 0.02
% 1.95/1.30  Subsumption          : 0.02
% 1.95/1.30  Abstraction          : 0.01
% 1.95/1.30  MUC search           : 0.00
% 1.95/1.30  Cooper               : 0.00
% 1.95/1.30  Total                : 0.51
% 1.95/1.30  Index Insertion      : 0.00
% 1.95/1.30  Index Deletion       : 0.00
% 1.95/1.30  Index Matching       : 0.00
% 1.95/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
