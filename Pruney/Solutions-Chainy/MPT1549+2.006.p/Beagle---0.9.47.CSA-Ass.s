%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:03 EST 2020

% Result     : CounterSatisfiable 1.95s
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
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:00:53 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.95/1.27  
% 1.95/1.27  % SZS status CounterSatisfiable for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.27  
% 1.95/1.27  Inference rules
% 1.95/1.27  ----------------------
% 1.95/1.27  #Ref     : 6
% 1.95/1.27  #Sup     : 25
% 1.95/1.27  #Fact    : 0
% 1.95/1.27  #Define  : 0
% 1.95/1.27  #Split   : 0
% 1.95/1.27  #Chain   : 0
% 1.95/1.27  #Close   : 0
% 1.95/1.27  
% 1.95/1.27  Ordering : KBO
% 1.95/1.27  
% 1.95/1.27  Simplification rules
% 1.95/1.27  ----------------------
% 1.95/1.27  #Subsume      : 9
% 1.95/1.27  #Demod        : 29
% 1.95/1.27  #Tautology    : 18
% 1.95/1.27  #SimpNegUnit  : 0
% 1.95/1.27  #BackRed      : 5
% 1.95/1.27  
% 1.95/1.27  #Partial instantiations: 0
% 1.95/1.27  #Strategies tried      : 1
% 1.95/1.27  
% 1.95/1.27  Timing (in seconds)
% 1.95/1.27  ----------------------
% 1.95/1.28  Preprocessing        : 0.31
% 1.95/1.28  Parsing              : 0.16
% 1.95/1.28  CNF conversion       : 0.02
% 1.95/1.28  Main loop            : 0.16
% 1.95/1.28  Inferencing          : 0.06
% 1.95/1.28  Reduction            : 0.05
% 1.95/1.28  Demodulation         : 0.04
% 1.95/1.28  BG Simplification    : 0.01
% 1.95/1.28  Subsumption          : 0.03
% 1.95/1.28  Abstraction          : 0.01
% 1.95/1.28  MUC search           : 0.00
% 1.95/1.28  Cooper               : 0.00
% 1.95/1.28  Total                : 0.48
% 1.95/1.28  Index Insertion      : 0.00
% 1.95/1.28  Index Deletion       : 0.00
% 1.95/1.28  Index Matching       : 0.00
% 1.95/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
