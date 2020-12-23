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
% DateTime   : Thu Dec  3 10:30:57 EST 2020

% Result     : CounterSatisfiable 3.90s
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
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:48:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.90/1.64  
% 3.90/1.64  % SZS status CounterSatisfiable for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.90/1.64  
% 3.90/1.64  Inference rules
% 3.90/1.64  ----------------------
% 3.90/1.64  #Ref     : 0
% 3.90/1.64  #Sup     : 123
% 3.90/1.64  #Fact    : 0
% 3.90/1.64  #Define  : 0
% 3.90/1.64  #Split   : 2
% 3.90/1.64  #Chain   : 0
% 3.90/1.64  #Close   : 0
% 3.90/1.64  
% 3.90/1.64  Ordering : KBO
% 3.90/1.64  
% 3.90/1.64  Simplification rules
% 3.90/1.64  ----------------------
% 3.90/1.64  #Subsume      : 67
% 3.90/1.64  #Demod        : 166
% 3.90/1.64  #Tautology    : 31
% 3.90/1.64  #SimpNegUnit  : 6
% 3.90/1.64  #BackRed      : 0
% 3.90/1.64  
% 3.90/1.64  #Partial instantiations: 0
% 3.90/1.64  #Strategies tried      : 1
% 3.90/1.64  
% 3.90/1.64  Timing (in seconds)
% 3.90/1.64  ----------------------
% 3.90/1.65  Preprocessing        : 0.32
% 3.90/1.65  Parsing              : 0.17
% 3.90/1.65  CNF conversion       : 0.02
% 3.90/1.65  Main loop            : 0.55
% 3.90/1.65  Inferencing          : 0.15
% 3.90/1.65  Reduction            : 0.11
% 3.90/1.65  Demodulation         : 0.07
% 3.90/1.65  BG Simplification    : 0.02
% 3.90/1.65  Subsumption          : 0.24
% 3.90/1.65  Abstraction          : 0.03
% 3.90/1.65  MUC search           : 0.00
% 3.90/1.65  Cooper               : 0.00
% 3.90/1.65  Total                : 0.88
% 3.90/1.65  Index Insertion      : 0.00
% 3.90/1.65  Index Deletion       : 0.00
% 3.90/1.65  Index Matching       : 0.00
% 3.90/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
