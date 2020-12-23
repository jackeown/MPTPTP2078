%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:03 EST 2020

% Result     : CounterSatisfiable 2.01s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:06:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.01/1.21  
% 2.01/1.21  % SZS status CounterSatisfiable for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.01/1.21  
% 2.01/1.21  Inference rules
% 2.01/1.21  ----------------------
% 2.01/1.21  #Ref     : 0
% 2.01/1.21  #Sup     : 7
% 2.01/1.21  #Fact    : 2
% 2.01/1.21  #Define  : 0
% 2.01/1.21  #Split   : 1
% 2.01/1.21  #Chain   : 0
% 2.01/1.21  #Close   : 0
% 2.01/1.21  
% 2.01/1.21  Ordering : KBO
% 2.01/1.21  
% 2.01/1.21  Simplification rules
% 2.01/1.21  ----------------------
% 2.01/1.21  #Subsume      : 1
% 2.01/1.21  #Demod        : 2
% 2.01/1.21  #Tautology    : 10
% 2.01/1.21  #SimpNegUnit  : 3
% 2.01/1.21  #BackRed      : 0
% 2.01/1.21  
% 2.01/1.21  #Partial instantiations: 0
% 2.01/1.21  #Strategies tried      : 1
% 2.01/1.21  
% 2.01/1.21  Timing (in seconds)
% 2.01/1.21  ----------------------
% 2.01/1.21  Preprocessing        : 0.29
% 2.01/1.21  Parsing              : 0.15
% 2.01/1.22  CNF conversion       : 0.03
% 2.01/1.22  Main loop            : 0.16
% 2.01/1.22  Inferencing          : 0.07
% 2.01/1.22  Reduction            : 0.05
% 2.01/1.22  Demodulation         : 0.03
% 2.01/1.22  BG Simplification    : 0.01
% 2.01/1.22  Subsumption          : 0.02
% 2.01/1.22  Abstraction          : 0.01
% 2.01/1.22  MUC search           : 0.00
% 2.01/1.22  Cooper               : 0.00
% 2.01/1.22  Total                : 0.46
% 2.01/1.22  Index Insertion      : 0.00
% 2.01/1.22  Index Deletion       : 0.00
% 2.01/1.22  Index Matching       : 0.00
% 2.01/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
