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
% DateTime   : Thu Dec  3 10:18:49 EST 2020

% Result     : CounterSatisfiable 2.07s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:17:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.07/1.40  
% 2.07/1.40  % SZS status CounterSatisfiable for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.07/1.40  
% 2.07/1.40  Inference rules
% 2.07/1.40  ----------------------
% 2.07/1.40  #Ref     : 0
% 2.07/1.40  #Sup     : 91
% 2.07/1.40  #Fact    : 0
% 2.07/1.40  #Define  : 0
% 2.07/1.40  #Split   : 0
% 2.07/1.40  #Chain   : 0
% 2.07/1.40  #Close   : 0
% 2.07/1.40  
% 2.07/1.40  Ordering : KBO
% 2.07/1.40  
% 2.07/1.40  Simplification rules
% 2.07/1.40  ----------------------
% 2.07/1.40  #Subsume      : 10
% 2.07/1.40  #Demod        : 12
% 2.07/1.40  #Tautology    : 60
% 2.07/1.40  #SimpNegUnit  : 0
% 2.07/1.40  #BackRed      : 1
% 2.07/1.40  
% 2.07/1.40  #Partial instantiations: 0
% 2.07/1.40  #Strategies tried      : 1
% 2.07/1.40  
% 2.07/1.40  Timing (in seconds)
% 2.07/1.40  ----------------------
% 2.07/1.40  Preprocessing        : 0.30
% 2.07/1.40  Parsing              : 0.15
% 2.07/1.40  CNF conversion       : 0.02
% 2.07/1.40  Main loop            : 0.22
% 2.07/1.40  Inferencing          : 0.08
% 2.07/1.40  Reduction            : 0.07
% 2.07/1.40  Demodulation         : 0.06
% 2.07/1.40  BG Simplification    : 0.01
% 2.07/1.40  Subsumption          : 0.04
% 2.07/1.40  Abstraction          : 0.01
% 2.07/1.40  MUC search           : 0.00
% 2.07/1.41  Cooper               : 0.00
% 2.07/1.41  Total                : 0.53
% 2.07/1.41  Index Insertion      : 0.00
% 2.07/1.41  Index Deletion       : 0.00
% 2.07/1.41  Index Matching       : 0.00
% 2.07/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
