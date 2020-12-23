%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:12 EST 2020

% Result     : CounterSatisfiable 4.41s
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
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:19:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.41/2.20  
% 4.41/2.20  % SZS status CounterSatisfiable for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.41/2.20  
% 4.41/2.20  Inference rules
% 4.41/2.20  ----------------------
% 4.41/2.20  #Ref     : 0
% 4.41/2.20  #Sup     : 130
% 4.41/2.20  #Fact    : 0
% 4.41/2.20  #Define  : 0
% 4.41/2.20  #Split   : 1
% 4.41/2.20  #Chain   : 0
% 4.41/2.20  #Close   : 0
% 4.41/2.20  
% 4.41/2.20  Ordering : KBO
% 4.41/2.20  
% 4.41/2.20  Simplification rules
% 4.41/2.20  ----------------------
% 4.41/2.20  #Subsume      : 18
% 4.41/2.20  #Demod        : 0
% 4.41/2.20  #Tautology    : 59
% 4.41/2.20  #SimpNegUnit  : 0
% 4.41/2.20  #BackRed      : 0
% 4.41/2.20  
% 4.41/2.20  #Partial instantiations: 0
% 4.41/2.20  #Strategies tried      : 1
% 4.41/2.20  
% 4.41/2.20  Timing (in seconds)
% 4.41/2.20  ----------------------
% 4.41/2.21  Preprocessing        : 0.46
% 4.41/2.21  Parsing              : 0.25
% 4.41/2.21  CNF conversion       : 0.04
% 4.41/2.21  Main loop            : 0.82
% 4.41/2.21  Inferencing          : 0.34
% 4.41/2.21  Reduction            : 0.16
% 4.41/2.21  Demodulation         : 0.09
% 4.41/2.21  BG Simplification    : 0.04
% 4.41/2.21  Subsumption          : 0.22
% 4.41/2.21  Abstraction          : 0.03
% 4.41/2.21  MUC search           : 0.00
% 4.41/2.21  Cooper               : 0.00
% 4.41/2.21  Total                : 1.30
% 4.41/2.21  Index Insertion      : 0.00
% 4.41/2.21  Index Deletion       : 0.00
% 4.41/2.21  Index Matching       : 0.00
% 4.41/2.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
