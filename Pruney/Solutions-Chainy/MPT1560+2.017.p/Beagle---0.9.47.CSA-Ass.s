%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:06 EST 2020

% Result     : CounterSatisfiable 1.86s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:14:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.79/1.19  
% 1.86/1.19  % SZS status CounterSatisfiable for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.86/1.19  
% 1.86/1.19  Inference rules
% 1.86/1.19  ----------------------
% 1.86/1.19  #Ref     : 0
% 1.86/1.19  #Sup     : 8
% 1.86/1.19  #Fact    : 0
% 1.86/1.19  #Define  : 0
% 1.86/1.19  #Split   : 2
% 1.86/1.19  #Chain   : 0
% 1.86/1.19  #Close   : 0
% 1.86/1.19  
% 1.86/1.19  Ordering : KBO
% 1.86/1.19  
% 1.86/1.19  Simplification rules
% 1.86/1.19  ----------------------
% 1.86/1.19  #Subsume      : 0
% 1.86/1.19  #Demod        : 4
% 1.86/1.19  #Tautology    : 4
% 1.86/1.19  #SimpNegUnit  : 2
% 1.86/1.19  #BackRed      : 1
% 1.86/1.19  
% 1.86/1.19  #Partial instantiations: 0
% 1.86/1.19  #Strategies tried      : 1
% 1.86/1.19  
% 1.86/1.19  Timing (in seconds)
% 1.86/1.19  ----------------------
% 1.86/1.20  Preprocessing        : 0.30
% 1.86/1.20  Parsing              : 0.16
% 1.86/1.20  CNF conversion       : 0.02
% 1.86/1.20  Main loop            : 0.10
% 1.86/1.20  Inferencing          : 0.04
% 1.86/1.20  Reduction            : 0.03
% 1.86/1.20  Demodulation         : 0.02
% 1.86/1.20  BG Simplification    : 0.01
% 1.86/1.20  Subsumption          : 0.01
% 1.86/1.20  Abstraction          : 0.01
% 1.86/1.20  MUC search           : 0.00
% 1.86/1.20  Cooper               : 0.00
% 1.86/1.20  Total                : 0.40
% 1.86/1.20  Index Insertion      : 0.00
% 1.86/1.20  Index Deletion       : 0.00
% 1.86/1.20  Index Matching       : 0.00
% 1.86/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
