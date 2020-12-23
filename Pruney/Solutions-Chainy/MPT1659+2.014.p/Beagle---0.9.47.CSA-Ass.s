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
% DateTime   : Thu Dec  3 10:25:59 EST 2020

% Result     : CounterSatisfiable 2.08s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:26:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.08/1.32  
% 2.08/1.32  % SZS status CounterSatisfiable for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.32  
% 2.08/1.32  Inference rules
% 2.08/1.32  ----------------------
% 2.08/1.32  #Ref     : 0
% 2.08/1.32  #Sup     : 17
% 2.08/1.32  #Fact    : 0
% 2.08/1.32  #Define  : 0
% 2.08/1.32  #Split   : 1
% 2.08/1.32  #Chain   : 0
% 2.08/1.32  #Close   : 0
% 2.08/1.32  
% 2.08/1.32  Ordering : KBO
% 2.08/1.32  
% 2.08/1.32  Simplification rules
% 2.08/1.32  ----------------------
% 2.08/1.32  #Subsume      : 6
% 2.08/1.32  #Demod        : 2
% 2.08/1.32  #Tautology    : 1
% 2.08/1.32  #SimpNegUnit  : 1
% 2.08/1.32  #BackRed      : 0
% 2.08/1.32  
% 2.08/1.32  #Partial instantiations: 0
% 2.08/1.32  #Strategies tried      : 1
% 2.08/1.32  
% 2.08/1.32  Timing (in seconds)
% 2.08/1.32  ----------------------
% 2.38/1.32  Preprocessing        : 0.31
% 2.38/1.32  Parsing              : 0.17
% 2.38/1.32  CNF conversion       : 0.02
% 2.38/1.32  Main loop            : 0.21
% 2.38/1.32  Inferencing          : 0.09
% 2.38/1.32  Reduction            : 0.05
% 2.38/1.32  Demodulation         : 0.03
% 2.38/1.32  BG Simplification    : 0.01
% 2.38/1.32  Subsumption          : 0.04
% 2.38/1.32  Abstraction          : 0.01
% 2.38/1.32  MUC search           : 0.00
% 2.38/1.32  Cooper               : 0.00
% 2.38/1.32  Total                : 0.53
% 2.38/1.32  Index Insertion      : 0.00
% 2.38/1.32  Index Deletion       : 0.00
% 2.38/1.32  Index Matching       : 0.00
% 2.38/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
