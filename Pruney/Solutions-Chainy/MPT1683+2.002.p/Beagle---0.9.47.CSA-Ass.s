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
% DateTime   : Thu Dec  3 10:26:03 EST 2020

% Result     : CounterSatisfiable 3.18s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:45:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.18/1.56  
% 3.18/1.56  % SZS status CounterSatisfiable for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.18/1.56  
% 3.18/1.56  Inference rules
% 3.18/1.56  ----------------------
% 3.18/1.56  #Ref     : 0
% 3.18/1.56  #Sup     : 57
% 3.18/1.56  #Fact    : 0
% 3.18/1.56  #Define  : 0
% 3.18/1.56  #Split   : 2
% 3.18/1.56  #Chain   : 0
% 3.18/1.56  #Close   : 0
% 3.18/1.56  
% 3.18/1.56  Ordering : KBO
% 3.18/1.56  
% 3.18/1.56  Simplification rules
% 3.18/1.56  ----------------------
% 3.18/1.56  #Subsume      : 4
% 3.18/1.56  #Demod        : 5
% 3.18/1.56  #Tautology    : 35
% 3.18/1.56  #SimpNegUnit  : 1
% 3.18/1.56  #BackRed      : 0
% 3.18/1.56  
% 3.18/1.56  #Partial instantiations: 0
% 3.18/1.56  #Strategies tried      : 1
% 3.18/1.56  
% 3.18/1.56  Timing (in seconds)
% 3.18/1.56  ----------------------
% 3.18/1.56  Preprocessing        : 0.37
% 3.18/1.56  Parsing              : 0.19
% 3.18/1.56  CNF conversion       : 0.03
% 3.18/1.56  Main loop            : 0.39
% 3.18/1.56  Inferencing          : 0.16
% 3.18/1.56  Reduction            : 0.09
% 3.18/1.56  Demodulation         : 0.06
% 3.18/1.56  BG Simplification    : 0.03
% 3.18/1.56  Subsumption          : 0.09
% 3.18/1.56  Abstraction          : 0.02
% 3.18/1.56  MUC search           : 0.00
% 3.18/1.56  Cooper               : 0.00
% 3.18/1.56  Total                : 0.76
% 3.18/1.56  Index Insertion      : 0.00
% 3.18/1.56  Index Deletion       : 0.00
% 3.18/1.56  Index Matching       : 0.00
% 3.18/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
