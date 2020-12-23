%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:59 EST 2020

% Result     : CounterSatisfiable 1.76s
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
% 0.13/0.32  % Computer   : n025.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 19:23:06 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.13/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.76/1.32  
% 1.76/1.32  % SZS status CounterSatisfiable for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.76/1.32  
% 1.76/1.32  Inference rules
% 1.76/1.32  ----------------------
% 1.76/1.32  #Ref     : 0
% 1.76/1.32  #Sup     : 0
% 1.76/1.32  #Fact    : 0
% 1.76/1.32  #Define  : 0
% 1.76/1.32  #Split   : 0
% 1.76/1.32  #Chain   : 0
% 1.76/1.32  #Close   : 0
% 1.76/1.32  
% 1.76/1.32  Ordering : KBO
% 1.76/1.32  
% 1.76/1.32  Simplification rules
% 1.76/1.32  ----------------------
% 1.76/1.32  #Subsume      : 0
% 1.76/1.32  #Demod        : 0
% 1.76/1.32  #Tautology    : 0
% 1.76/1.32  #SimpNegUnit  : 0
% 1.76/1.32  #BackRed      : 0
% 1.76/1.32  
% 1.76/1.32  #Partial instantiations: 0
% 1.76/1.32  #Strategies tried      : 1
% 1.76/1.32  
% 1.76/1.32  Timing (in seconds)
% 1.76/1.32  ----------------------
% 1.76/1.32  Preprocessing        : 0.38
% 1.76/1.33  Parsing              : 0.20
% 1.76/1.33  CNF conversion       : 0.03
% 1.76/1.33  Main loop            : 0.08
% 1.76/1.33  Inferencing          : 0.03
% 1.76/1.33  Reduction            : 0.02
% 1.76/1.33  Demodulation         : 0.01
% 1.76/1.33  BG Simplification    : 0.01
% 1.76/1.33  Subsumption          : 0.01
% 1.76/1.33  Abstraction          : 0.00
% 1.76/1.33  MUC search           : 0.00
% 1.76/1.33  Cooper               : 0.00
% 1.76/1.33  Total                : 0.47
% 1.76/1.33  Index Insertion      : 0.00
% 1.76/1.33  Index Deletion       : 0.00
% 1.76/1.33  Index Matching       : 0.00
% 1.76/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
