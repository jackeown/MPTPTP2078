%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:06 EST 2020

% Result     : CounterSatisfiable 2.30s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:26:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.30/1.30  
% 2.30/1.30  % SZS status CounterSatisfiable for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.30/1.30  
% 2.30/1.30  Inference rules
% 2.30/1.30  ----------------------
% 2.30/1.30  #Ref     : 0
% 2.30/1.30  #Sup     : 62
% 2.30/1.30  #Fact    : 0
% 2.30/1.30  #Define  : 0
% 2.30/1.30  #Split   : 3
% 2.30/1.30  #Chain   : 0
% 2.30/1.30  #Close   : 0
% 2.30/1.30  
% 2.30/1.30  Ordering : KBO
% 2.30/1.30  
% 2.30/1.30  Simplification rules
% 2.30/1.30  ----------------------
% 2.30/1.30  #Subsume      : 4
% 2.30/1.30  #Demod        : 5
% 2.30/1.30  #Tautology    : 39
% 2.30/1.30  #SimpNegUnit  : 2
% 2.30/1.30  #BackRed      : 0
% 2.30/1.30  
% 2.30/1.30  #Partial instantiations: 0
% 2.30/1.30  #Strategies tried      : 1
% 2.30/1.30  
% 2.30/1.30  Timing (in seconds)
% 2.30/1.30  ----------------------
% 2.30/1.30  Preprocessing        : 0.31
% 2.30/1.30  Parsing              : 0.16
% 2.30/1.30  CNF conversion       : 0.02
% 2.30/1.30  Main loop            : 0.25
% 2.30/1.30  Inferencing          : 0.10
% 2.30/1.30  Reduction            : 0.07
% 2.30/1.30  Demodulation         : 0.05
% 2.30/1.30  BG Simplification    : 0.02
% 2.30/1.30  Subsumption          : 0.05
% 2.30/1.30  Abstraction          : 0.02
% 2.30/1.30  MUC search           : 0.00
% 2.30/1.30  Cooper               : 0.00
% 2.30/1.30  Total                : 0.57
% 2.30/1.30  Index Insertion      : 0.00
% 2.30/1.30  Index Deletion       : 0.00
% 2.30/1.30  Index Matching       : 0.00
% 2.30/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
