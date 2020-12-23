%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:58 EST 2020

% Result     : CounterSatisfiable 17.31s
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
% 0.13/0.33  % Computer   : n002.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 09:24:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 17.31/10.03  
% 17.31/10.03  % SZS status CounterSatisfiable for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 17.31/10.03  
% 17.31/10.03  Inference rules
% 17.31/10.03  ----------------------
% 17.31/10.03  #Ref     : 0
% 17.31/10.03  #Sup     : 18649
% 17.31/10.03  #Fact    : 11
% 17.31/10.03  #Define  : 0
% 17.31/10.03  #Split   : 2
% 17.31/10.03  #Chain   : 0
% 17.31/10.03  #Close   : 0
% 17.31/10.03  
% 17.31/10.03  Ordering : KBO
% 17.31/10.03  
% 17.31/10.03  Simplification rules
% 17.31/10.03  ----------------------
% 17.31/10.03  #Subsume      : 11155
% 17.31/10.04  #Demod        : 12024
% 17.31/10.04  #Tautology    : 7064
% 17.31/10.04  #SimpNegUnit  : 87
% 17.31/10.04  #BackRed      : 6
% 17.31/10.04  
% 17.31/10.04  #Partial instantiations: 0
% 17.31/10.04  #Strategies tried      : 1
% 17.31/10.04  
% 17.31/10.04  Timing (in seconds)
% 17.31/10.04  ----------------------
% 17.31/10.04  Preprocessing        : 0.32
% 17.31/10.04  Parsing              : 0.17
% 17.31/10.04  CNF conversion       : 0.02
% 17.31/10.04  Main loop            : 8.98
% 17.31/10.04  Inferencing          : 1.69
% 17.31/10.04  Reduction            : 3.30
% 17.31/10.04  Demodulation         : 2.72
% 17.31/10.04  BG Simplification    : 0.13
% 17.31/10.04  Subsumption          : 3.58
% 17.31/10.04  Abstraction          : 0.27
% 17.31/10.04  MUC search           : 0.00
% 17.31/10.04  Cooper               : 0.00
% 17.31/10.04  Total                : 9.31
% 17.31/10.04  Index Insertion      : 0.00
% 17.31/10.04  Index Deletion       : 0.00
% 17.31/10.04  Index Matching       : 0.00
% 17.31/10.04  BG Taut test         : 0.00
%------------------------------------------------------------------------------
