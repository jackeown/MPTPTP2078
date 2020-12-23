%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:21 EST 2020

% Result     : CounterSatisfiable 2.31s
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
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:34:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.31/1.34  
% 2.31/1.34  % SZS status CounterSatisfiable for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.31/1.34  
% 2.31/1.34  Inference rules
% 2.31/1.34  ----------------------
% 2.31/1.34  #Ref     : 0
% 2.31/1.34  #Sup     : 152
% 2.31/1.34  #Fact    : 0
% 2.31/1.34  #Define  : 0
% 2.31/1.34  #Split   : 1
% 2.31/1.34  #Chain   : 0
% 2.31/1.34  #Close   : 0
% 2.31/1.34  
% 2.31/1.34  Ordering : KBO
% 2.31/1.34  
% 2.31/1.34  Simplification rules
% 2.31/1.34  ----------------------
% 2.31/1.34  #Subsume      : 25
% 2.31/1.34  #Demod        : 98
% 2.31/1.34  #Tautology    : 110
% 2.31/1.34  #SimpNegUnit  : 0
% 2.31/1.34  #BackRed      : 8
% 2.31/1.34  
% 2.31/1.34  #Partial instantiations: 0
% 2.31/1.34  #Strategies tried      : 1
% 2.31/1.34  
% 2.31/1.34  Timing (in seconds)
% 2.31/1.34  ----------------------
% 2.31/1.34  Preprocessing        : 0.31
% 2.31/1.34  Parsing              : 0.16
% 2.31/1.34  CNF conversion       : 0.02
% 2.31/1.34  Main loop            : 0.28
% 2.31/1.34  Inferencing          : 0.10
% 2.31/1.34  Reduction            : 0.11
% 2.31/1.34  Demodulation         : 0.09
% 2.31/1.34  BG Simplification    : 0.01
% 2.31/1.34  Subsumption          : 0.05
% 2.31/1.34  Abstraction          : 0.02
% 2.31/1.34  MUC search           : 0.00
% 2.31/1.34  Cooper               : 0.00
% 2.31/1.34  Total                : 0.60
% 2.31/1.34  Index Insertion      : 0.00
% 2.31/1.34  Index Deletion       : 0.00
% 2.31/1.34  Index Matching       : 0.00
% 2.31/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
