%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:18 EST 2020

% Result     : CounterSatisfiable 1.77s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:55:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.77/1.19  
% 1.77/1.19  % SZS status CounterSatisfiable for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.77/1.19  
% 1.77/1.19  Inference rules
% 1.77/1.19  ----------------------
% 1.77/1.19  #Ref     : 0
% 1.77/1.19  #Sup     : 20
% 1.77/1.19  #Fact    : 0
% 1.77/1.19  #Define  : 0
% 1.77/1.19  #Split   : 1
% 1.77/1.19  #Chain   : 0
% 1.77/1.19  #Close   : 0
% 1.77/1.19  
% 1.77/1.19  Ordering : KBO
% 1.77/1.19  
% 1.77/1.19  Simplification rules
% 1.77/1.19  ----------------------
% 1.77/1.19  #Subsume      : 0
% 1.77/1.20  #Demod        : 3
% 1.77/1.20  #Tautology    : 17
% 1.77/1.20  #SimpNegUnit  : 0
% 1.77/1.20  #BackRed      : 1
% 1.77/1.20  
% 1.77/1.20  #Partial instantiations: 0
% 1.77/1.20  #Strategies tried      : 1
% 1.77/1.20  
% 1.77/1.20  Timing (in seconds)
% 1.77/1.20  ----------------------
% 1.77/1.20  Preprocessing        : 0.30
% 1.77/1.20  Parsing              : 0.16
% 1.77/1.20  CNF conversion       : 0.02
% 1.77/1.20  Main loop            : 0.12
% 1.77/1.20  Inferencing          : 0.04
% 1.77/1.20  Reduction            : 0.04
% 1.77/1.20  Demodulation         : 0.03
% 1.77/1.20  BG Simplification    : 0.01
% 1.77/1.20  Subsumption          : 0.02
% 1.77/1.20  Abstraction          : 0.01
% 1.77/1.20  MUC search           : 0.00
% 1.77/1.20  Cooper               : 0.00
% 1.77/1.20  Total                : 0.42
% 1.77/1.20  Index Insertion      : 0.00
% 1.77/1.20  Index Deletion       : 0.00
% 1.77/1.20  Index Matching       : 0.00
% 1.77/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
