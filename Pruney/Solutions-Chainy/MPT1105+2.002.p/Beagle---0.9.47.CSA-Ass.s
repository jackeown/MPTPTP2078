%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:53 EST 2020

% Result     : CounterSatisfiable 1.76s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:16:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.76/1.30  
% 1.76/1.30  % SZS status CounterSatisfiable for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.76/1.30  
% 1.76/1.31  Inference rules
% 1.76/1.31  ----------------------
% 1.76/1.31  #Ref     : 0
% 1.76/1.31  #Sup     : 6
% 1.85/1.31  #Fact    : 0
% 1.85/1.31  #Define  : 0
% 1.85/1.31  #Split   : 0
% 1.85/1.31  #Chain   : 0
% 1.85/1.31  #Close   : 0
% 1.85/1.31  
% 1.85/1.31  Ordering : KBO
% 1.85/1.31  
% 1.85/1.31  Simplification rules
% 1.85/1.31  ----------------------
% 1.85/1.31  #Subsume      : 0
% 1.85/1.31  #Demod        : 2
% 1.85/1.31  #Tautology    : 6
% 1.85/1.31  #SimpNegUnit  : 0
% 1.85/1.31  #BackRed      : 0
% 1.85/1.31  
% 1.85/1.31  #Partial instantiations: 0
% 1.85/1.31  #Strategies tried      : 1
% 1.85/1.31  
% 1.85/1.31  Timing (in seconds)
% 1.85/1.31  ----------------------
% 1.85/1.31  Preprocessing        : 0.38
% 1.85/1.31  Parsing              : 0.21
% 1.85/1.31  CNF conversion       : 0.02
% 1.85/1.31  Main loop            : 0.10
% 1.85/1.31  Inferencing          : 0.04
% 1.85/1.31  Reduction            : 0.03
% 1.85/1.31  Demodulation         : 0.03
% 1.85/1.31  BG Simplification    : 0.01
% 1.85/1.31  Subsumption          : 0.01
% 1.85/1.31  Abstraction          : 0.01
% 1.85/1.31  MUC search           : 0.00
% 1.85/1.31  Cooper               : 0.00
% 1.85/1.31  Total                : 0.50
% 1.85/1.31  Index Insertion      : 0.00
% 1.85/1.31  Index Deletion       : 0.00
% 1.85/1.31  Index Matching       : 0.00
% 1.85/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
