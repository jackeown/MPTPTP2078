%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:23 EST 2020

% Result     : CounterSatisfiable 3.24s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:08:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.24/1.55  
% 3.24/1.55  % SZS status CounterSatisfiable for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.24/1.55  
% 3.24/1.55  Inference rules
% 3.24/1.55  ----------------------
% 3.24/1.55  #Ref     : 0
% 3.24/1.55  #Sup     : 461
% 3.24/1.55  #Fact    : 0
% 3.24/1.55  #Define  : 0
% 3.24/1.55  #Split   : 1
% 3.24/1.55  #Chain   : 0
% 3.24/1.55  #Close   : 0
% 3.24/1.55  
% 3.24/1.55  Ordering : KBO
% 3.24/1.55  
% 3.24/1.55  Simplification rules
% 3.24/1.55  ----------------------
% 3.24/1.55  #Subsume      : 177
% 3.24/1.55  #Demod        : 298
% 3.24/1.55  #Tautology    : 229
% 3.24/1.55  #SimpNegUnit  : 25
% 3.24/1.55  #BackRed      : 15
% 3.24/1.55  
% 3.24/1.55  #Partial instantiations: 0
% 3.24/1.55  #Strategies tried      : 1
% 3.24/1.55  
% 3.24/1.55  Timing (in seconds)
% 3.24/1.55  ----------------------
% 3.24/1.56  Preprocessing        : 0.31
% 3.24/1.56  Parsing              : 0.17
% 3.24/1.56  CNF conversion       : 0.02
% 3.24/1.56  Main loop            : 0.50
% 3.24/1.56  Inferencing          : 0.18
% 3.24/1.56  Reduction            : 0.19
% 3.24/1.56  Demodulation         : 0.15
% 3.24/1.56  BG Simplification    : 0.02
% 3.24/1.56  Subsumption          : 0.08
% 3.24/1.56  Abstraction          : 0.03
% 3.24/1.56  MUC search           : 0.00
% 3.24/1.56  Cooper               : 0.00
% 3.24/1.56  Total                : 0.82
% 3.24/1.56  Index Insertion      : 0.00
% 3.24/1.56  Index Deletion       : 0.00
% 3.24/1.56  Index Matching       : 0.00
% 3.24/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
