%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:02 EST 2020

% Result     : CounterSatisfiable 1.66s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:05:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.66/1.11  
% 1.66/1.11  % SZS status CounterSatisfiable for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.66/1.11  
% 1.66/1.11  Inference rules
% 1.66/1.11  ----------------------
% 1.66/1.11  #Ref     : 0
% 1.66/1.11  #Sup     : 8
% 1.66/1.11  #Fact    : 0
% 1.66/1.11  #Define  : 0
% 1.66/1.11  #Split   : 0
% 1.66/1.11  #Chain   : 0
% 1.66/1.11  #Close   : 0
% 1.66/1.11  
% 1.66/1.11  Ordering : KBO
% 1.66/1.11  
% 1.66/1.11  Simplification rules
% 1.66/1.11  ----------------------
% 1.66/1.11  #Subsume      : 2
% 1.66/1.11  #Demod        : 2
% 1.66/1.11  #Tautology    : 3
% 1.66/1.11  #SimpNegUnit  : 0
% 1.66/1.11  #BackRed      : 1
% 1.66/1.11  
% 1.66/1.11  #Partial instantiations: 0
% 1.66/1.11  #Strategies tried      : 1
% 1.66/1.11  
% 1.66/1.11  Timing (in seconds)
% 1.66/1.11  ----------------------
% 1.66/1.12  Preprocessing        : 0.26
% 1.66/1.12  Parsing              : 0.15
% 1.66/1.12  CNF conversion       : 0.02
% 1.66/1.12  Main loop            : 0.11
% 1.66/1.12  Inferencing          : 0.05
% 1.66/1.12  Reduction            : 0.02
% 1.66/1.12  Demodulation         : 0.02
% 1.66/1.12  BG Simplification    : 0.01
% 1.66/1.12  Subsumption          : 0.02
% 1.66/1.12  Abstraction          : 0.00
% 1.66/1.12  MUC search           : 0.00
% 1.66/1.12  Cooper               : 0.00
% 1.66/1.12  Total                : 0.38
% 1.66/1.12  Index Insertion      : 0.00
% 1.66/1.12  Index Deletion       : 0.00
% 1.66/1.12  Index Matching       : 0.00
% 1.66/1.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
