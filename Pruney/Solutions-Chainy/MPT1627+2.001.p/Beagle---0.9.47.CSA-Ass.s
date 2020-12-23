%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:45 EST 2020

% Result     : CounterSatisfiable 1.67s
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
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:58:50 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.67/1.11  
% 1.67/1.11  % SZS status CounterSatisfiable for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.67/1.11  
% 1.67/1.11  Inference rules
% 1.67/1.11  ----------------------
% 1.67/1.11  #Ref     : 0
% 1.67/1.11  #Sup     : 0
% 1.67/1.11  #Fact    : 0
% 1.67/1.11  #Define  : 0
% 1.67/1.11  #Split   : 1
% 1.67/1.11  #Chain   : 0
% 1.67/1.11  #Close   : 0
% 1.67/1.11  
% 1.67/1.11  Ordering : KBO
% 1.67/1.11  
% 1.67/1.11  Simplification rules
% 1.67/1.11  ----------------------
% 1.67/1.11  #Subsume      : 0
% 1.67/1.11  #Demod        : 0
% 1.67/1.11  #Tautology    : 0
% 1.67/1.11  #SimpNegUnit  : 0
% 1.67/1.11  #BackRed      : 0
% 1.67/1.11  
% 1.67/1.11  #Partial instantiations: 0
% 1.67/1.11  #Strategies tried      : 1
% 1.67/1.11  
% 1.67/1.11  Timing (in seconds)
% 1.67/1.11  ----------------------
% 1.67/1.11  Preprocessing        : 0.29
% 1.67/1.11  Parsing              : 0.15
% 1.67/1.11  CNF conversion       : 0.02
% 1.67/1.11  Main loop            : 0.08
% 1.67/1.11  Inferencing          : 0.03
% 1.67/1.11  Reduction            : 0.02
% 1.67/1.11  Demodulation         : 0.02
% 1.67/1.11  BG Simplification    : 0.01
% 1.67/1.11  Subsumption          : 0.01
% 1.67/1.11  Abstraction          : 0.00
% 1.67/1.11  MUC search           : 0.00
% 1.67/1.11  Cooper               : 0.00
% 1.67/1.11  Total                : 0.38
% 1.67/1.11  Index Insertion      : 0.00
% 1.67/1.11  Index Deletion       : 0.00
% 1.67/1.11  Index Matching       : 0.00
% 1.67/1.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
