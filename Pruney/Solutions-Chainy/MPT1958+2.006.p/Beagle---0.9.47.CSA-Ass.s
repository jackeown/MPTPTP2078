%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:57 EST 2020

% Result     : CounterSatisfiable 2.01s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:46:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.01/1.19  
% 2.01/1.19  % SZS status CounterSatisfiable for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.01/1.19  
% 2.01/1.19  Inference rules
% 2.01/1.19  ----------------------
% 2.01/1.19  #Ref     : 0
% 2.01/1.19  #Sup     : 27
% 2.01/1.19  #Fact    : 0
% 2.01/1.19  #Define  : 0
% 2.01/1.19  #Split   : 1
% 2.01/1.19  #Chain   : 0
% 2.01/1.19  #Close   : 0
% 2.01/1.19  
% 2.01/1.19  Ordering : KBO
% 2.01/1.19  
% 2.01/1.19  Simplification rules
% 2.01/1.19  ----------------------
% 2.01/1.19  #Subsume      : 3
% 2.01/1.19  #Demod        : 45
% 2.01/1.19  #Tautology    : 18
% 2.01/1.19  #SimpNegUnit  : 7
% 2.01/1.19  #BackRed      : 0
% 2.01/1.19  
% 2.01/1.19  #Partial instantiations: 0
% 2.01/1.19  #Strategies tried      : 1
% 2.01/1.19  
% 2.01/1.19  Timing (in seconds)
% 2.01/1.19  ----------------------
% 2.01/1.19  Preprocessing        : 0.30
% 2.01/1.19  Parsing              : 0.16
% 2.01/1.19  CNF conversion       : 0.02
% 2.01/1.19  Main loop            : 0.16
% 2.01/1.19  Inferencing          : 0.07
% 2.01/1.19  Reduction            : 0.04
% 2.01/1.19  Demodulation         : 0.03
% 2.01/1.19  BG Simplification    : 0.01
% 2.01/1.19  Subsumption          : 0.02
% 2.01/1.19  Abstraction          : 0.01
% 2.01/1.19  MUC search           : 0.00
% 2.01/1.19  Cooper               : 0.00
% 2.01/1.19  Total                : 0.46
% 2.01/1.19  Index Insertion      : 0.00
% 2.01/1.19  Index Deletion       : 0.00
% 2.01/1.19  Index Matching       : 0.00
% 2.01/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
