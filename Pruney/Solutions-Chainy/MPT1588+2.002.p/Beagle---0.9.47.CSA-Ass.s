%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:18 EST 2020

% Result     : CounterSatisfiable 3.08s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:52:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.08/1.49  
% 3.08/1.49  % SZS status CounterSatisfiable for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.08/1.49  
% 3.08/1.49  Inference rules
% 3.08/1.49  ----------------------
% 3.08/1.50  #Ref     : 0
% 3.08/1.50  #Sup     : 62
% 3.08/1.50  #Fact    : 0
% 3.08/1.50  #Define  : 0
% 3.08/1.50  #Split   : 1
% 3.08/1.50  #Chain   : 0
% 3.08/1.50  #Close   : 0
% 3.08/1.50  
% 3.08/1.50  Ordering : KBO
% 3.08/1.50  
% 3.08/1.50  Simplification rules
% 3.08/1.50  ----------------------
% 3.08/1.50  #Subsume      : 7
% 3.08/1.50  #Demod        : 9
% 3.08/1.50  #Tautology    : 35
% 3.08/1.50  #SimpNegUnit  : 2
% 3.08/1.50  #BackRed      : 3
% 3.08/1.50  
% 3.08/1.50  #Partial instantiations: 0
% 3.08/1.50  #Strategies tried      : 1
% 3.08/1.50  
% 3.08/1.50  Timing (in seconds)
% 3.08/1.50  ----------------------
% 3.08/1.50  Preprocessing        : 0.39
% 3.08/1.50  Parsing              : 0.19
% 3.08/1.50  CNF conversion       : 0.05
% 3.08/1.50  Main loop            : 0.28
% 3.08/1.50  Inferencing          : 0.13
% 3.08/1.50  Reduction            : 0.07
% 3.08/1.50  Demodulation         : 0.05
% 3.08/1.50  BG Simplification    : 0.02
% 3.08/1.50  Subsumption          : 0.04
% 3.08/1.50  Abstraction          : 0.02
% 3.08/1.50  MUC search           : 0.00
% 3.08/1.50  Cooper               : 0.00
% 3.08/1.50  Total                : 0.68
% 3.08/1.50  Index Insertion      : 0.00
% 3.08/1.50  Index Deletion       : 0.00
% 3.08/1.50  Index Matching       : 0.00
% 3.08/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
