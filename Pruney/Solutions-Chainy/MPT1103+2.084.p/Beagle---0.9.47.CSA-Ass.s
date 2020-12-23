%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:40 EST 2020

% Result     : CounterSatisfiable 2.59s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:46:26 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.59/1.49  
% 2.59/1.49  % SZS status CounterSatisfiable for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.59/1.49  
% 2.59/1.49  Inference rules
% 2.59/1.49  ----------------------
% 2.59/1.49  #Ref     : 0
% 2.59/1.49  #Sup     : 145
% 2.59/1.49  #Fact    : 0
% 2.59/1.49  #Define  : 0
% 2.59/1.49  #Split   : 1
% 2.59/1.49  #Chain   : 0
% 2.59/1.49  #Close   : 0
% 2.59/1.49  
% 2.59/1.49  Ordering : KBO
% 2.59/1.49  
% 2.59/1.49  Simplification rules
% 2.59/1.49  ----------------------
% 2.59/1.49  #Subsume      : 1
% 2.59/1.49  #Demod        : 48
% 2.59/1.49  #Tautology    : 122
% 2.59/1.49  #SimpNegUnit  : 0
% 2.59/1.49  #BackRed      : 6
% 2.59/1.49  
% 2.59/1.49  #Partial instantiations: 0
% 2.59/1.49  #Strategies tried      : 1
% 2.59/1.49  
% 2.59/1.49  Timing (in seconds)
% 2.59/1.49  ----------------------
% 2.59/1.49  Preprocessing        : 0.36
% 2.59/1.49  Parsing              : 0.21
% 2.59/1.49  CNF conversion       : 0.02
% 2.59/1.49  Main loop            : 0.27
% 2.59/1.49  Inferencing          : 0.11
% 2.59/1.49  Reduction            : 0.08
% 2.59/1.49  Demodulation         : 0.06
% 2.59/1.49  BG Simplification    : 0.02
% 2.59/1.49  Subsumption          : 0.04
% 2.59/1.49  Abstraction          : 0.02
% 2.59/1.49  MUC search           : 0.00
% 2.59/1.49  Cooper               : 0.00
% 2.59/1.49  Total                : 0.64
% 2.59/1.49  Index Insertion      : 0.00
% 2.59/1.49  Index Deletion       : 0.00
% 2.59/1.49  Index Matching       : 0.00
% 2.59/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
