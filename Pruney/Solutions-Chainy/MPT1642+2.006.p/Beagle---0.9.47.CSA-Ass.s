%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:51 EST 2020

% Result     : CounterSatisfiable 2.66s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n023.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 11:53:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.66/1.71  
% 2.66/1.71  % SZS status CounterSatisfiable for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.66/1.71  
% 2.66/1.71  Inference rules
% 2.66/1.71  ----------------------
% 2.66/1.71  #Ref     : 0
% 2.66/1.71  #Sup     : 27
% 2.66/1.71  #Fact    : 0
% 2.66/1.71  #Define  : 0
% 2.66/1.71  #Split   : 1
% 2.66/1.71  #Chain   : 0
% 2.66/1.71  #Close   : 0
% 2.66/1.71  
% 2.66/1.71  Ordering : KBO
% 2.66/1.71  
% 2.66/1.71  Simplification rules
% 2.66/1.71  ----------------------
% 2.66/1.71  #Subsume      : 7
% 2.66/1.71  #Demod        : 30
% 2.66/1.71  #Tautology    : 5
% 2.66/1.71  #SimpNegUnit  : 0
% 2.66/1.71  #BackRed      : 0
% 2.66/1.71  
% 2.66/1.71  #Partial instantiations: 0
% 2.66/1.71  #Strategies tried      : 1
% 2.66/1.71  
% 2.66/1.71  Timing (in seconds)
% 2.66/1.71  ----------------------
% 2.66/1.72  Preprocessing        : 0.46
% 2.66/1.72  Parsing              : 0.26
% 2.66/1.72  CNF conversion       : 0.04
% 2.66/1.72  Main loop            : 0.36
% 2.66/1.72  Inferencing          : 0.15
% 2.66/1.72  Reduction            : 0.09
% 2.66/1.72  Demodulation         : 0.06
% 2.66/1.72  BG Simplification    : 0.03
% 2.66/1.72  Subsumption          : 0.08
% 2.66/1.72  Abstraction          : 0.01
% 2.66/1.72  MUC search           : 0.00
% 2.66/1.72  Cooper               : 0.00
% 2.66/1.72  Total                : 0.84
% 2.66/1.72  Index Insertion      : 0.00
% 2.66/1.72  Index Deletion       : 0.00
% 2.66/1.72  Index Matching       : 0.00
% 2.66/1.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
