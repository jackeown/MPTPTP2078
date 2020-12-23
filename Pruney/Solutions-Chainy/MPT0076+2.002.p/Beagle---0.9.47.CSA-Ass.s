%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:32 EST 2020

% Result     : CounterSatisfiable 3.98s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:58:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.98/1.77  
% 3.98/1.77  % SZS status CounterSatisfiable for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.98/1.77  
% 3.98/1.77  Inference rules
% 3.98/1.77  ----------------------
% 3.98/1.77  #Ref     : 0
% 3.98/1.77  #Sup     : 642
% 3.98/1.77  #Fact    : 0
% 3.98/1.77  #Define  : 0
% 3.98/1.77  #Split   : 2
% 3.98/1.77  #Chain   : 0
% 3.98/1.77  #Close   : 0
% 3.98/1.77  
% 3.98/1.77  Ordering : KBO
% 3.98/1.77  
% 3.98/1.77  Simplification rules
% 3.98/1.77  ----------------------
% 3.98/1.77  #Subsume      : 318
% 3.98/1.77  #Demod        : 317
% 3.98/1.77  #Tautology    : 217
% 3.98/1.77  #SimpNegUnit  : 8
% 3.98/1.77  #BackRed      : 0
% 3.98/1.77  
% 3.98/1.77  #Partial instantiations: 0
% 3.98/1.77  #Strategies tried      : 1
% 3.98/1.77  
% 3.98/1.77  Timing (in seconds)
% 3.98/1.77  ----------------------
% 3.98/1.78  Preprocessing        : 0.30
% 3.98/1.78  Parsing              : 0.17
% 3.98/1.78  CNF conversion       : 0.02
% 3.98/1.78  Main loop            : 0.73
% 3.98/1.78  Inferencing          : 0.26
% 3.98/1.78  Reduction            : 0.20
% 3.98/1.78  Demodulation         : 0.13
% 3.98/1.78  BG Simplification    : 0.02
% 3.98/1.78  Subsumption          : 0.21
% 3.98/1.78  Abstraction          : 0.03
% 3.98/1.78  MUC search           : 0.00
% 3.98/1.78  Cooper               : 0.00
% 3.98/1.78  Total                : 1.03
% 3.98/1.78  Index Insertion      : 0.00
% 3.98/1.78  Index Deletion       : 0.00
% 3.98/1.78  Index Matching       : 0.00
% 3.98/1.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
