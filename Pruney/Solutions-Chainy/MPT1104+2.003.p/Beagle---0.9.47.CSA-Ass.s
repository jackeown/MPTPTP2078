%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:44 EST 2020

% Result     : CounterSatisfiable 4.21s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:16:54 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.21/1.76  
% 4.21/1.76  % SZS status CounterSatisfiable for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.21/1.76  
% 4.21/1.76  Inference rules
% 4.21/1.76  ----------------------
% 4.21/1.76  #Ref     : 0
% 4.21/1.76  #Sup     : 784
% 4.21/1.76  #Fact    : 0
% 4.21/1.76  #Define  : 0
% 4.21/1.76  #Split   : 0
% 4.21/1.76  #Chain   : 0
% 4.21/1.76  #Close   : 0
% 4.21/1.76  
% 4.21/1.76  Ordering : KBO
% 4.21/1.76  
% 4.21/1.76  Simplification rules
% 4.21/1.76  ----------------------
% 4.21/1.76  #Subsume      : 59
% 4.21/1.76  #Demod        : 1187
% 4.21/1.76  #Tautology    : 670
% 4.21/1.76  #SimpNegUnit  : 0
% 4.21/1.76  #BackRed      : 4
% 4.21/1.76  
% 4.21/1.76  #Partial instantiations: 0
% 4.21/1.76  #Strategies tried      : 1
% 4.21/1.76  
% 4.21/1.76  Timing (in seconds)
% 4.21/1.76  ----------------------
% 4.21/1.76  Preprocessing        : 0.31
% 4.21/1.76  Parsing              : 0.18
% 4.21/1.76  CNF conversion       : 0.02
% 4.21/1.77  Main loop            : 0.65
% 4.21/1.77  Inferencing          : 0.19
% 4.21/1.77  Reduction            : 0.34
% 4.21/1.77  Demodulation         : 0.30
% 4.21/1.77  BG Simplification    : 0.02
% 4.21/1.77  Subsumption          : 0.07
% 4.21/1.77  Abstraction          : 0.03
% 4.21/1.77  MUC search           : 0.00
% 4.21/1.77  Cooper               : 0.00
% 4.21/1.77  Total                : 0.97
% 4.21/1.77  Index Insertion      : 0.00
% 4.21/1.77  Index Deletion       : 0.00
% 4.21/1.77  Index Matching       : 0.00
% 4.21/1.77  BG Taut test         : 0.00
%------------------------------------------------------------------------------
