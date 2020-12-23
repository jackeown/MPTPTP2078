%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:32 EST 2020

% Result     : CounterSatisfiable 4.49s
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
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:21:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.49/1.87  
% 4.49/1.87  % SZS status CounterSatisfiable for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.49/1.87  
% 4.49/1.87  Inference rules
% 4.49/1.87  ----------------------
% 4.49/1.87  #Ref     : 0
% 4.49/1.87  #Sup     : 736
% 4.49/1.87  #Fact    : 0
% 4.49/1.87  #Define  : 0
% 4.49/1.87  #Split   : 0
% 4.49/1.87  #Chain   : 0
% 4.49/1.87  #Close   : 0
% 4.49/1.87  
% 4.49/1.87  Ordering : KBO
% 4.49/1.87  
% 4.49/1.87  Simplification rules
% 4.49/1.87  ----------------------
% 4.49/1.87  #Subsume      : 0
% 4.49/1.87  #Demod        : 2268
% 4.49/1.87  #Tautology    : 713
% 4.49/1.87  #SimpNegUnit  : 0
% 4.49/1.87  #BackRed      : 21
% 4.49/1.87  
% 4.49/1.87  #Partial instantiations: 0
% 4.49/1.87  #Strategies tried      : 1
% 4.49/1.87  
% 4.49/1.87  Timing (in seconds)
% 4.49/1.87  ----------------------
% 4.49/1.87  Preprocessing        : 0.27
% 4.49/1.87  Parsing              : 0.15
% 4.49/1.87  CNF conversion       : 0.02
% 4.49/1.87  Main loop            : 0.78
% 4.49/1.87  Inferencing          : 0.24
% 4.49/1.87  Reduction            : 0.39
% 4.49/1.87  Demodulation         : 0.34
% 4.49/1.87  BG Simplification    : 0.03
% 4.49/1.87  Subsumption          : 0.08
% 4.49/1.87  Abstraction          : 0.06
% 4.49/1.87  MUC search           : 0.00
% 4.49/1.87  Cooper               : 0.00
% 4.49/1.87  Total                : 1.06
% 4.49/1.87  Index Insertion      : 0.00
% 4.49/1.87  Index Deletion       : 0.00
% 4.49/1.87  Index Matching       : 0.00
% 4.49/1.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
