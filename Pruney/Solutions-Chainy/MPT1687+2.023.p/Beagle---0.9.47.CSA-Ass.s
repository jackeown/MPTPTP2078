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
% DateTime   : Thu Dec  3 10:26:05 EST 2020

% Result     : CounterSatisfiable 12.79s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:19:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.66/9.70  
% 12.79/9.71  % SZS status CounterSatisfiable for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.79/9.71  
% 12.79/9.71  Inference rules
% 12.79/9.71  ----------------------
% 12.79/9.71  #Ref     : 0
% 12.79/9.71  #Sup     : 79
% 12.79/9.71  #Fact    : 0
% 12.79/9.71  #Define  : 0
% 12.79/9.71  #Split   : 4
% 12.79/9.71  #Chain   : 0
% 12.79/9.71  #Close   : 0
% 12.79/9.71  
% 12.79/9.71  Ordering : KBO
% 12.79/9.71  
% 12.79/9.71  Simplification rules
% 12.79/9.71  ----------------------
% 12.79/9.71  #Subsume      : 25
% 12.79/9.71  #Demod        : 37
% 12.79/9.71  #Tautology    : 23
% 12.79/9.71  #SimpNegUnit  : 2
% 12.79/9.71  #BackRed      : 3
% 12.79/9.71  
% 12.79/9.71  #Partial instantiations: 0
% 12.79/9.71  #Strategies tried      : 1
% 12.79/9.71  
% 12.79/9.71  Timing (in seconds)
% 12.79/9.71  ----------------------
% 12.79/9.71  Preprocessing        : 0.34
% 12.79/9.71  Parsing              : 0.18
% 12.79/9.71  CNF conversion       : 0.02
% 12.79/9.71  Main loop            : 8.61
% 12.79/9.71  Inferencing          : 0.16
% 12.79/9.71  Reduction            : 0.11
% 12.79/9.71  Demodulation         : 0.07
% 12.79/9.71  BG Simplification    : 0.02
% 12.79/9.71  Subsumption          : 8.29
% 12.79/9.71  Abstraction          : 0.02
% 12.79/9.71  MUC search           : 0.00
% 12.79/9.71  Cooper               : 0.00
% 12.79/9.71  Total                : 8.96
% 12.79/9.71  Index Insertion      : 0.00
% 12.79/9.71  Index Deletion       : 0.00
% 12.79/9.71  Index Matching       : 0.00
% 12.79/9.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
