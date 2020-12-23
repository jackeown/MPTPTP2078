%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:09 EST 2020

% Result     : CounterSatisfiable 2.86s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 09:49:04 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.86/1.38  
% 2.86/1.38  % SZS status CounterSatisfiable for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.86/1.38  
% 2.86/1.38  Inference rules
% 2.86/1.38  ----------------------
% 2.86/1.38  #Ref     : 0
% 2.86/1.38  #Sup     : 75
% 2.86/1.38  #Fact    : 0
% 2.86/1.38  #Define  : 0
% 2.86/1.38  #Split   : 3
% 2.86/1.38  #Chain   : 0
% 2.86/1.38  #Close   : 0
% 2.86/1.39  
% 2.86/1.39  Ordering : KBO
% 2.86/1.39  
% 2.86/1.39  Simplification rules
% 2.86/1.39  ----------------------
% 2.86/1.39  #Subsume      : 25
% 2.86/1.39  #Demod        : 28
% 2.86/1.39  #Tautology    : 22
% 2.86/1.39  #SimpNegUnit  : 2
% 2.86/1.39  #BackRed      : 0
% 2.86/1.39  
% 2.86/1.39  #Partial instantiations: 0
% 2.86/1.39  #Strategies tried      : 1
% 2.86/1.39  
% 2.86/1.39  Timing (in seconds)
% 2.86/1.39  ----------------------
% 2.86/1.39  Preprocessing        : 0.31
% 2.86/1.39  Parsing              : 0.17
% 2.86/1.39  CNF conversion       : 0.02
% 2.86/1.39  Main loop            : 0.34
% 2.86/1.39  Inferencing          : 0.13
% 2.86/1.39  Reduction            : 0.07
% 2.86/1.39  Demodulation         : 0.05
% 2.86/1.39  BG Simplification    : 0.02
% 2.86/1.39  Subsumption          : 0.09
% 2.86/1.39  Abstraction          : 0.02
% 2.86/1.39  MUC search           : 0.00
% 2.86/1.39  Cooper               : 0.00
% 2.86/1.39  Total                : 0.66
% 2.86/1.39  Index Insertion      : 0.00
% 2.86/1.39  Index Deletion       : 0.00
% 2.86/1.39  Index Matching       : 0.00
% 2.86/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
