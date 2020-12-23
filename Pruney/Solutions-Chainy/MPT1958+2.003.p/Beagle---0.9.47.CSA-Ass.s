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
% DateTime   : Thu Dec  3 10:30:57 EST 2020

% Result     : CounterSatisfiable 4.58s
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
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:28:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.58/1.86  
% 4.58/1.86  % SZS status CounterSatisfiable for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.58/1.86  
% 4.58/1.86  Inference rules
% 4.58/1.86  ----------------------
% 4.58/1.86  #Ref     : 0
% 4.58/1.86  #Sup     : 154
% 4.58/1.86  #Fact    : 0
% 4.58/1.86  #Define  : 0
% 4.58/1.86  #Split   : 2
% 4.58/1.86  #Chain   : 0
% 4.58/1.86  #Close   : 0
% 4.58/1.86  
% 4.58/1.86  Ordering : KBO
% 4.58/1.86  
% 4.58/1.86  Simplification rules
% 4.58/1.86  ----------------------
% 4.58/1.86  #Subsume      : 100
% 4.58/1.86  #Demod        : 159
% 4.58/1.86  #Tautology    : 31
% 4.58/1.86  #SimpNegUnit  : 5
% 4.58/1.86  #BackRed      : 0
% 4.58/1.86  
% 4.58/1.86  #Partial instantiations: 0
% 4.58/1.86  #Strategies tried      : 1
% 4.58/1.86  
% 4.58/1.86  Timing (in seconds)
% 4.58/1.86  ----------------------
% 4.58/1.86  Preprocessing        : 0.34
% 4.58/1.86  Parsing              : 0.18
% 4.58/1.86  CNF conversion       : 0.02
% 4.58/1.86  Main loop            : 0.77
% 4.58/1.86  Inferencing          : 0.19
% 4.58/1.86  Reduction            : 0.13
% 4.58/1.86  Demodulation         : 0.09
% 4.58/1.86  BG Simplification    : 0.02
% 4.58/1.86  Subsumption          : 0.39
% 4.58/1.86  Abstraction          : 0.04
% 4.58/1.86  MUC search           : 0.00
% 4.58/1.86  Cooper               : 0.00
% 4.58/1.86  Total                : 1.12
% 4.58/1.87  Index Insertion      : 0.00
% 4.58/1.87  Index Deletion       : 0.00
% 4.58/1.87  Index Matching       : 0.00
% 4.58/1.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
