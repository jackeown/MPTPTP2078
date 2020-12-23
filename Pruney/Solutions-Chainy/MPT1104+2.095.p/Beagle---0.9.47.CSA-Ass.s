%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:53 EST 2020

% Result     : CounterSatisfiable 2.32s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:38:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.32/1.47  
% 2.32/1.47  % SZS status CounterSatisfiable for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/1.47  
% 2.32/1.47  Inference rules
% 2.32/1.47  ----------------------
% 2.32/1.47  #Ref     : 0
% 2.32/1.47  #Sup     : 56
% 2.32/1.47  #Fact    : 0
% 2.32/1.47  #Define  : 0
% 2.32/1.47  #Split   : 0
% 2.32/1.47  #Chain   : 0
% 2.32/1.47  #Close   : 0
% 2.32/1.47  
% 2.32/1.47  Ordering : KBO
% 2.32/1.47  
% 2.32/1.47  Simplification rules
% 2.32/1.47  ----------------------
% 2.32/1.47  #Subsume      : 0
% 2.32/1.47  #Demod        : 3
% 2.32/1.47  #Tautology    : 39
% 2.32/1.47  #SimpNegUnit  : 0
% 2.32/1.47  #BackRed      : 0
% 2.32/1.47  
% 2.32/1.47  #Partial instantiations: 0
% 2.32/1.47  #Strategies tried      : 1
% 2.32/1.47  
% 2.32/1.47  Timing (in seconds)
% 2.32/1.47  ----------------------
% 2.32/1.48  Preprocessing        : 0.47
% 2.32/1.48  Parsing              : 0.25
% 2.32/1.48  CNF conversion       : 0.03
% 2.32/1.48  Main loop            : 0.22
% 2.32/1.48  Inferencing          : 0.08
% 2.32/1.48  Reduction            : 0.08
% 2.43/1.48  Demodulation         : 0.06
% 2.43/1.48  BG Simplification    : 0.02
% 2.43/1.48  Subsumption          : 0.03
% 2.43/1.48  Abstraction          : 0.02
% 2.43/1.48  MUC search           : 0.00
% 2.43/1.48  Cooper               : 0.00
% 2.43/1.48  Total                : 0.71
% 2.43/1.48  Index Insertion      : 0.00
% 2.43/1.48  Index Deletion       : 0.00
% 2.43/1.48  Index Matching       : 0.00
% 2.43/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
