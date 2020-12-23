%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:12 EST 2020

% Result     : CounterSatisfiable 2.43s
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
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:14:25 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.43/1.41  
% 2.43/1.41  % SZS status CounterSatisfiable for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.43/1.41  
% 2.43/1.41  Inference rules
% 2.43/1.41  ----------------------
% 2.43/1.41  #Ref     : 0
% 2.43/1.41  #Sup     : 48
% 2.43/1.41  #Fact    : 0
% 2.43/1.41  #Define  : 0
% 2.43/1.41  #Split   : 1
% 2.43/1.41  #Chain   : 0
% 2.43/1.41  #Close   : 0
% 2.43/1.41  
% 2.43/1.41  Ordering : KBO
% 2.43/1.41  
% 2.43/1.41  Simplification rules
% 2.43/1.41  ----------------------
% 2.43/1.41  #Subsume      : 13
% 2.43/1.41  #Demod        : 0
% 2.43/1.41  #Tautology    : 8
% 2.43/1.41  #SimpNegUnit  : 0
% 2.43/1.41  #BackRed      : 0
% 2.43/1.41  
% 2.43/1.41  #Partial instantiations: 0
% 2.43/1.41  #Strategies tried      : 1
% 2.43/1.41  
% 2.43/1.41  Timing (in seconds)
% 2.43/1.41  ----------------------
% 2.43/1.41  Preprocessing        : 0.33
% 2.43/1.41  Parsing              : 0.19
% 2.43/1.41  CNF conversion       : 0.03
% 2.43/1.41  Main loop            : 0.25
% 2.43/1.41  Inferencing          : 0.11
% 2.43/1.41  Reduction            : 0.05
% 2.43/1.41  Demodulation         : 0.03
% 2.43/1.41  BG Simplification    : 0.02
% 2.43/1.41  Subsumption          : 0.06
% 2.43/1.41  Abstraction          : 0.01
% 2.43/1.41  MUC search           : 0.00
% 2.43/1.41  Cooper               : 0.00
% 2.43/1.41  Total                : 0.59
% 2.43/1.41  Index Insertion      : 0.00
% 2.43/1.41  Index Deletion       : 0.00
% 2.43/1.41  Index Matching       : 0.00
% 2.43/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
