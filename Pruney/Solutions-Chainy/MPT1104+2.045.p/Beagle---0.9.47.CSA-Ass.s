%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:48 EST 2020

% Result     : CounterSatisfiable 3.04s
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
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:10:14 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.04/1.57  
% 3.04/1.57  % SZS status CounterSatisfiable for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.04/1.57  
% 3.04/1.57  Inference rules
% 3.04/1.57  ----------------------
% 3.04/1.57  #Ref     : 0
% 3.04/1.57  #Sup     : 223
% 3.04/1.57  #Fact    : 0
% 3.04/1.57  #Define  : 0
% 3.04/1.57  #Split   : 1
% 3.04/1.57  #Chain   : 0
% 3.04/1.57  #Close   : 0
% 3.04/1.57  
% 3.04/1.57  Ordering : KBO
% 3.04/1.57  
% 3.04/1.57  Simplification rules
% 3.04/1.57  ----------------------
% 3.04/1.57  #Subsume      : 18
% 3.04/1.57  #Demod        : 54
% 3.04/1.57  #Tautology    : 163
% 3.04/1.57  #SimpNegUnit  : 0
% 3.04/1.57  #BackRed      : 1
% 3.04/1.57  
% 3.04/1.57  #Partial instantiations: 0
% 3.04/1.57  #Strategies tried      : 1
% 3.04/1.57  
% 3.04/1.57  Timing (in seconds)
% 3.04/1.57  ----------------------
% 3.04/1.58  Preprocessing        : 0.36
% 3.04/1.58  Parsing              : 0.18
% 3.04/1.58  CNF conversion       : 0.02
% 3.04/1.58  Main loop            : 0.36
% 3.04/1.58  Inferencing          : 0.13
% 3.04/1.58  Reduction            : 0.13
% 3.04/1.58  Demodulation         : 0.10
% 3.04/1.58  BG Simplification    : 0.02
% 3.04/1.58  Subsumption          : 0.06
% 3.04/1.58  Abstraction          : 0.02
% 3.04/1.58  MUC search           : 0.00
% 3.04/1.58  Cooper               : 0.00
% 3.04/1.58  Total                : 0.74
% 3.04/1.58  Index Insertion      : 0.00
% 3.04/1.58  Index Deletion       : 0.00
% 3.04/1.58  Index Matching       : 0.00
% 3.04/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
