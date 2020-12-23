%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:00 EST 2020

% Result     : CounterSatisfiable 2.14s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:43:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.14/1.28  
% 2.14/1.28  % SZS status CounterSatisfiable for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.28  
% 2.14/1.28  Inference rules
% 2.14/1.28  ----------------------
% 2.14/1.28  #Ref     : 0
% 2.14/1.28  #Sup     : 51
% 2.14/1.28  #Fact    : 0
% 2.14/1.28  #Define  : 0
% 2.14/1.28  #Split   : 5
% 2.14/1.28  #Chain   : 0
% 2.14/1.28  #Close   : 0
% 2.14/1.28  
% 2.14/1.28  Ordering : KBO
% 2.14/1.28  
% 2.14/1.28  Simplification rules
% 2.14/1.28  ----------------------
% 2.14/1.28  #Subsume      : 7
% 2.14/1.28  #Demod        : 42
% 2.14/1.28  #Tautology    : 39
% 2.14/1.28  #SimpNegUnit  : 1
% 2.14/1.28  #BackRed      : 1
% 2.14/1.28  
% 2.14/1.28  #Partial instantiations: 0
% 2.14/1.28  #Strategies tried      : 1
% 2.14/1.28  
% 2.14/1.28  Timing (in seconds)
% 2.14/1.28  ----------------------
% 2.14/1.29  Preprocessing        : 0.33
% 2.14/1.29  Parsing              : 0.17
% 2.14/1.29  CNF conversion       : 0.03
% 2.14/1.29  Main loop            : 0.19
% 2.14/1.29  Inferencing          : 0.06
% 2.14/1.29  Reduction            : 0.06
% 2.14/1.29  Demodulation         : 0.04
% 2.14/1.29  BG Simplification    : 0.02
% 2.14/1.29  Subsumption          : 0.04
% 2.14/1.29  Abstraction          : 0.01
% 2.14/1.29  MUC search           : 0.00
% 2.14/1.29  Cooper               : 0.00
% 2.14/1.29  Total                : 0.52
% 2.14/1.29  Index Insertion      : 0.00
% 2.14/1.29  Index Deletion       : 0.00
% 2.14/1.29  Index Matching       : 0.00
% 2.14/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
