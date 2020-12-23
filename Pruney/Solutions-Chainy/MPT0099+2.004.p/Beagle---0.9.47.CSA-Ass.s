%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:36 EST 2020

% Result     : CounterSatisfiable 1.47s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 15:42:06 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.47/1.05  
% 1.47/1.05  % SZS status CounterSatisfiable for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.47/1.05  
% 1.47/1.05  Inference rules
% 1.47/1.05  ----------------------
% 1.47/1.05  #Ref     : 0
% 1.47/1.05  #Sup     : 5
% 1.47/1.05  #Fact    : 0
% 1.47/1.05  #Define  : 0
% 1.47/1.05  #Split   : 0
% 1.47/1.05  #Chain   : 0
% 1.47/1.05  #Close   : 0
% 1.47/1.05  
% 1.47/1.05  Ordering : KBO
% 1.47/1.05  
% 1.47/1.05  Simplification rules
% 1.47/1.05  ----------------------
% 1.47/1.05  #Subsume      : 0
% 1.47/1.05  #Demod        : 0
% 1.47/1.05  #Tautology    : 5
% 1.47/1.05  #SimpNegUnit  : 0
% 1.47/1.05  #BackRed      : 0
% 1.47/1.05  
% 1.47/1.05  #Partial instantiations: 0
% 1.47/1.05  #Strategies tried      : 1
% 1.47/1.05  
% 1.47/1.05  Timing (in seconds)
% 1.47/1.05  ----------------------
% 1.47/1.06  Preprocessing        : 0.23
% 1.47/1.06  Parsing              : 0.13
% 1.47/1.06  CNF conversion       : 0.01
% 1.47/1.06  Main loop            : 0.06
% 1.47/1.06  Inferencing          : 0.03
% 1.47/1.06  Reduction            : 0.01
% 1.47/1.06  Demodulation         : 0.01
% 1.47/1.06  BG Simplification    : 0.01
% 1.47/1.06  Subsumption          : 0.01
% 1.47/1.06  Abstraction          : 0.00
% 1.47/1.06  MUC search           : 0.00
% 1.47/1.06  Cooper               : 0.00
% 1.47/1.06  Total                : 0.31
% 1.47/1.06  Index Insertion      : 0.00
% 1.47/1.06  Index Deletion       : 0.00
% 1.47/1.06  Index Matching       : 0.00
% 1.47/1.06  BG Taut test         : 0.00
%------------------------------------------------------------------------------
