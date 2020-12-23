%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:01 EST 2020

% Result     : CounterSatisfiable 2.02s
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
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:52:46 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.02/1.52  
% 2.02/1.52  % SZS status CounterSatisfiable for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.52  
% 2.02/1.52  Inference rules
% 2.02/1.52  ----------------------
% 2.02/1.52  #Ref     : 0
% 2.02/1.52  #Sup     : 8
% 2.02/1.52  #Fact    : 0
% 2.02/1.52  #Define  : 0
% 2.02/1.52  #Split   : 0
% 2.02/1.52  #Chain   : 0
% 2.02/1.52  #Close   : 0
% 2.02/1.52  
% 2.02/1.52  Ordering : KBO
% 2.02/1.52  
% 2.02/1.52  Simplification rules
% 2.02/1.52  ----------------------
% 2.02/1.52  #Subsume      : 2
% 2.02/1.52  #Demod        : 3
% 2.02/1.52  #Tautology    : 3
% 2.02/1.52  #SimpNegUnit  : 0
% 2.02/1.52  #BackRed      : 1
% 2.02/1.52  
% 2.02/1.52  #Partial instantiations: 0
% 2.02/1.52  #Strategies tried      : 1
% 2.02/1.52  
% 2.02/1.52  Timing (in seconds)
% 2.02/1.52  ----------------------
% 2.15/1.53  Preprocessing        : 0.42
% 2.15/1.53  Parsing              : 0.23
% 2.15/1.53  CNF conversion       : 0.03
% 2.15/1.53  Main loop            : 0.18
% 2.15/1.53  Inferencing          : 0.08
% 2.15/1.53  Reduction            : 0.04
% 2.15/1.53  Demodulation         : 0.03
% 2.15/1.53  BG Simplification    : 0.01
% 2.15/1.53  Subsumption          : 0.03
% 2.15/1.53  Abstraction          : 0.01
% 2.15/1.53  MUC search           : 0.00
% 2.15/1.53  Cooper               : 0.00
% 2.15/1.53  Total                : 0.61
% 2.15/1.53  Index Insertion      : 0.00
% 2.15/1.53  Index Deletion       : 0.00
% 2.15/1.53  Index Matching       : 0.00
% 2.15/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
