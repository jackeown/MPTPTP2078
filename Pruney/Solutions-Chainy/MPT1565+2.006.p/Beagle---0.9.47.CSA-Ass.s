%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:12 EST 2020

% Result     : CounterSatisfiable 31.56s
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
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:52:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 31.56/21.76  
% 31.56/21.76  % SZS status CounterSatisfiable for /export/starexec/sandbox/benchmark/theBenchmark.p
% 31.56/21.76  
% 31.56/21.76  Inference rules
% 31.56/21.76  ----------------------
% 31.56/21.76  #Ref     : 0
% 31.56/21.76  #Sup     : 5706
% 31.56/21.76  #Fact    : 70
% 31.56/21.76  #Define  : 0
% 31.56/21.76  #Split   : 7
% 31.56/21.76  #Chain   : 0
% 31.56/21.76  #Close   : 0
% 31.56/21.76  
% 31.56/21.76  Ordering : KBO
% 31.56/21.76  
% 31.56/21.76  Simplification rules
% 31.56/21.76  ----------------------
% 31.56/21.76  #Subsume      : 5021
% 31.56/21.76  #Demod        : 50
% 31.56/21.76  #Tautology    : 737
% 31.56/21.76  #SimpNegUnit  : 0
% 31.56/21.76  #BackRed      : 0
% 31.56/21.76  
% 31.56/21.76  #Partial instantiations: 0
% 31.56/21.76  #Strategies tried      : 1
% 31.56/21.76  
% 31.56/21.76  Timing (in seconds)
% 31.56/21.76  ----------------------
% 31.56/21.76  Preprocessing        : 0.27
% 31.56/21.76  Parsing              : 0.15
% 31.56/21.76  CNF conversion       : 0.02
% 31.56/21.76  Main loop            : 20.74
% 31.56/21.76  Inferencing          : 1.43
% 31.56/21.76  Reduction            : 1.06
% 31.56/21.76  Demodulation         : 0.72
% 31.56/21.76  BG Simplification    : 0.19
% 31.56/21.76  Subsumption          : 17.41
% 31.56/21.76  Abstraction          : 0.24
% 31.56/21.76  MUC search           : 0.00
% 31.56/21.77  Cooper               : 0.00
% 31.56/21.77  Total                : 21.02
% 31.56/21.77  Index Insertion      : 0.00
% 31.56/21.77  Index Deletion       : 0.00
% 31.56/21.77  Index Matching       : 0.00
% 31.56/21.77  BG Taut test         : 0.00
%------------------------------------------------------------------------------
