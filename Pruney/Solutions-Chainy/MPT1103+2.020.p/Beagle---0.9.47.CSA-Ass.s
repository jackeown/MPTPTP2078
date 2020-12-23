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
% DateTime   : Thu Dec  3 10:18:34 EST 2020

% Result     : CounterSatisfiable 3.93s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:18:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.93/1.74  
% 3.93/1.74  % SZS status CounterSatisfiable for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.93/1.74  
% 3.93/1.74  Inference rules
% 3.93/1.74  ----------------------
% 3.93/1.74  #Ref     : 0
% 3.93/1.74  #Sup     : 738
% 3.93/1.74  #Fact    : 0
% 3.93/1.74  #Define  : 0
% 3.93/1.74  #Split   : 4
% 3.93/1.74  #Chain   : 0
% 3.93/1.74  #Close   : 0
% 3.93/1.74  
% 3.93/1.74  Ordering : KBO
% 3.93/1.74  
% 3.93/1.74  Simplification rules
% 3.93/1.74  ----------------------
% 3.93/1.74  #Subsume      : 59
% 3.93/1.74  #Demod        : 931
% 3.93/1.74  #Tautology    : 605
% 3.93/1.74  #SimpNegUnit  : 2
% 3.93/1.74  #BackRed      : 4
% 3.93/1.74  
% 3.93/1.74  #Partial instantiations: 0
% 3.93/1.74  #Strategies tried      : 1
% 3.93/1.74  
% 3.93/1.74  Timing (in seconds)
% 3.93/1.74  ----------------------
% 3.93/1.74  Preprocessing        : 0.32
% 3.93/1.74  Parsing              : 0.18
% 3.93/1.74  CNF conversion       : 0.02
% 3.93/1.74  Main loop            : 0.67
% 3.93/1.74  Inferencing          : 0.20
% 3.93/1.74  Reduction            : 0.32
% 3.93/1.74  Demodulation         : 0.27
% 3.93/1.74  BG Simplification    : 0.02
% 3.93/1.74  Subsumption          : 0.09
% 3.93/1.74  Abstraction          : 0.03
% 3.93/1.74  MUC search           : 0.00
% 3.93/1.74  Cooper               : 0.00
% 3.93/1.74  Total                : 1.01
% 3.93/1.74  Index Insertion      : 0.00
% 3.93/1.74  Index Deletion       : 0.00
% 3.93/1.74  Index Matching       : 0.00
% 3.93/1.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
