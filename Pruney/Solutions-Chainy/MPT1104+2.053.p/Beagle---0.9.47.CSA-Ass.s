%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:49 EST 2020

% Result     : CounterSatisfiable 5.15s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:00:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.15/2.01  
% 5.15/2.01  % SZS status CounterSatisfiable for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.15/2.01  
% 5.15/2.01  Inference rules
% 5.15/2.01  ----------------------
% 5.15/2.01  #Ref     : 5
% 5.15/2.01  #Sup     : 708
% 5.15/2.01  #Fact    : 0
% 5.15/2.01  #Define  : 0
% 5.15/2.01  #Split   : 2
% 5.15/2.01  #Chain   : 0
% 5.15/2.01  #Close   : 0
% 5.15/2.01  
% 5.15/2.01  Ordering : KBO
% 5.15/2.01  
% 5.15/2.01  Simplification rules
% 5.15/2.01  ----------------------
% 5.15/2.01  #Subsume      : 205
% 5.15/2.01  #Demod        : 285
% 5.15/2.01  #Tautology    : 449
% 5.15/2.01  #SimpNegUnit  : 4
% 5.15/2.01  #BackRed      : 0
% 5.15/2.01  
% 5.15/2.01  #Partial instantiations: 0
% 5.15/2.01  #Strategies tried      : 1
% 5.15/2.01  
% 5.15/2.01  Timing (in seconds)
% 5.15/2.01  ----------------------
% 5.15/2.02  Preprocessing        : 0.30
% 5.15/2.02  Parsing              : 0.17
% 5.15/2.02  CNF conversion       : 0.02
% 5.15/2.02  Main loop            : 0.93
% 5.15/2.02  Inferencing          : 0.30
% 5.15/2.02  Reduction            : 0.35
% 5.15/2.02  Demodulation         : 0.29
% 5.15/2.02  BG Simplification    : 0.05
% 5.15/2.02  Subsumption          : 0.18
% 5.15/2.02  Abstraction          : 0.07
% 5.15/2.02  MUC search           : 0.00
% 5.15/2.02  Cooper               : 0.00
% 5.15/2.02  Total                : 1.24
% 5.15/2.02  Index Insertion      : 0.00
% 5.15/2.02  Index Deletion       : 0.00
% 5.15/2.02  Index Matching       : 0.00
% 5.15/2.02  BG Taut test         : 0.00
%------------------------------------------------------------------------------
