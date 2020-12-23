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
% DateTime   : Thu Dec  3 09:48:37 EST 2020

% Result     : CounterSatisfiable 2.02s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:40:29 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.02/1.23  
% 2.02/1.23  % SZS status CounterSatisfiable for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.23  
% 2.02/1.23  Inference rules
% 2.02/1.23  ----------------------
% 2.02/1.23  #Ref     : 0
% 2.02/1.23  #Sup     : 50
% 2.02/1.23  #Fact    : 0
% 2.02/1.23  #Define  : 0
% 2.02/1.23  #Split   : 2
% 2.02/1.23  #Chain   : 0
% 2.02/1.23  #Close   : 0
% 2.02/1.23  
% 2.02/1.23  Ordering : KBO
% 2.02/1.23  
% 2.02/1.23  Simplification rules
% 2.02/1.23  ----------------------
% 2.02/1.23  #Subsume      : 3
% 2.02/1.23  #Demod        : 5
% 2.02/1.23  #Tautology    : 37
% 2.02/1.23  #SimpNegUnit  : 3
% 2.02/1.23  #BackRed      : 0
% 2.02/1.23  
% 2.02/1.23  #Partial instantiations: 0
% 2.02/1.23  #Strategies tried      : 1
% 2.02/1.23  
% 2.02/1.23  Timing (in seconds)
% 2.02/1.23  ----------------------
% 2.02/1.24  Preprocessing        : 0.32
% 2.02/1.24  Parsing              : 0.18
% 2.02/1.24  CNF conversion       : 0.02
% 2.02/1.24  Main loop            : 0.17
% 2.02/1.24  Inferencing          : 0.07
% 2.02/1.24  Reduction            : 0.05
% 2.02/1.24  Demodulation         : 0.03
% 2.02/1.24  BG Simplification    : 0.01
% 2.02/1.24  Subsumption          : 0.02
% 2.02/1.24  Abstraction          : 0.01
% 2.02/1.24  MUC search           : 0.00
% 2.02/1.24  Cooper               : 0.00
% 2.02/1.24  Total                : 0.50
% 2.02/1.24  Index Insertion      : 0.00
% 2.02/1.24  Index Deletion       : 0.00
% 2.02/1.24  Index Matching       : 0.00
% 2.02/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
