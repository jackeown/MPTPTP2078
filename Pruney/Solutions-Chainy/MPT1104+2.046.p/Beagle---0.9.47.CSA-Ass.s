%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:48 EST 2020

% Result     : CounterSatisfiable 2.74s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.31  % Computer   : n003.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % DateTime   : Tue Dec  1 16:38:42 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.74/1.49  
% 2.74/1.49  % SZS status CounterSatisfiable for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.74/1.49  
% 2.74/1.49  Inference rules
% 2.74/1.49  ----------------------
% 2.74/1.49  #Ref     : 0
% 2.74/1.49  #Sup     : 189
% 2.74/1.49  #Fact    : 0
% 2.74/1.49  #Define  : 0
% 2.74/1.49  #Split   : 0
% 2.74/1.49  #Chain   : 0
% 2.74/1.49  #Close   : 0
% 2.74/1.49  
% 2.74/1.49  Ordering : KBO
% 2.74/1.49  
% 2.74/1.49  Simplification rules
% 2.74/1.49  ----------------------
% 2.74/1.49  #Subsume      : 8
% 2.74/1.49  #Demod        : 71
% 2.74/1.49  #Tautology    : 148
% 2.74/1.49  #SimpNegUnit  : 0
% 2.74/1.49  #BackRed      : 1
% 2.74/1.49  
% 2.74/1.49  #Partial instantiations: 0
% 2.74/1.49  #Strategies tried      : 1
% 2.74/1.49  
% 2.74/1.49  Timing (in seconds)
% 2.74/1.49  ----------------------
% 2.74/1.49  Preprocessing        : 0.41
% 2.74/1.49  Parsing              : 0.22
% 2.74/1.49  CNF conversion       : 0.02
% 2.74/1.49  Main loop            : 0.32
% 2.74/1.49  Inferencing          : 0.12
% 2.74/1.49  Reduction            : 0.12
% 2.74/1.49  Demodulation         : 0.09
% 2.74/1.49  BG Simplification    : 0.02
% 2.74/1.49  Subsumption          : 0.05
% 2.74/1.49  Abstraction          : 0.02
% 2.74/1.49  MUC search           : 0.00
% 2.74/1.50  Cooper               : 0.00
% 2.74/1.50  Total                : 0.74
% 2.74/1.50  Index Insertion      : 0.00
% 2.74/1.50  Index Deletion       : 0.00
% 2.74/1.50  Index Matching       : 0.00
% 2.74/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
