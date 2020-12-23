%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:51 EST 2020

% Result     : CounterSatisfiable 5.34s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:13:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.34/2.00  
% 5.34/2.00  % SZS status CounterSatisfiable for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.34/2.00  
% 5.34/2.00  Inference rules
% 5.34/2.00  ----------------------
% 5.34/2.00  #Ref     : 6
% 5.34/2.00  #Sup     : 699
% 5.34/2.00  #Fact    : 0
% 5.34/2.00  #Define  : 0
% 5.34/2.00  #Split   : 2
% 5.34/2.00  #Chain   : 0
% 5.34/2.00  #Close   : 0
% 5.34/2.00  
% 5.34/2.00  Ordering : KBO
% 5.34/2.00  
% 5.34/2.00  Simplification rules
% 5.34/2.00  ----------------------
% 5.34/2.00  #Subsume      : 192
% 5.34/2.00  #Demod        : 289
% 5.34/2.00  #Tautology    : 456
% 5.34/2.00  #SimpNegUnit  : 4
% 5.34/2.00  #BackRed      : 1
% 5.34/2.00  
% 5.34/2.00  #Partial instantiations: 0
% 5.34/2.00  #Strategies tried      : 1
% 5.34/2.00  
% 5.34/2.00  Timing (in seconds)
% 5.34/2.00  ----------------------
% 5.34/2.00  Preprocessing        : 0.29
% 5.34/2.00  Parsing              : 0.16
% 5.34/2.00  CNF conversion       : 0.02
% 5.34/2.00  Main loop            : 0.96
% 5.34/2.00  Inferencing          : 0.31
% 5.34/2.00  Reduction            : 0.38
% 5.34/2.00  Demodulation         : 0.31
% 5.34/2.00  BG Simplification    : 0.05
% 5.34/2.00  Subsumption          : 0.18
% 5.34/2.00  Abstraction          : 0.07
% 5.34/2.00  MUC search           : 0.00
% 5.34/2.00  Cooper               : 0.00
% 5.34/2.00  Total                : 1.26
% 5.34/2.00  Index Insertion      : 0.00
% 5.34/2.00  Index Deletion       : 0.00
% 5.34/2.00  Index Matching       : 0.00
% 5.34/2.00  BG Taut test         : 0.00
%------------------------------------------------------------------------------
