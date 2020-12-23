%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:34 EST 2020

% Result     : CounterSatisfiable 4.02s
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
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:18:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.02/1.73  
% 4.02/1.73  % SZS status CounterSatisfiable for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.02/1.73  
% 4.02/1.73  Inference rules
% 4.02/1.73  ----------------------
% 4.02/1.73  #Ref     : 0
% 4.02/1.73  #Sup     : 725
% 4.02/1.73  #Fact    : 0
% 4.02/1.73  #Define  : 0
% 4.02/1.73  #Split   : 1
% 4.02/1.73  #Chain   : 0
% 4.02/1.73  #Close   : 0
% 4.02/1.73  
% 4.02/1.73  Ordering : KBO
% 4.02/1.73  
% 4.02/1.73  Simplification rules
% 4.02/1.73  ----------------------
% 4.02/1.73  #Subsume      : 71
% 4.02/1.73  #Demod        : 1017
% 4.02/1.73  #Tautology    : 597
% 4.02/1.73  #SimpNegUnit  : 0
% 4.02/1.73  #BackRed      : 1
% 4.02/1.73  
% 4.02/1.73  #Partial instantiations: 0
% 4.02/1.73  #Strategies tried      : 1
% 4.02/1.73  
% 4.02/1.73  Timing (in seconds)
% 4.02/1.73  ----------------------
% 4.02/1.73  Preprocessing        : 0.32
% 4.02/1.73  Parsing              : 0.17
% 4.02/1.73  CNF conversion       : 0.02
% 4.02/1.73  Main loop            : 0.65
% 4.02/1.73  Inferencing          : 0.20
% 4.02/1.73  Reduction            : 0.31
% 4.02/1.73  Demodulation         : 0.27
% 4.02/1.73  BG Simplification    : 0.02
% 4.02/1.73  Subsumption          : 0.07
% 4.02/1.73  Abstraction          : 0.04
% 4.02/1.73  MUC search           : 0.00
% 4.02/1.73  Cooper               : 0.00
% 4.02/1.73  Total                : 0.98
% 4.02/1.73  Index Insertion      : 0.00
% 4.02/1.73  Index Deletion       : 0.00
% 4.02/1.73  Index Matching       : 0.00
% 4.02/1.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
