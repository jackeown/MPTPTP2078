%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:42 EST 2020

% Result     : CounterSatisfiable 1.88s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:20:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.88/1.23  
% 1.88/1.23  % SZS status CounterSatisfiable for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.23  
% 1.88/1.23  Inference rules
% 1.88/1.23  ----------------------
% 1.88/1.23  #Ref     : 0
% 1.88/1.23  #Sup     : 57
% 1.88/1.23  #Fact    : 0
% 1.88/1.23  #Define  : 0
% 1.88/1.23  #Split   : 4
% 1.88/1.23  #Chain   : 0
% 1.88/1.23  #Close   : 0
% 1.88/1.23  
% 1.88/1.23  Ordering : KBO
% 1.88/1.23  
% 1.88/1.23  Simplification rules
% 1.88/1.23  ----------------------
% 1.88/1.23  #Subsume      : 2
% 1.88/1.23  #Demod        : 18
% 1.88/1.23  #Tautology    : 40
% 1.88/1.23  #SimpNegUnit  : 0
% 1.88/1.23  #BackRed      : 1
% 1.88/1.23  
% 1.88/1.23  #Partial instantiations: 0
% 1.88/1.23  #Strategies tried      : 1
% 1.88/1.23  
% 1.88/1.23  Timing (in seconds)
% 1.88/1.23  ----------------------
% 1.88/1.23  Preprocessing        : 0.29
% 1.88/1.23  Parsing              : 0.16
% 1.88/1.23  CNF conversion       : 0.02
% 1.88/1.23  Main loop            : 0.18
% 1.88/1.23  Inferencing          : 0.07
% 1.88/1.23  Reduction            : 0.06
% 1.88/1.23  Demodulation         : 0.04
% 2.05/1.23  BG Simplification    : 0.01
% 2.05/1.23  Subsumption          : 0.03
% 2.05/1.23  Abstraction          : 0.01
% 2.05/1.23  MUC search           : 0.00
% 2.05/1.23  Cooper               : 0.00
% 2.05/1.23  Total                : 0.49
% 2.05/1.23  Index Insertion      : 0.00
% 2.05/1.23  Index Deletion       : 0.00
% 2.05/1.23  Index Matching       : 0.00
% 2.05/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
