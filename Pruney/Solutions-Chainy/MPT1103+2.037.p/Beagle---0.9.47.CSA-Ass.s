%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:36 EST 2020

% Result     : CounterSatisfiable 3.52s
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
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:54:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.52/2.03  
% 3.52/2.03  % SZS status CounterSatisfiable for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.52/2.03  
% 3.52/2.03  Inference rules
% 3.52/2.03  ----------------------
% 3.52/2.03  #Ref     : 0
% 3.52/2.03  #Sup     : 373
% 3.52/2.03  #Fact    : 0
% 3.52/2.03  #Define  : 0
% 3.52/2.03  #Split   : 2
% 3.52/2.03  #Chain   : 0
% 3.52/2.03  #Close   : 0
% 3.52/2.03  
% 3.52/2.03  Ordering : KBO
% 3.52/2.03  
% 3.52/2.03  Simplification rules
% 3.52/2.03  ----------------------
% 3.52/2.03  #Subsume      : 5
% 3.52/2.03  #Demod        : 274
% 3.52/2.03  #Tautology    : 309
% 3.52/2.03  #SimpNegUnit  : 1
% 3.52/2.03  #BackRed      : 9
% 3.52/2.03  
% 3.52/2.03  #Partial instantiations: 0
% 3.52/2.03  #Strategies tried      : 1
% 3.52/2.03  
% 3.52/2.03  Timing (in seconds)
% 3.52/2.03  ----------------------
% 3.72/2.04  Preprocessing        : 0.54
% 3.72/2.04  Parsing              : 0.30
% 3.72/2.04  CNF conversion       : 0.03
% 3.72/2.04  Main loop            : 0.65
% 3.72/2.04  Inferencing          : 0.24
% 3.72/2.04  Reduction            : 0.23
% 3.72/2.04  Demodulation         : 0.18
% 3.72/2.04  BG Simplification    : 0.03
% 3.72/2.04  Subsumption          : 0.09
% 3.72/2.04  Abstraction          : 0.04
% 3.72/2.04  MUC search           : 0.00
% 3.72/2.04  Cooper               : 0.00
% 3.72/2.04  Total                : 1.21
% 3.72/2.04  Index Insertion      : 0.00
% 3.72/2.04  Index Deletion       : 0.00
% 3.72/2.04  Index Matching       : 0.00
% 3.72/2.04  BG Taut test         : 0.00
%------------------------------------------------------------------------------
