%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:40 EST 2020

% Result     : CounterSatisfiable 3.52s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:03:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.52/1.71  
% 3.52/1.71  % SZS status CounterSatisfiable for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.52/1.71  
% 3.52/1.71  Inference rules
% 3.52/1.71  ----------------------
% 3.52/1.71  #Ref     : 0
% 3.52/1.71  #Sup     : 301
% 3.52/1.71  #Fact    : 0
% 3.52/1.71  #Define  : 0
% 3.52/1.71  #Split   : 7
% 3.52/1.71  #Chain   : 0
% 3.52/1.71  #Close   : 0
% 3.52/1.71  
% 3.52/1.71  Ordering : KBO
% 3.52/1.71  
% 3.52/1.71  Simplification rules
% 3.52/1.71  ----------------------
% 3.52/1.71  #Subsume      : 19
% 3.52/1.71  #Demod        : 199
% 3.52/1.71  #Tautology    : 215
% 3.52/1.71  #SimpNegUnit  : 0
% 3.52/1.71  #BackRed      : 9
% 3.52/1.71  
% 3.52/1.71  #Partial instantiations: 0
% 3.52/1.71  #Strategies tried      : 1
% 3.52/1.71  
% 3.52/1.71  Timing (in seconds)
% 3.52/1.71  ----------------------
% 3.52/1.71  Preprocessing        : 0.42
% 3.52/1.71  Parsing              : 0.24
% 3.52/1.71  CNF conversion       : 0.02
% 3.52/1.71  Main loop            : 0.44
% 3.52/1.71  Inferencing          : 0.15
% 3.52/1.71  Reduction            : 0.16
% 3.52/1.71  Demodulation         : 0.12
% 3.52/1.72  BG Simplification    : 0.02
% 3.52/1.72  Subsumption          : 0.07
% 3.52/1.72  Abstraction          : 0.02
% 3.52/1.72  MUC search           : 0.00
% 3.52/1.72  Cooper               : 0.00
% 3.52/1.72  Total                : 0.87
% 3.52/1.72  Index Insertion      : 0.00
% 3.52/1.72  Index Deletion       : 0.00
% 3.52/1.72  Index Matching       : 0.00
% 3.52/1.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
