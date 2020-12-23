%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:58 EST 2020

% Result     : CounterSatisfiable 2.52s
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
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:07:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.52/1.35  
% 2.52/1.36  % SZS status CounterSatisfiable for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.52/1.36  
% 2.52/1.36  Inference rules
% 2.52/1.36  ----------------------
% 2.52/1.36  #Ref     : 0
% 2.52/1.36  #Sup     : 21
% 2.52/1.36  #Fact    : 0
% 2.52/1.36  #Define  : 0
% 2.52/1.36  #Split   : 1
% 2.52/1.36  #Chain   : 0
% 2.52/1.36  #Close   : 0
% 2.52/1.36  
% 2.52/1.36  Ordering : KBO
% 2.52/1.36  
% 2.52/1.36  Simplification rules
% 2.52/1.36  ----------------------
% 2.52/1.36  #Subsume      : 5
% 2.52/1.36  #Demod        : 2
% 2.52/1.36  #Tautology    : 2
% 2.52/1.36  #SimpNegUnit  : 1
% 2.52/1.36  #BackRed      : 0
% 2.52/1.36  
% 2.52/1.36  #Partial instantiations: 0
% 2.52/1.36  #Strategies tried      : 1
% 2.52/1.36  
% 2.52/1.36  Timing (in seconds)
% 2.52/1.36  ----------------------
% 2.52/1.36  Preprocessing        : 0.32
% 2.52/1.36  Parsing              : 0.17
% 2.52/1.36  CNF conversion       : 0.03
% 2.52/1.36  Main loop            : 0.28
% 2.52/1.36  Inferencing          : 0.13
% 2.52/1.36  Reduction            : 0.06
% 2.52/1.36  Demodulation         : 0.04
% 2.52/1.36  BG Simplification    : 0.02
% 2.52/1.36  Subsumption          : 0.05
% 2.52/1.36  Abstraction          : 0.01
% 2.52/1.36  MUC search           : 0.00
% 2.52/1.36  Cooper               : 0.00
% 2.52/1.36  Total                : 0.61
% 2.52/1.36  Index Insertion      : 0.00
% 2.52/1.36  Index Deletion       : 0.00
% 2.52/1.36  Index Matching       : 0.00
% 2.52/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
