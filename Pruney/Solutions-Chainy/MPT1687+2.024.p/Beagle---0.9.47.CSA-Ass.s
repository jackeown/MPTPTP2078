%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:06 EST 2020

% Result     : CounterSatisfiable 3.69s
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
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:52:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.69/1.60  
% 3.69/1.60  % SZS status CounterSatisfiable for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.69/1.60  
% 3.69/1.60  Inference rules
% 3.69/1.60  ----------------------
% 3.69/1.60  #Ref     : 0
% 3.69/1.60  #Sup     : 166
% 3.69/1.60  #Fact    : 0
% 3.69/1.60  #Define  : 0
% 3.69/1.60  #Split   : 4
% 3.69/1.60  #Chain   : 0
% 3.69/1.60  #Close   : 0
% 3.69/1.60  
% 3.69/1.60  Ordering : KBO
% 3.69/1.60  
% 3.69/1.60  Simplification rules
% 3.69/1.60  ----------------------
% 3.69/1.60  #Subsume      : 50
% 3.69/1.60  #Demod        : 286
% 3.69/1.60  #Tautology    : 66
% 3.69/1.60  #SimpNegUnit  : 25
% 3.69/1.60  #BackRed      : 2
% 3.69/1.60  
% 3.69/1.60  #Partial instantiations: 0
% 3.69/1.60  #Strategies tried      : 1
% 3.69/1.60  
% 3.69/1.60  Timing (in seconds)
% 3.69/1.60  ----------------------
% 3.69/1.60  Preprocessing        : 0.36
% 3.69/1.60  Parsing              : 0.20
% 3.69/1.60  CNF conversion       : 0.02
% 3.69/1.61  Main loop            : 0.50
% 3.69/1.61  Inferencing          : 0.19
% 3.69/1.61  Reduction            : 0.16
% 3.69/1.61  Demodulation         : 0.11
% 3.69/1.61  BG Simplification    : 0.03
% 3.69/1.61  Subsumption          : 0.09
% 3.69/1.61  Abstraction          : 0.03
% 3.69/1.61  MUC search           : 0.00
% 3.69/1.61  Cooper               : 0.00
% 3.69/1.61  Total                : 0.87
% 3.69/1.61  Index Insertion      : 0.00
% 3.69/1.61  Index Deletion       : 0.00
% 3.69/1.61  Index Matching       : 0.00
% 3.69/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
