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
% DateTime   : Thu Dec  3 10:18:33 EST 2020

% Result     : CounterSatisfiable 2.84s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n006.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 12:05:22 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.84/1.71  
% 2.84/1.71  % SZS status CounterSatisfiable for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.84/1.71  
% 2.84/1.71  Inference rules
% 2.84/1.71  ----------------------
% 2.84/1.71  #Ref     : 0
% 2.84/1.71  #Sup     : 220
% 2.84/1.71  #Fact    : 0
% 2.84/1.71  #Define  : 0
% 2.84/1.71  #Split   : 1
% 2.84/1.71  #Chain   : 0
% 2.84/1.71  #Close   : 0
% 2.84/1.71  
% 2.84/1.71  Ordering : KBO
% 2.84/1.71  
% 2.84/1.71  Simplification rules
% 2.84/1.71  ----------------------
% 2.84/1.71  #Subsume      : 2
% 2.84/1.71  #Demod        : 102
% 2.84/1.71  #Tautology    : 199
% 2.84/1.71  #SimpNegUnit  : 2
% 2.84/1.71  #BackRed      : 4
% 2.84/1.71  
% 2.84/1.71  #Partial instantiations: 0
% 2.84/1.71  #Strategies tried      : 1
% 2.84/1.71  
% 2.84/1.71  Timing (in seconds)
% 2.84/1.71  ----------------------
% 2.84/1.71  Preprocessing        : 0.49
% 2.84/1.71  Parsing              : 0.26
% 2.84/1.71  CNF conversion       : 0.03
% 2.84/1.71  Main loop            : 0.41
% 2.84/1.71  Inferencing          : 0.15
% 2.84/1.71  Reduction            : 0.15
% 2.84/1.71  Demodulation         : 0.12
% 2.84/1.71  BG Simplification    : 0.02
% 2.84/1.71  Subsumption          : 0.05
% 2.84/1.71  Abstraction          : 0.03
% 2.84/1.71  MUC search           : 0.00
% 2.84/1.71  Cooper               : 0.00
% 2.84/1.71  Total                : 0.91
% 2.84/1.71  Index Insertion      : 0.00
% 2.84/1.71  Index Deletion       : 0.00
% 2.84/1.71  Index Matching       : 0.00
% 2.84/1.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
