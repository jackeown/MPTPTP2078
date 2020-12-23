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
% DateTime   : Thu Dec  3 10:25:43 EST 2020

% Result     : CounterSatisfiable 3.17s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:29:44 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.17/1.52  
% 3.17/1.53  % SZS status CounterSatisfiable for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.17/1.53  
% 3.17/1.53  Inference rules
% 3.17/1.53  ----------------------
% 3.17/1.53  #Ref     : 6
% 3.17/1.53  #Sup     : 172
% 3.17/1.53  #Fact    : 0
% 3.17/1.53  #Define  : 0
% 3.17/1.53  #Split   : 2
% 3.17/1.53  #Chain   : 0
% 3.17/1.53  #Close   : 0
% 3.17/1.53  
% 3.17/1.53  Ordering : KBO
% 3.17/1.53  
% 3.17/1.53  Simplification rules
% 3.17/1.53  ----------------------
% 3.17/1.53  #Subsume      : 35
% 3.17/1.53  #Demod        : 311
% 3.17/1.53  #Tautology    : 109
% 3.17/1.53  #SimpNegUnit  : 1
% 3.17/1.53  #BackRed      : 7
% 3.17/1.53  
% 3.17/1.53  #Partial instantiations: 0
% 3.17/1.53  #Strategies tried      : 1
% 3.17/1.53  
% 3.17/1.53  Timing (in seconds)
% 3.17/1.53  ----------------------
% 3.17/1.53  Preprocessing        : 0.37
% 3.17/1.53  Parsing              : 0.19
% 3.17/1.53  CNF conversion       : 0.03
% 3.17/1.53  Main loop            : 0.37
% 3.17/1.53  Inferencing          : 0.13
% 3.17/1.53  Reduction            : 0.12
% 3.17/1.53  Demodulation         : 0.08
% 3.17/1.53  BG Simplification    : 0.02
% 3.17/1.53  Subsumption          : 0.08
% 3.17/1.53  Abstraction          : 0.02
% 3.17/1.53  MUC search           : 0.00
% 3.17/1.53  Cooper               : 0.00
% 3.17/1.53  Total                : 0.75
% 3.17/1.53  Index Insertion      : 0.00
% 3.17/1.53  Index Deletion       : 0.00
% 3.17/1.53  Index Matching       : 0.00
% 3.33/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
