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
% DateTime   : Thu Dec  3 10:18:46 EST 2020

% Result     : CounterSatisfiable 3.46s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:18:27 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.46/1.66  
% 3.46/1.66  % SZS status CounterSatisfiable for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.46/1.66  
% 3.46/1.66  Inference rules
% 3.46/1.66  ----------------------
% 3.46/1.66  #Ref     : 0
% 3.46/1.66  #Sup     : 410
% 3.46/1.66  #Fact    : 0
% 3.46/1.66  #Define  : 0
% 3.46/1.66  #Split   : 0
% 3.46/1.66  #Chain   : 0
% 3.46/1.66  #Close   : 0
% 3.46/1.66  
% 3.46/1.66  Ordering : KBO
% 3.46/1.66  
% 3.46/1.66  Simplification rules
% 3.46/1.66  ----------------------
% 3.46/1.66  #Subsume      : 14
% 3.46/1.66  #Demod        : 290
% 3.46/1.66  #Tautology    : 330
% 3.46/1.66  #SimpNegUnit  : 0
% 3.46/1.66  #BackRed      : 3
% 3.46/1.66  
% 3.46/1.66  #Partial instantiations: 0
% 3.46/1.66  #Strategies tried      : 1
% 3.46/1.66  
% 3.46/1.66  Timing (in seconds)
% 3.46/1.66  ----------------------
% 3.46/1.66  Preprocessing        : 0.37
% 3.46/1.66  Parsing              : 0.20
% 3.46/1.66  CNF conversion       : 0.02
% 3.46/1.66  Main loop            : 0.50
% 3.46/1.66  Inferencing          : 0.17
% 3.46/1.66  Reduction            : 0.19
% 3.46/1.66  Demodulation         : 0.15
% 3.46/1.66  BG Simplification    : 0.02
% 3.46/1.66  Subsumption          : 0.08
% 3.46/1.66  Abstraction          : 0.03
% 3.46/1.66  MUC search           : 0.00
% 3.46/1.66  Cooper               : 0.00
% 3.46/1.66  Total                : 0.88
% 3.46/1.66  Index Insertion      : 0.00
% 3.46/1.66  Index Deletion       : 0.00
% 3.46/1.66  Index Matching       : 0.00
% 3.46/1.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
