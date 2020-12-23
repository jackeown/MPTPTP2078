%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:45 EST 2020

% Result     : CounterSatisfiable 6.64s
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
% 0.13/0.33  % Computer   : n023.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 11:41:06 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.64/2.44  
% 6.64/2.44  % SZS status CounterSatisfiable for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.64/2.44  
% 6.64/2.44  Inference rules
% 6.64/2.44  ----------------------
% 6.64/2.44  #Ref     : 0
% 6.64/2.44  #Sup     : 1694
% 6.64/2.44  #Fact    : 0
% 6.64/2.44  #Define  : 0
% 6.64/2.44  #Split   : 0
% 6.64/2.44  #Chain   : 0
% 6.64/2.44  #Close   : 0
% 6.64/2.44  
% 6.64/2.44  Ordering : KBO
% 6.64/2.44  
% 6.64/2.44  Simplification rules
% 6.64/2.44  ----------------------
% 6.64/2.44  #Subsume      : 423
% 6.64/2.44  #Demod        : 3675
% 6.64/2.44  #Tautology    : 1197
% 6.64/2.44  #SimpNegUnit  : 0
% 6.64/2.44  #BackRed      : 3
% 6.64/2.44  
% 6.64/2.44  #Partial instantiations: 0
% 6.64/2.44  #Strategies tried      : 1
% 6.64/2.44  
% 6.64/2.44  Timing (in seconds)
% 6.64/2.44  ----------------------
% 6.64/2.45  Preprocessing        : 0.36
% 6.64/2.45  Parsing              : 0.19
% 6.64/2.45  CNF conversion       : 0.02
% 6.64/2.45  Main loop            : 1.27
% 6.64/2.45  Inferencing          : 0.31
% 6.64/2.45  Reduction            : 0.73
% 6.64/2.45  Demodulation         : 0.65
% 6.64/2.45  BG Simplification    : 0.03
% 6.64/2.45  Subsumption          : 0.15
% 6.64/2.45  Abstraction          : 0.07
% 6.64/2.45  MUC search           : 0.00
% 6.64/2.45  Cooper               : 0.00
% 6.64/2.45  Total                : 1.65
% 6.64/2.45  Index Insertion      : 0.00
% 6.64/2.45  Index Deletion       : 0.00
% 6.64/2.45  Index Matching       : 0.00
% 6.64/2.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
