%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:00 EST 2020

% Result     : CounterSatisfiable 2.90s
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
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:06:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.90/1.45  
% 2.90/1.45  % SZS status CounterSatisfiable for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.90/1.45  
% 2.90/1.45  Inference rules
% 2.90/1.45  ----------------------
% 2.90/1.45  #Ref     : 0
% 2.90/1.45  #Sup     : 52
% 2.90/1.45  #Fact    : 0
% 2.90/1.45  #Define  : 0
% 2.90/1.45  #Split   : 4
% 2.90/1.45  #Chain   : 0
% 2.90/1.45  #Close   : 0
% 2.90/1.45  
% 2.90/1.45  Ordering : KBO
% 2.90/1.45  
% 2.90/1.45  Simplification rules
% 2.90/1.45  ----------------------
% 2.90/1.45  #Subsume      : 8
% 2.90/1.45  #Demod        : 6
% 2.90/1.45  #Tautology    : 9
% 2.90/1.45  #SimpNegUnit  : 1
% 2.90/1.45  #BackRed      : 0
% 2.90/1.45  
% 2.90/1.45  #Partial instantiations: 0
% 2.90/1.45  #Strategies tried      : 1
% 2.90/1.45  
% 2.90/1.45  Timing (in seconds)
% 2.90/1.45  ----------------------
% 2.90/1.46  Preprocessing        : 0.28
% 2.90/1.46  Parsing              : 0.15
% 2.90/1.46  CNF conversion       : 0.02
% 2.90/1.46  Main loop            : 0.35
% 2.90/1.46  Inferencing          : 0.13
% 2.90/1.46  Reduction            : 0.07
% 2.90/1.46  Demodulation         : 0.05
% 2.90/1.46  BG Simplification    : 0.02
% 2.90/1.46  Subsumption          : 0.10
% 2.90/1.46  Abstraction          : 0.01
% 2.90/1.46  MUC search           : 0.00
% 2.90/1.46  Cooper               : 0.00
% 2.90/1.46  Total                : 0.63
% 2.90/1.46  Index Insertion      : 0.00
% 2.90/1.46  Index Deletion       : 0.00
% 2.90/1.46  Index Matching       : 0.00
% 2.90/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
