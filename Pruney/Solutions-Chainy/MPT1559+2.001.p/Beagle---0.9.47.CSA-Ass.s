%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:04 EST 2020

% Result     : CounterSatisfiable 1.62s
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
% 0.12/0.33  % Computer   : n002.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:41:36 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.62/1.05  
% 1.62/1.05  % SZS status CounterSatisfiable for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.62/1.05  
% 1.62/1.05  Inference rules
% 1.62/1.05  ----------------------
% 1.62/1.05  #Ref     : 0
% 1.62/1.05  #Sup     : 14
% 1.62/1.05  #Fact    : 0
% 1.62/1.05  #Define  : 0
% 1.62/1.05  #Split   : 0
% 1.62/1.05  #Chain   : 0
% 1.62/1.05  #Close   : 0
% 1.62/1.05  
% 1.62/1.05  Ordering : KBO
% 1.62/1.05  
% 1.62/1.05  Simplification rules
% 1.62/1.05  ----------------------
% 1.62/1.05  #Subsume      : 0
% 1.62/1.05  #Demod        : 5
% 1.62/1.05  #Tautology    : 13
% 1.62/1.05  #SimpNegUnit  : 0
% 1.62/1.05  #BackRed      : 0
% 1.62/1.05  
% 1.62/1.05  #Partial instantiations: 0
% 1.62/1.05  #Strategies tried      : 1
% 1.62/1.05  
% 1.62/1.05  Timing (in seconds)
% 1.62/1.05  ----------------------
% 1.62/1.05  Preprocessing        : 0.27
% 1.62/1.05  Parsing              : 0.15
% 1.62/1.05  CNF conversion       : 0.01
% 1.62/1.05  Main loop            : 0.11
% 1.62/1.05  Inferencing          : 0.03
% 1.62/1.05  Reduction            : 0.04
% 1.62/1.05  Demodulation         : 0.04
% 1.62/1.05  BG Simplification    : 0.01
% 1.62/1.05  Subsumption          : 0.02
% 1.62/1.05  Abstraction          : 0.00
% 1.62/1.05  MUC search           : 0.00
% 1.62/1.05  Cooper               : 0.00
% 1.62/1.05  Total                : 0.38
% 1.62/1.05  Index Insertion      : 0.00
% 1.62/1.05  Index Deletion       : 0.00
% 1.62/1.05  Index Matching       : 0.00
% 1.62/1.05  BG Taut test         : 0.00
%------------------------------------------------------------------------------
