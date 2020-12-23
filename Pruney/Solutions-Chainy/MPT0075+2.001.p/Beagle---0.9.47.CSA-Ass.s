%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:29 EST 2020

% Result     : CounterSatisfiable 6.03s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:32:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.03/2.14  
% 6.03/2.14  % SZS status CounterSatisfiable for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.03/2.14  
% 6.03/2.14  Inference rules
% 6.03/2.14  ----------------------
% 6.03/2.14  #Ref     : 0
% 6.03/2.14  #Sup     : 1150
% 6.03/2.14  #Fact    : 0
% 6.03/2.14  #Define  : 0
% 6.03/2.14  #Split   : 6
% 6.03/2.14  #Chain   : 0
% 6.03/2.14  #Close   : 0
% 6.03/2.14  
% 6.03/2.14  Ordering : KBO
% 6.03/2.14  
% 6.03/2.14  Simplification rules
% 6.03/2.14  ----------------------
% 6.03/2.14  #Subsume      : 597
% 6.03/2.14  #Demod        : 608
% 6.03/2.14  #Tautology    : 349
% 6.03/2.14  #SimpNegUnit  : 12
% 6.03/2.14  #BackRed      : 0
% 6.03/2.14  
% 6.03/2.14  #Partial instantiations: 0
% 6.03/2.14  #Strategies tried      : 1
% 6.03/2.14  
% 6.03/2.14  Timing (in seconds)
% 6.03/2.14  ----------------------
% 6.03/2.14  Preprocessing        : 0.28
% 6.03/2.14  Parsing              : 0.15
% 6.03/2.14  CNF conversion       : 0.02
% 6.03/2.15  Main loop            : 1.13
% 6.03/2.15  Inferencing          : 0.35
% 6.03/2.15  Reduction            : 0.32
% 6.03/2.15  Demodulation         : 0.21
% 6.03/2.15  BG Simplification    : 0.03
% 6.03/2.15  Subsumption          : 0.37
% 6.03/2.15  Abstraction          : 0.04
% 6.03/2.15  MUC search           : 0.00
% 6.03/2.15  Cooper               : 0.00
% 6.03/2.15  Total                : 1.42
% 6.03/2.15  Index Insertion      : 0.00
% 6.03/2.15  Index Deletion       : 0.00
% 6.03/2.15  Index Matching       : 0.00
% 6.03/2.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
