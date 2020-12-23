%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:23 EST 2020

% Result     : CounterSatisfiable 1.76s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:41:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.76/1.22  
% 1.76/1.22  % SZS status CounterSatisfiable for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.76/1.23  
% 1.76/1.23  Inference rules
% 1.76/1.23  ----------------------
% 1.76/1.23  #Ref     : 0
% 1.76/1.23  #Sup     : 59
% 1.76/1.23  #Fact    : 0
% 1.76/1.23  #Define  : 0
% 1.76/1.23  #Split   : 0
% 1.76/1.23  #Chain   : 0
% 1.76/1.23  #Close   : 0
% 1.76/1.23  
% 1.76/1.23  Ordering : KBO
% 1.76/1.23  
% 1.76/1.23  Simplification rules
% 1.76/1.23  ----------------------
% 1.76/1.23  #Subsume      : 7
% 1.76/1.23  #Demod        : 12
% 1.92/1.23  #Tautology    : 44
% 1.92/1.23  #SimpNegUnit  : 0
% 1.92/1.23  #BackRed      : 0
% 1.92/1.23  
% 1.92/1.23  #Partial instantiations: 0
% 1.92/1.23  #Strategies tried      : 1
% 1.92/1.23  
% 1.92/1.23  Timing (in seconds)
% 1.92/1.23  ----------------------
% 1.92/1.23  Preprocessing        : 0.29
% 1.92/1.23  Parsing              : 0.16
% 1.92/1.23  CNF conversion       : 0.01
% 1.92/1.23  Main loop            : 0.15
% 1.92/1.23  Inferencing          : 0.06
% 1.92/1.23  Reduction            : 0.05
% 1.92/1.23  Demodulation         : 0.04
% 1.92/1.23  BG Simplification    : 0.01
% 1.92/1.23  Subsumption          : 0.02
% 1.92/1.23  Abstraction          : 0.01
% 1.92/1.23  MUC search           : 0.00
% 1.92/1.23  Cooper               : 0.00
% 1.92/1.23  Total                : 0.45
% 1.92/1.23  Index Insertion      : 0.00
% 1.92/1.23  Index Deletion       : 0.00
% 1.92/1.23  Index Matching       : 0.00
% 1.92/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
