%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:02 EST 2020

% Result     : CounterSatisfiable 1.96s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:11:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.96/1.26  
% 1.96/1.26  % SZS status CounterSatisfiable for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.26  
% 1.96/1.26  Inference rules
% 1.96/1.26  ----------------------
% 1.96/1.26  #Ref     : 0
% 1.96/1.26  #Sup     : 26
% 1.96/1.26  #Fact    : 0
% 1.96/1.26  #Define  : 0
% 1.96/1.26  #Split   : 3
% 1.96/1.26  #Chain   : 0
% 1.96/1.26  #Close   : 0
% 1.96/1.26  
% 1.96/1.26  Ordering : KBO
% 1.96/1.26  
% 1.96/1.26  Simplification rules
% 1.96/1.26  ----------------------
% 1.96/1.26  #Subsume      : 0
% 1.96/1.26  #Demod        : 32
% 1.96/1.26  #Tautology    : 13
% 1.96/1.26  #SimpNegUnit  : 7
% 1.96/1.26  #BackRed      : 1
% 1.96/1.26  
% 1.96/1.26  #Partial instantiations: 0
% 1.96/1.26  #Strategies tried      : 1
% 1.96/1.26  
% 1.96/1.26  Timing (in seconds)
% 1.96/1.26  ----------------------
% 1.96/1.27  Preprocessing        : 0.31
% 1.96/1.27  Parsing              : 0.17
% 1.96/1.27  CNF conversion       : 0.02
% 1.96/1.27  Main loop            : 0.15
% 1.96/1.27  Inferencing          : 0.06
% 1.96/1.27  Reduction            : 0.05
% 1.96/1.27  Demodulation         : 0.03
% 1.96/1.27  BG Simplification    : 0.01
% 1.96/1.27  Subsumption          : 0.02
% 1.96/1.27  Abstraction          : 0.01
% 1.96/1.27  MUC search           : 0.00
% 1.96/1.27  Cooper               : 0.00
% 1.96/1.27  Total                : 0.46
% 1.96/1.27  Index Insertion      : 0.00
% 1.96/1.27  Index Deletion       : 0.00
% 1.96/1.27  Index Matching       : 0.00
% 1.96/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
