%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:39 EST 2020

% Result     : CounterSatisfiable 2.30s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:19:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.30/1.28  
% 2.30/1.28  % SZS status CounterSatisfiable for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.30/1.28  
% 2.30/1.28  Inference rules
% 2.30/1.28  ----------------------
% 2.30/1.28  #Ref     : 0
% 2.30/1.28  #Sup     : 114
% 2.30/1.28  #Fact    : 0
% 2.30/1.28  #Define  : 0
% 2.30/1.28  #Split   : 1
% 2.30/1.28  #Chain   : 0
% 2.30/1.28  #Close   : 0
% 2.30/1.28  
% 2.30/1.28  Ordering : KBO
% 2.30/1.28  
% 2.30/1.28  Simplification rules
% 2.30/1.28  ----------------------
% 2.30/1.28  #Subsume      : 0
% 2.30/1.28  #Demod        : 38
% 2.30/1.28  #Tautology    : 93
% 2.30/1.28  #SimpNegUnit  : 2
% 2.30/1.28  #BackRed      : 6
% 2.30/1.28  
% 2.30/1.28  #Partial instantiations: 0
% 2.30/1.28  #Strategies tried      : 1
% 2.30/1.28  
% 2.30/1.28  Timing (in seconds)
% 2.30/1.28  ----------------------
% 2.30/1.28  Preprocessing        : 0.29
% 2.30/1.28  Parsing              : 0.15
% 2.30/1.28  CNF conversion       : 0.02
% 2.30/1.28  Main loop            : 0.24
% 2.30/1.28  Inferencing          : 0.10
% 2.30/1.28  Reduction            : 0.08
% 2.30/1.28  Demodulation         : 0.06
% 2.30/1.28  BG Simplification    : 0.01
% 2.30/1.28  Subsumption          : 0.03
% 2.30/1.28  Abstraction          : 0.02
% 2.30/1.28  MUC search           : 0.00
% 2.30/1.28  Cooper               : 0.00
% 2.30/1.28  Total                : 0.54
% 2.30/1.28  Index Insertion      : 0.00
% 2.30/1.28  Index Deletion       : 0.00
% 2.30/1.28  Index Matching       : 0.00
% 2.30/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
