%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:35 EST 2020

% Result     : CounterSatisfiable 3.11s
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
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:29:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.11/1.43  
% 3.11/1.43  % SZS status CounterSatisfiable for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.11/1.43  
% 3.11/1.43  Inference rules
% 3.11/1.43  ----------------------
% 3.11/1.43  #Ref     : 0
% 3.11/1.43  #Sup     : 146
% 3.11/1.43  #Fact    : 0
% 3.11/1.43  #Define  : 0
% 3.11/1.43  #Split   : 25
% 3.11/1.43  #Chain   : 0
% 3.11/1.43  #Close   : 0
% 3.11/1.43  
% 3.11/1.43  Ordering : KBO
% 3.11/1.43  
% 3.11/1.43  Simplification rules
% 3.11/1.43  ----------------------
% 3.11/1.43  #Subsume      : 2
% 3.11/1.43  #Demod        : 157
% 3.11/1.43  #Tautology    : 71
% 3.11/1.43  #SimpNegUnit  : 48
% 3.11/1.43  #BackRed      : 11
% 3.11/1.43  
% 3.11/1.43  #Partial instantiations: 0
% 3.11/1.43  #Strategies tried      : 1
% 3.11/1.43  
% 3.11/1.43  Timing (in seconds)
% 3.11/1.43  ----------------------
% 3.11/1.43  Preprocessing        : 0.32
% 3.11/1.43  Parsing              : 0.17
% 3.11/1.43  CNF conversion       : 0.02
% 3.11/1.43  Main loop            : 0.36
% 3.11/1.43  Inferencing          : 0.13
% 3.11/1.43  Reduction            : 0.11
% 3.11/1.43  Demodulation         : 0.07
% 3.11/1.43  BG Simplification    : 0.02
% 3.11/1.43  Subsumption          : 0.07
% 3.11/1.43  Abstraction          : 0.02
% 3.11/1.43  MUC search           : 0.00
% 3.11/1.43  Cooper               : 0.00
% 3.11/1.43  Total                : 0.69
% 3.11/1.43  Index Insertion      : 0.00
% 3.11/1.44  Index Deletion       : 0.00
% 3.11/1.44  Index Matching       : 0.00
% 3.11/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
