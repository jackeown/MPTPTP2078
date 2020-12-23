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
% DateTime   : Thu Dec  3 10:18:40 EST 2020

% Result     : CounterSatisfiable 2.66s
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
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:01:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.66/1.42  
% 2.66/1.42  % SZS status CounterSatisfiable for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.66/1.42  
% 2.66/1.42  Inference rules
% 2.66/1.42  ----------------------
% 2.66/1.42  #Ref     : 0
% 2.66/1.42  #Sup     : 187
% 2.66/1.42  #Fact    : 0
% 2.66/1.42  #Define  : 0
% 2.66/1.42  #Split   : 6
% 2.66/1.42  #Chain   : 0
% 2.66/1.42  #Close   : 0
% 2.66/1.42  
% 2.66/1.42  Ordering : KBO
% 2.66/1.42  
% 2.66/1.42  Simplification rules
% 2.66/1.42  ----------------------
% 2.66/1.42  #Subsume      : 1
% 2.66/1.42  #Demod        : 82
% 2.66/1.42  #Tautology    : 144
% 2.66/1.42  #SimpNegUnit  : 0
% 2.66/1.42  #BackRed      : 4
% 2.66/1.42  
% 2.66/1.42  #Partial instantiations: 0
% 2.66/1.42  #Strategies tried      : 1
% 2.66/1.42  
% 2.66/1.42  Timing (in seconds)
% 2.66/1.42  ----------------------
% 2.66/1.43  Preprocessing        : 0.30
% 2.66/1.43  Parsing              : 0.16
% 2.66/1.43  CNF conversion       : 0.02
% 2.66/1.43  Main loop            : 0.32
% 2.66/1.43  Inferencing          : 0.12
% 2.66/1.43  Reduction            : 0.11
% 2.66/1.43  Demodulation         : 0.08
% 2.66/1.43  BG Simplification    : 0.02
% 2.66/1.43  Subsumption          : 0.05
% 2.66/1.43  Abstraction          : 0.02
% 2.66/1.43  MUC search           : 0.00
% 2.66/1.43  Cooper               : 0.00
% 2.66/1.43  Total                : 0.63
% 2.66/1.43  Index Insertion      : 0.00
% 2.66/1.43  Index Deletion       : 0.00
% 2.66/1.43  Index Matching       : 0.00
% 2.66/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
