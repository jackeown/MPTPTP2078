%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:34 EST 2020

% Result     : CounterSatisfiable 4.10s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:38:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.10/1.74  
% 4.10/1.74  % SZS status CounterSatisfiable for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.10/1.74  
% 4.10/1.74  Inference rules
% 4.10/1.74  ----------------------
% 4.10/1.74  #Ref     : 0
% 4.10/1.74  #Sup     : 778
% 4.10/1.74  #Fact    : 0
% 4.10/1.74  #Define  : 0
% 4.10/1.74  #Split   : 4
% 4.10/1.74  #Chain   : 0
% 4.10/1.74  #Close   : 0
% 4.10/1.74  
% 4.10/1.74  Ordering : KBO
% 4.10/1.74  
% 4.10/1.74  Simplification rules
% 4.10/1.74  ----------------------
% 4.10/1.74  #Subsume      : 59
% 4.10/1.74  #Demod        : 970
% 4.10/1.74  #Tautology    : 640
% 4.10/1.74  #SimpNegUnit  : 0
% 4.10/1.74  #BackRed      : 3
% 4.10/1.74  
% 4.10/1.74  #Partial instantiations: 0
% 4.10/1.74  #Strategies tried      : 1
% 4.10/1.74  
% 4.10/1.74  Timing (in seconds)
% 4.10/1.74  ----------------------
% 4.10/1.74  Preprocessing        : 0.31
% 4.10/1.74  Parsing              : 0.17
% 4.10/1.75  CNF conversion       : 0.02
% 4.10/1.75  Main loop            : 0.67
% 4.10/1.75  Inferencing          : 0.20
% 4.10/1.75  Reduction            : 0.32
% 4.10/1.75  Demodulation         : 0.28
% 4.10/1.75  BG Simplification    : 0.02
% 4.10/1.75  Subsumption          : 0.08
% 4.10/1.75  Abstraction          : 0.04
% 4.10/1.75  MUC search           : 0.00
% 4.10/1.75  Cooper               : 0.00
% 4.10/1.75  Total                : 0.99
% 4.10/1.75  Index Insertion      : 0.00
% 4.10/1.75  Index Deletion       : 0.00
% 4.10/1.75  Index Matching       : 0.00
% 4.10/1.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
