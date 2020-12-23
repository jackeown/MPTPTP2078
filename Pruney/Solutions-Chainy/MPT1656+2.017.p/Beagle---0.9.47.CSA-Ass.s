%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:57 EST 2020

% Result     : CounterSatisfiable 2.45s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n016.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:11:04 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.45/1.36  
% 2.45/1.36  % SZS status CounterSatisfiable for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.45/1.36  
% 2.45/1.36  Inference rules
% 2.45/1.36  ----------------------
% 2.45/1.36  #Ref     : 0
% 2.45/1.36  #Sup     : 38
% 2.45/1.36  #Fact    : 0
% 2.45/1.36  #Define  : 0
% 2.45/1.36  #Split   : 3
% 2.45/1.36  #Chain   : 0
% 2.45/1.36  #Close   : 0
% 2.45/1.36  
% 2.45/1.36  Ordering : KBO
% 2.45/1.36  
% 2.45/1.36  Simplification rules
% 2.45/1.36  ----------------------
% 2.45/1.36  #Subsume      : 17
% 2.45/1.36  #Demod        : 41
% 2.45/1.36  #Tautology    : 6
% 2.45/1.36  #SimpNegUnit  : 2
% 2.45/1.36  #BackRed      : 0
% 2.45/1.36  
% 2.45/1.36  #Partial instantiations: 0
% 2.45/1.36  #Strategies tried      : 1
% 2.45/1.36  
% 2.45/1.36  Timing (in seconds)
% 2.45/1.36  ----------------------
% 2.45/1.37  Preprocessing        : 0.31
% 2.45/1.37  Parsing              : 0.17
% 2.45/1.37  CNF conversion       : 0.02
% 2.45/1.37  Main loop            : 0.28
% 2.45/1.37  Inferencing          : 0.11
% 2.45/1.37  Reduction            : 0.07
% 2.45/1.37  Demodulation         : 0.05
% 2.45/1.37  BG Simplification    : 0.01
% 2.45/1.37  Subsumption          : 0.07
% 2.45/1.37  Abstraction          : 0.01
% 2.45/1.37  MUC search           : 0.00
% 2.45/1.37  Cooper               : 0.00
% 2.45/1.37  Total                : 0.59
% 2.45/1.37  Index Insertion      : 0.00
% 2.45/1.37  Index Deletion       : 0.00
% 2.45/1.37  Index Matching       : 0.00
% 2.45/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
