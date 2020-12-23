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
% DateTime   : Thu Dec  3 10:18:49 EST 2020

% Result     : CounterSatisfiable 2.73s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:16:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.73/1.44  
% 2.73/1.44  % SZS status CounterSatisfiable for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.73/1.44  
% 2.73/1.44  Inference rules
% 2.73/1.44  ----------------------
% 2.73/1.44  #Ref     : 0
% 2.73/1.44  #Sup     : 203
% 2.73/1.44  #Fact    : 0
% 2.73/1.44  #Define  : 0
% 2.73/1.44  #Split   : 0
% 2.73/1.44  #Chain   : 0
% 2.73/1.44  #Close   : 0
% 2.73/1.44  
% 2.73/1.44  Ordering : KBO
% 2.73/1.44  
% 2.73/1.44  Simplification rules
% 2.73/1.44  ----------------------
% 2.73/1.44  #Subsume      : 18
% 2.73/1.44  #Demod        : 49
% 2.73/1.44  #Tautology    : 147
% 2.73/1.44  #SimpNegUnit  : 0
% 2.73/1.44  #BackRed      : 0
% 2.73/1.44  
% 2.73/1.44  #Partial instantiations: 0
% 2.73/1.44  #Strategies tried      : 1
% 2.73/1.44  
% 2.73/1.44  Timing (in seconds)
% 2.73/1.44  ----------------------
% 2.73/1.44  Preprocessing        : 0.32
% 2.73/1.44  Parsing              : 0.17
% 2.73/1.44  CNF conversion       : 0.02
% 2.73/1.44  Main loop            : 0.32
% 2.73/1.44  Inferencing          : 0.12
% 2.73/1.44  Reduction            : 0.12
% 2.73/1.44  Demodulation         : 0.09
% 2.73/1.44  BG Simplification    : 0.02
% 2.73/1.44  Subsumption          : 0.05
% 2.73/1.44  Abstraction          : 0.02
% 2.73/1.44  MUC search           : 0.00
% 2.73/1.44  Cooper               : 0.00
% 2.73/1.45  Total                : 0.65
% 2.73/1.45  Index Insertion      : 0.00
% 2.73/1.45  Index Deletion       : 0.00
% 2.73/1.45  Index Matching       : 0.00
% 2.73/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
