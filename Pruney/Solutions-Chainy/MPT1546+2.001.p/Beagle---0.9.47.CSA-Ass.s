%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:00 EST 2020

% Result     : CounterSatisfiable 2.94s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n020.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 14:57:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.94/1.42  
% 2.94/1.42  % SZS status CounterSatisfiable for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.94/1.42  
% 2.94/1.42  Inference rules
% 2.94/1.42  ----------------------
% 2.94/1.42  #Ref     : 0
% 2.94/1.42  #Sup     : 113
% 2.94/1.42  #Fact    : 0
% 2.94/1.42  #Define  : 0
% 2.94/1.42  #Split   : 5
% 2.94/1.42  #Chain   : 0
% 2.94/1.42  #Close   : 0
% 2.94/1.42  
% 2.94/1.42  Ordering : KBO
% 2.94/1.42  
% 2.94/1.42  Simplification rules
% 2.94/1.42  ----------------------
% 2.94/1.42  #Subsume      : 39
% 2.94/1.42  #Demod        : 22
% 2.94/1.42  #Tautology    : 19
% 2.94/1.42  #SimpNegUnit  : 1
% 2.94/1.42  #BackRed      : 0
% 2.94/1.42  
% 2.94/1.42  #Partial instantiations: 0
% 2.94/1.42  #Strategies tried      : 1
% 2.94/1.42  
% 2.94/1.42  Timing (in seconds)
% 2.94/1.42  ----------------------
% 2.94/1.42  Preprocessing        : 0.29
% 2.94/1.42  Parsing              : 0.16
% 2.94/1.42  CNF conversion       : 0.02
% 2.94/1.42  Main loop            : 0.38
% 2.94/1.42  Inferencing          : 0.16
% 2.94/1.42  Reduction            : 0.09
% 2.94/1.42  Demodulation         : 0.05
% 2.94/1.42  BG Simplification    : 0.02
% 2.94/1.43  Subsumption          : 0.08
% 2.94/1.43  Abstraction          : 0.02
% 2.94/1.43  MUC search           : 0.00
% 2.94/1.43  Cooper               : 0.00
% 2.94/1.43  Total                : 0.68
% 2.94/1.43  Index Insertion      : 0.00
% 2.94/1.43  Index Deletion       : 0.00
% 2.94/1.43  Index Matching       : 0.00
% 2.94/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
