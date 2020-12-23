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
% DateTime   : Thu Dec  3 10:25:14 EST 2020

% Result     : CounterSatisfiable 1.57s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:41:15 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.57/1.21  
% 1.57/1.21  % SZS status CounterSatisfiable for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.57/1.21  
% 1.57/1.21  Inference rules
% 1.57/1.21  ----------------------
% 1.57/1.21  #Ref     : 0
% 1.57/1.21  #Sup     : 0
% 1.57/1.21  #Fact    : 0
% 1.57/1.21  #Define  : 0
% 1.57/1.21  #Split   : 4
% 1.57/1.21  #Chain   : 0
% 1.57/1.21  #Close   : 0
% 1.57/1.21  
% 1.57/1.21  Ordering : KBO
% 1.57/1.21  
% 1.57/1.21  Simplification rules
% 1.57/1.21  ----------------------
% 1.57/1.21  #Subsume      : 11
% 1.57/1.21  #Demod        : 1
% 1.57/1.21  #Tautology    : 1
% 1.57/1.21  #SimpNegUnit  : 0
% 1.57/1.21  #BackRed      : 0
% 1.57/1.21  
% 1.57/1.21  #Partial instantiations: 0
% 1.57/1.21  #Strategies tried      : 1
% 1.57/1.21  
% 1.57/1.21  Timing (in seconds)
% 1.57/1.21  ----------------------
% 1.57/1.21  Preprocessing        : 0.29
% 1.79/1.21  Parsing              : 0.16
% 1.79/1.21  CNF conversion       : 0.02
% 1.79/1.21  Main loop            : 0.10
% 1.79/1.21  Inferencing          : 0.02
% 1.79/1.21  Reduction            : 0.03
% 1.79/1.21  Demodulation         : 0.02
% 1.79/1.21  BG Simplification    : 0.01
% 1.79/1.21  Subsumption          : 0.03
% 1.79/1.22  Abstraction          : 0.00
% 1.79/1.22  MUC search           : 0.00
% 1.79/1.22  Cooper               : 0.00
% 1.79/1.22  Total                : 0.40
% 1.79/1.22  Index Insertion      : 0.00
% 1.79/1.22  Index Deletion       : 0.00
% 1.79/1.22  Index Matching       : 0.00
% 1.79/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
