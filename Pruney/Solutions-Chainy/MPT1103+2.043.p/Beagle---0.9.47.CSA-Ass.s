%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:36 EST 2020

% Result     : CounterSatisfiable 3.07s
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
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:54:54 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.07/1.51  
% 3.07/1.51  % SZS status CounterSatisfiable for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.07/1.51  
% 3.07/1.51  Inference rules
% 3.07/1.51  ----------------------
% 3.07/1.51  #Ref     : 0
% 3.07/1.51  #Sup     : 202
% 3.07/1.51  #Fact    : 0
% 3.07/1.51  #Define  : 0
% 3.07/1.51  #Split   : 7
% 3.07/1.51  #Chain   : 0
% 3.07/1.51  #Close   : 0
% 3.07/1.51  
% 3.07/1.51  Ordering : KBO
% 3.07/1.51  
% 3.07/1.51  Simplification rules
% 3.07/1.51  ----------------------
% 3.07/1.51  #Subsume      : 55
% 3.07/1.51  #Demod        : 33
% 3.07/1.51  #Tautology    : 87
% 3.07/1.51  #SimpNegUnit  : 5
% 3.07/1.51  #BackRed      : 2
% 3.07/1.51  
% 3.07/1.51  #Partial instantiations: 0
% 3.07/1.51  #Strategies tried      : 1
% 3.07/1.51  
% 3.07/1.51  Timing (in seconds)
% 3.07/1.51  ----------------------
% 3.07/1.51  Preprocessing        : 0.35
% 3.07/1.51  Parsing              : 0.18
% 3.07/1.51  CNF conversion       : 0.02
% 3.07/1.51  Main loop            : 0.42
% 3.07/1.51  Inferencing          : 0.16
% 3.07/1.51  Reduction            : 0.12
% 3.07/1.51  Demodulation         : 0.08
% 3.07/1.51  BG Simplification    : 0.02
% 3.07/1.51  Subsumption          : 0.08
% 3.07/1.51  Abstraction          : 0.02
% 3.07/1.51  MUC search           : 0.00
% 3.07/1.51  Cooper               : 0.00
% 3.07/1.51  Total                : 0.78
% 3.07/1.51  Index Insertion      : 0.00
% 3.07/1.51  Index Deletion       : 0.00
% 3.07/1.51  Index Matching       : 0.00
% 3.07/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
