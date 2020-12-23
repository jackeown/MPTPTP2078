%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:44 EST 2020

% Result     : CounterSatisfiable 3.26s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:06:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.26/1.58  
% 3.26/1.58  % SZS status CounterSatisfiable for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.26/1.58  
% 3.26/1.58  Inference rules
% 3.26/1.58  ----------------------
% 3.26/1.58  #Ref     : 6
% 3.26/1.58  #Sup     : 172
% 3.26/1.58  #Fact    : 0
% 3.26/1.58  #Define  : 0
% 3.26/1.58  #Split   : 2
% 3.26/1.58  #Chain   : 0
% 3.26/1.58  #Close   : 0
% 3.26/1.58  
% 3.26/1.58  Ordering : KBO
% 3.26/1.58  
% 3.26/1.58  Simplification rules
% 3.26/1.58  ----------------------
% 3.26/1.58  #Subsume      : 35
% 3.26/1.58  #Demod        : 311
% 3.26/1.58  #Tautology    : 109
% 3.26/1.58  #SimpNegUnit  : 1
% 3.26/1.58  #BackRed      : 7
% 3.26/1.58  
% 3.26/1.58  #Partial instantiations: 0
% 3.26/1.58  #Strategies tried      : 1
% 3.26/1.58  
% 3.26/1.58  Timing (in seconds)
% 3.26/1.58  ----------------------
% 3.26/1.58  Preprocessing        : 0.37
% 3.26/1.58  Parsing              : 0.20
% 3.26/1.58  CNF conversion       : 0.03
% 3.26/1.58  Main loop            : 0.44
% 3.26/1.58  Inferencing          : 0.16
% 3.26/1.58  Reduction            : 0.13
% 3.26/1.58  Demodulation         : 0.10
% 3.26/1.58  BG Simplification    : 0.02
% 3.26/1.59  Subsumption          : 0.09
% 3.26/1.59  Abstraction          : 0.02
% 3.26/1.59  MUC search           : 0.00
% 3.26/1.59  Cooper               : 0.00
% 3.26/1.59  Total                : 0.83
% 3.26/1.59  Index Insertion      : 0.00
% 3.26/1.59  Index Deletion       : 0.00
% 3.26/1.59  Index Matching       : 0.00
% 3.26/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
