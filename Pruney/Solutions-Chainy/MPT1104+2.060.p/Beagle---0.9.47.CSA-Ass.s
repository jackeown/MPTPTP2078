%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:49 EST 2020

% Result     : CounterSatisfiable 6.86s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:50:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.86/2.57  
% 6.86/2.57  % SZS status CounterSatisfiable for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.86/2.57  
% 6.86/2.57  Inference rules
% 6.86/2.57  ----------------------
% 6.86/2.57  #Ref     : 5
% 6.86/2.57  #Sup     : 1532
% 6.86/2.57  #Fact    : 0
% 6.86/2.57  #Define  : 0
% 6.86/2.57  #Split   : 2
% 6.86/2.57  #Chain   : 0
% 6.86/2.57  #Close   : 0
% 6.86/2.57  
% 6.86/2.57  Ordering : KBO
% 6.86/2.57  
% 6.86/2.57  Simplification rules
% 6.86/2.57  ----------------------
% 6.86/2.57  #Subsume      : 446
% 6.86/2.57  #Demod        : 2418
% 6.86/2.57  #Tautology    : 992
% 6.86/2.57  #SimpNegUnit  : 39
% 6.86/2.57  #BackRed      : 2
% 6.86/2.57  
% 6.86/2.57  #Partial instantiations: 0
% 6.86/2.57  #Strategies tried      : 1
% 6.86/2.57  
% 6.86/2.57  Timing (in seconds)
% 6.86/2.57  ----------------------
% 6.86/2.57  Preprocessing        : 0.30
% 6.86/2.57  Parsing              : 0.16
% 6.86/2.57  CNF conversion       : 0.02
% 6.86/2.57  Main loop            : 1.53
% 6.86/2.57  Inferencing          : 0.45
% 6.86/2.57  Reduction            : 0.70
% 6.86/2.57  Demodulation         : 0.59
% 6.86/2.57  BG Simplification    : 0.06
% 6.86/2.57  Subsumption          : 0.26
% 6.86/2.57  Abstraction          : 0.10
% 6.86/2.57  MUC search           : 0.00
% 6.86/2.57  Cooper               : 0.00
% 6.86/2.57  Total                : 1.84
% 6.86/2.57  Index Insertion      : 0.00
% 6.86/2.57  Index Deletion       : 0.00
% 6.86/2.57  Index Matching       : 0.00
% 6.86/2.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
