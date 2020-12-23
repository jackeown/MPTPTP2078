%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:46 EST 2020

% Result     : CounterSatisfiable 7.76s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:10:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.76/2.79  
% 7.76/2.79  % SZS status CounterSatisfiable for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.76/2.79  
% 7.76/2.79  Inference rules
% 7.76/2.79  ----------------------
% 7.76/2.79  #Ref     : 0
% 7.76/2.79  #Sup     : 2290
% 7.76/2.79  #Fact    : 0
% 7.76/2.79  #Define  : 0
% 7.76/2.79  #Split   : 0
% 7.76/2.79  #Chain   : 0
% 7.76/2.79  #Close   : 0
% 7.76/2.79  
% 7.76/2.79  Ordering : KBO
% 7.76/2.79  
% 7.76/2.79  Simplification rules
% 7.76/2.79  ----------------------
% 7.76/2.79  #Subsume      : 677
% 7.76/2.79  #Demod        : 5665
% 7.76/2.79  #Tautology    : 1501
% 7.76/2.79  #SimpNegUnit  : 0
% 7.76/2.79  #BackRed      : 6
% 7.76/2.79  
% 7.76/2.79  #Partial instantiations: 0
% 7.76/2.79  #Strategies tried      : 1
% 7.76/2.79  
% 7.76/2.79  Timing (in seconds)
% 7.76/2.79  ----------------------
% 7.76/2.79  Preprocessing        : 0.33
% 7.76/2.79  Parsing              : 0.18
% 7.76/2.79  CNF conversion       : 0.02
% 7.76/2.79  Main loop            : 1.71
% 7.76/2.79  Inferencing          : 0.37
% 7.76/2.79  Reduction            : 1.07
% 7.76/2.79  Demodulation         : 0.96
% 7.76/2.79  BG Simplification    : 0.03
% 7.76/2.79  Subsumption          : 0.18
% 7.76/2.79  Abstraction          : 0.08
% 7.76/2.79  MUC search           : 0.00
% 7.76/2.79  Cooper               : 0.00
% 7.76/2.79  Total                : 2.05
% 7.76/2.79  Index Insertion      : 0.00
% 7.76/2.79  Index Deletion       : 0.00
% 7.76/2.79  Index Matching       : 0.00
% 7.76/2.79  BG Taut test         : 0.00
%------------------------------------------------------------------------------
