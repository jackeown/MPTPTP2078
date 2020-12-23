%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:56 EST 2020

% Result     : CounterSatisfiable 2.40s
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
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:19:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.40/1.76  
% 2.40/1.76  % SZS status CounterSatisfiable for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.40/1.76  
% 2.40/1.76  Inference rules
% 2.40/1.76  ----------------------
% 2.40/1.76  #Ref     : 6
% 2.40/1.76  #Sup     : 40
% 2.40/1.76  #Fact    : 0
% 2.40/1.76  #Define  : 0
% 2.40/1.76  #Split   : 0
% 2.40/1.76  #Chain   : 0
% 2.40/1.76  #Close   : 0
% 2.40/1.76  
% 2.40/1.76  Ordering : KBO
% 2.40/1.76  
% 2.40/1.76  Simplification rules
% 2.40/1.76  ----------------------
% 2.40/1.76  #Subsume      : 10
% 2.40/1.76  #Demod        : 54
% 2.40/1.76  #Tautology    : 23
% 2.40/1.76  #SimpNegUnit  : 3
% 2.40/1.76  #BackRed      : 5
% 2.40/1.76  
% 2.40/1.76  #Partial instantiations: 0
% 2.40/1.76  #Strategies tried      : 1
% 2.40/1.76  
% 2.40/1.76  Timing (in seconds)
% 2.40/1.76  ----------------------
% 2.40/1.76  Preprocessing        : 0.48
% 2.40/1.76  Parsing              : 0.25
% 2.40/1.76  CNF conversion       : 0.04
% 2.40/1.76  Main loop            : 0.36
% 2.40/1.76  Inferencing          : 0.14
% 2.40/1.76  Reduction            : 0.11
% 2.40/1.76  Demodulation         : 0.08
% 2.40/1.76  BG Simplification    : 0.02
% 2.40/1.77  Subsumption          : 0.07
% 2.40/1.77  Abstraction          : 0.02
% 2.40/1.77  MUC search           : 0.00
% 2.40/1.77  Cooper               : 0.00
% 2.40/1.77  Total                : 0.86
% 2.40/1.77  Index Insertion      : 0.00
% 2.40/1.77  Index Deletion       : 0.00
% 2.40/1.77  Index Matching       : 0.00
% 2.40/1.77  BG Taut test         : 0.00
%------------------------------------------------------------------------------
