%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:37 EST 2020

% Result     : CounterSatisfiable 2.28s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:41:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.28/1.39  
% 2.28/1.39  % SZS status CounterSatisfiable for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.28/1.39  
% 2.28/1.39  Inference rules
% 2.28/1.39  ----------------------
% 2.28/1.39  #Ref     : 0
% 2.28/1.39  #Sup     : 44
% 2.28/1.39  #Fact    : 0
% 2.28/1.39  #Define  : 0
% 2.28/1.39  #Split   : 1
% 2.28/1.39  #Chain   : 0
% 2.28/1.39  #Close   : 0
% 2.28/1.39  
% 2.28/1.39  Ordering : KBO
% 2.28/1.39  
% 2.28/1.39  Simplification rules
% 2.28/1.39  ----------------------
% 2.28/1.39  #Subsume      : 1
% 2.28/1.39  #Demod        : 16
% 2.28/1.39  #Tautology    : 37
% 2.28/1.39  #SimpNegUnit  : 0
% 2.28/1.39  #BackRed      : 1
% 2.28/1.39  
% 2.28/1.39  #Partial instantiations: 0
% 2.28/1.39  #Strategies tried      : 1
% 2.28/1.39  
% 2.28/1.39  Timing (in seconds)
% 2.28/1.39  ----------------------
% 2.28/1.40  Preprocessing        : 0.37
% 2.28/1.40  Parsing              : 0.20
% 2.28/1.40  CNF conversion       : 0.02
% 2.28/1.40  Main loop            : 0.21
% 2.28/1.40  Inferencing          : 0.08
% 2.28/1.40  Reduction            : 0.06
% 2.28/1.40  Demodulation         : 0.05
% 2.28/1.40  BG Simplification    : 0.01
% 2.28/1.40  Subsumption          : 0.03
% 2.28/1.40  Abstraction          : 0.01
% 2.28/1.40  MUC search           : 0.00
% 2.28/1.40  Cooper               : 0.00
% 2.28/1.40  Total                : 0.59
% 2.28/1.40  Index Insertion      : 0.00
% 2.28/1.40  Index Deletion       : 0.00
% 2.28/1.40  Index Matching       : 0.00
% 2.28/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
