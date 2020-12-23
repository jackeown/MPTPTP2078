%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:12 EST 2020

% Result     : CounterSatisfiable 2.60s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:05:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.60/1.37  
% 2.60/1.37  % SZS status CounterSatisfiable for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.60/1.37  
% 2.60/1.37  Inference rules
% 2.60/1.37  ----------------------
% 2.60/1.37  #Ref     : 0
% 2.60/1.37  #Sup     : 64
% 2.60/1.37  #Fact    : 0
% 2.60/1.37  #Define  : 0
% 2.60/1.37  #Split   : 1
% 2.60/1.37  #Chain   : 0
% 2.60/1.37  #Close   : 0
% 2.60/1.37  
% 2.60/1.37  Ordering : KBO
% 2.60/1.37  
% 2.60/1.37  Simplification rules
% 2.60/1.37  ----------------------
% 2.60/1.37  #Subsume      : 9
% 2.60/1.37  #Demod        : 0
% 2.60/1.37  #Tautology    : 26
% 2.60/1.37  #SimpNegUnit  : 0
% 2.60/1.37  #BackRed      : 0
% 2.60/1.37  
% 2.60/1.37  #Partial instantiations: 0
% 2.60/1.37  #Strategies tried      : 1
% 2.60/1.37  
% 2.60/1.37  Timing (in seconds)
% 2.60/1.37  ----------------------
% 2.60/1.37  Preprocessing        : 0.28
% 2.60/1.37  Parsing              : 0.16
% 2.60/1.37  CNF conversion       : 0.02
% 2.60/1.37  Main loop            : 0.35
% 2.60/1.37  Inferencing          : 0.14
% 2.60/1.37  Reduction            : 0.06
% 2.60/1.37  Demodulation         : 0.04
% 2.60/1.37  BG Simplification    : 0.02
% 2.60/1.37  Subsumption          : 0.11
% 2.60/1.37  Abstraction          : 0.01
% 2.60/1.37  MUC search           : 0.00
% 2.60/1.37  Cooper               : 0.00
% 2.60/1.37  Total                : 0.64
% 2.60/1.37  Index Insertion      : 0.00
% 2.60/1.37  Index Deletion       : 0.00
% 2.60/1.37  Index Matching       : 0.00
% 2.60/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
