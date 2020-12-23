%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:02 EST 2020

% Result     : CounterSatisfiable 2.12s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:38:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.12/1.33  
% 2.12/1.33  % SZS status CounterSatisfiable for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.12/1.33  
% 2.12/1.33  Inference rules
% 2.12/1.33  ----------------------
% 2.12/1.33  #Ref     : 0
% 2.12/1.33  #Sup     : 7
% 2.12/1.33  #Fact    : 2
% 2.12/1.33  #Define  : 0
% 2.12/1.33  #Split   : 1
% 2.12/1.33  #Chain   : 0
% 2.12/1.33  #Close   : 0
% 2.12/1.33  
% 2.12/1.33  Ordering : KBO
% 2.12/1.33  
% 2.12/1.33  Simplification rules
% 2.12/1.33  ----------------------
% 2.12/1.33  #Subsume      : 1
% 2.12/1.33  #Demod        : 2
% 2.12/1.33  #Tautology    : 10
% 2.12/1.33  #SimpNegUnit  : 3
% 2.12/1.33  #BackRed      : 0
% 2.12/1.33  
% 2.12/1.33  #Partial instantiations: 0
% 2.12/1.33  #Strategies tried      : 1
% 2.12/1.33  
% 2.12/1.33  Timing (in seconds)
% 2.12/1.33  ----------------------
% 2.12/1.33  Preprocessing        : 0.39
% 2.12/1.33  Parsing              : 0.21
% 2.12/1.33  CNF conversion       : 0.03
% 2.12/1.33  Main loop            : 0.16
% 2.12/1.33  Inferencing          : 0.07
% 2.12/1.33  Reduction            : 0.04
% 2.12/1.33  Demodulation         : 0.03
% 2.12/1.33  BG Simplification    : 0.01
% 2.12/1.33  Subsumption          : 0.02
% 2.12/1.33  Abstraction          : 0.01
% 2.12/1.33  MUC search           : 0.00
% 2.12/1.33  Cooper               : 0.00
% 2.12/1.33  Total                : 0.56
% 2.12/1.33  Index Insertion      : 0.00
% 2.12/1.33  Index Deletion       : 0.00
% 2.12/1.33  Index Matching       : 0.00
% 2.12/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
