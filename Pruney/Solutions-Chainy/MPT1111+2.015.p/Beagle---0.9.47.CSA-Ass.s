%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:00 EST 2020

% Result     : CounterSatisfiable 2.26s
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
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:05:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.26/1.33  
% 2.26/1.33  % SZS status CounterSatisfiable for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.26/1.33  
% 2.26/1.33  Inference rules
% 2.26/1.33  ----------------------
% 2.26/1.33  #Ref     : 0
% 2.26/1.33  #Sup     : 62
% 2.26/1.33  #Fact    : 0
% 2.26/1.33  #Define  : 0
% 2.26/1.33  #Split   : 2
% 2.26/1.33  #Chain   : 0
% 2.26/1.33  #Close   : 0
% 2.26/1.33  
% 2.26/1.33  Ordering : KBO
% 2.26/1.33  
% 2.26/1.33  Simplification rules
% 2.26/1.33  ----------------------
% 2.26/1.33  #Subsume      : 13
% 2.26/1.33  #Demod        : 24
% 2.26/1.33  #Tautology    : 19
% 2.26/1.33  #SimpNegUnit  : 7
% 2.26/1.33  #BackRed      : 12
% 2.26/1.33  
% 2.26/1.33  #Partial instantiations: 0
% 2.26/1.33  #Strategies tried      : 1
% 2.26/1.33  
% 2.26/1.33  Timing (in seconds)
% 2.26/1.33  ----------------------
% 2.26/1.33  Preprocessing        : 0.29
% 2.26/1.33  Parsing              : 0.16
% 2.26/1.33  CNF conversion       : 0.02
% 2.26/1.33  Main loop            : 0.30
% 2.26/1.33  Inferencing          : 0.12
% 2.26/1.33  Reduction            : 0.07
% 2.26/1.33  Demodulation         : 0.04
% 2.26/1.33  BG Simplification    : 0.01
% 2.26/1.33  Subsumption          : 0.06
% 2.26/1.33  Abstraction          : 0.01
% 2.26/1.33  MUC search           : 0.00
% 2.26/1.33  Cooper               : 0.00
% 2.57/1.33  Total                : 0.59
% 2.57/1.33  Index Insertion      : 0.00
% 2.57/1.33  Index Deletion       : 0.00
% 2.57/1.33  Index Matching       : 0.00
% 2.57/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
