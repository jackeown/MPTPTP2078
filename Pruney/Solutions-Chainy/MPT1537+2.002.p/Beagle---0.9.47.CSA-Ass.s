%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:59 EST 2020

% Result     : CounterSatisfiable 1.87s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:22:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.87/1.32  
% 1.87/1.32  % SZS status CounterSatisfiable for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.32  
% 1.87/1.32  Inference rules
% 1.87/1.32  ----------------------
% 1.87/1.32  #Ref     : 0
% 1.87/1.32  #Sup     : 0
% 1.87/1.32  #Fact    : 0
% 1.87/1.32  #Define  : 0
% 1.87/1.32  #Split   : 7
% 1.87/1.32  #Chain   : 0
% 1.87/1.32  #Close   : 0
% 1.87/1.32  
% 1.87/1.32  Ordering : KBO
% 1.87/1.32  
% 1.87/1.32  Simplification rules
% 1.87/1.32  ----------------------
% 1.87/1.32  #Subsume      : 5
% 2.05/1.32  #Demod        : 5
% 2.05/1.32  #Tautology    : 4
% 2.05/1.32  #SimpNegUnit  : 0
% 2.05/1.32  #BackRed      : 0
% 2.05/1.32  
% 2.05/1.32  #Partial instantiations: 0
% 2.05/1.32  #Strategies tried      : 1
% 2.05/1.32  
% 2.05/1.32  Timing (in seconds)
% 2.05/1.32  ----------------------
% 2.05/1.33  Preprocessing        : 0.39
% 2.05/1.33  Parsing              : 0.24
% 2.05/1.33  CNF conversion       : 0.02
% 2.05/1.33  Main loop            : 0.11
% 2.05/1.33  Inferencing          : 0.03
% 2.05/1.33  Reduction            : 0.03
% 2.05/1.33  Demodulation         : 0.02
% 2.05/1.33  BG Simplification    : 0.01
% 2.05/1.33  Subsumption          : 0.03
% 2.05/1.33  Abstraction          : 0.01
% 2.05/1.33  MUC search           : 0.00
% 2.05/1.33  Cooper               : 0.00
% 2.05/1.33  Total                : 0.52
% 2.05/1.33  Index Insertion      : 0.00
% 2.05/1.33  Index Deletion       : 0.00
% 2.05/1.33  Index Matching       : 0.00
% 2.05/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
