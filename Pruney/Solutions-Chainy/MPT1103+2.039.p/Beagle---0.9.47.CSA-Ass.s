%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:36 EST 2020

% Result     : CounterSatisfiable 1.87s
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
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:30:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.87/1.33  
% 1.87/1.33  % SZS status CounterSatisfiable for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.33  
% 1.87/1.33  Inference rules
% 1.87/1.33  ----------------------
% 1.87/1.33  #Ref     : 0
% 1.87/1.33  #Sup     : 111
% 1.87/1.33  #Fact    : 0
% 1.87/1.33  #Define  : 0
% 1.87/1.33  #Split   : 2
% 1.87/1.33  #Chain   : 0
% 1.87/1.33  #Close   : 0
% 1.87/1.33  
% 1.87/1.33  Ordering : KBO
% 1.87/1.33  
% 1.87/1.33  Simplification rules
% 1.87/1.33  ----------------------
% 1.87/1.33  #Subsume      : 1
% 1.87/1.33  #Demod        : 38
% 1.87/1.33  #Tautology    : 85
% 1.87/1.33  #SimpNegUnit  : 2
% 1.87/1.33  #BackRed      : 2
% 1.87/1.33  
% 1.87/1.33  #Partial instantiations: 0
% 1.87/1.33  #Strategies tried      : 1
% 1.87/1.33  
% 1.87/1.33  Timing (in seconds)
% 1.87/1.33  ----------------------
% 1.87/1.33  Preprocessing        : 0.26
% 1.87/1.33  Parsing              : 0.14
% 1.87/1.33  CNF conversion       : 0.02
% 1.87/1.34  Main loop            : 0.23
% 1.87/1.34  Inferencing          : 0.09
% 1.87/1.34  Reduction            : 0.07
% 1.87/1.34  Demodulation         : 0.06
% 1.87/1.34  BG Simplification    : 0.01
% 1.87/1.34  Subsumption          : 0.03
% 1.87/1.34  Abstraction          : 0.01
% 1.87/1.34  MUC search           : 0.00
% 1.87/1.34  Cooper               : 0.00
% 1.87/1.34  Total                : 0.50
% 1.87/1.34  Index Insertion      : 0.00
% 1.87/1.34  Index Deletion       : 0.00
% 1.87/1.34  Index Matching       : 0.00
% 1.87/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
