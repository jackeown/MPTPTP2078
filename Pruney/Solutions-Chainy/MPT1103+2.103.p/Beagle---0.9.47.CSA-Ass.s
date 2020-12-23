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
% DateTime   : Thu Dec  3 10:18:42 EST 2020

% Result     : CounterSatisfiable 2.31s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.36  % Computer   : n008.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 12:13:00 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.31/1.33  
% 2.31/1.33  % SZS status CounterSatisfiable for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.31/1.33  
% 2.31/1.33  Inference rules
% 2.31/1.33  ----------------------
% 2.31/1.33  #Ref     : 0
% 2.31/1.33  #Sup     : 90
% 2.31/1.33  #Fact    : 0
% 2.31/1.33  #Define  : 0
% 2.31/1.33  #Split   : 1
% 2.31/1.33  #Chain   : 0
% 2.31/1.33  #Close   : 0
% 2.31/1.33  
% 2.31/1.33  Ordering : KBO
% 2.31/1.33  
% 2.31/1.33  Simplification rules
% 2.31/1.33  ----------------------
% 2.31/1.33  #Subsume      : 2
% 2.31/1.33  #Demod        : 30
% 2.31/1.33  #Tautology    : 69
% 2.31/1.33  #SimpNegUnit  : 1
% 2.31/1.33  #BackRed      : 1
% 2.31/1.33  
% 2.31/1.33  #Partial instantiations: 0
% 2.31/1.33  #Strategies tried      : 1
% 2.31/1.33  
% 2.31/1.33  Timing (in seconds)
% 2.31/1.33  ----------------------
% 2.31/1.33  Preprocessing        : 0.31
% 2.31/1.33  Parsing              : 0.17
% 2.31/1.33  CNF conversion       : 0.02
% 2.31/1.33  Main loop            : 0.23
% 2.31/1.33  Inferencing          : 0.09
% 2.31/1.33  Reduction            : 0.07
% 2.31/1.33  Demodulation         : 0.05
% 2.31/1.33  BG Simplification    : 0.01
% 2.31/1.33  Subsumption          : 0.03
% 2.31/1.34  Abstraction          : 0.02
% 2.31/1.34  MUC search           : 0.00
% 2.31/1.34  Cooper               : 0.00
% 2.31/1.34  Total                : 0.55
% 2.31/1.34  Index Insertion      : 0.00
% 2.31/1.34  Index Deletion       : 0.00
% 2.31/1.34  Index Matching       : 0.00
% 2.31/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
