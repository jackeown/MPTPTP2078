%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:53 EST 2020

% Result     : CounterSatisfiable 1.75s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:09:52 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.75/1.13  
% 1.75/1.13  % SZS status CounterSatisfiable for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.75/1.13  
% 1.75/1.13  Inference rules
% 1.75/1.13  ----------------------
% 1.75/1.13  #Ref     : 0
% 1.75/1.13  #Sup     : 31
% 1.75/1.13  #Fact    : 0
% 1.75/1.13  #Define  : 0
% 1.75/1.13  #Split   : 0
% 1.75/1.13  #Chain   : 0
% 1.75/1.13  #Close   : 0
% 1.75/1.13  
% 1.75/1.13  Ordering : KBO
% 1.75/1.13  
% 1.75/1.13  Simplification rules
% 1.75/1.13  ----------------------
% 1.75/1.13  #Subsume      : 0
% 1.75/1.13  #Demod        : 2
% 1.75/1.13  #Tautology    : 22
% 1.75/1.13  #SimpNegUnit  : 0
% 1.75/1.13  #BackRed      : 0
% 1.75/1.13  
% 1.75/1.13  #Partial instantiations: 0
% 1.75/1.13  #Strategies tried      : 1
% 1.75/1.13  
% 1.75/1.13  Timing (in seconds)
% 1.75/1.13  ----------------------
% 1.75/1.13  Preprocessing        : 0.30
% 1.75/1.13  Parsing              : 0.16
% 1.75/1.13  CNF conversion       : 0.02
% 1.75/1.13  Main loop            : 0.13
% 1.75/1.13  Inferencing          : 0.05
% 1.75/1.13  Reduction            : 0.04
% 1.75/1.13  Demodulation         : 0.03
% 1.75/1.13  BG Simplification    : 0.01
% 1.75/1.13  Subsumption          : 0.01
% 1.75/1.13  Abstraction          : 0.01
% 1.75/1.14  MUC search           : 0.00
% 1.75/1.14  Cooper               : 0.00
% 1.75/1.14  Total                : 0.44
% 1.75/1.14  Index Insertion      : 0.00
% 1.75/1.14  Index Deletion       : 0.00
% 1.75/1.14  Index Matching       : 0.00
% 1.75/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
