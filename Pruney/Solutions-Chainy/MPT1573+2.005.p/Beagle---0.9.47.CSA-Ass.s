%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:15 EST 2020

% Result     : CounterSatisfiable 1.52s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:20:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.52/1.06  
% 1.52/1.06  % SZS status CounterSatisfiable for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.52/1.06  
% 1.52/1.06  Inference rules
% 1.52/1.06  ----------------------
% 1.52/1.06  #Ref     : 0
% 1.52/1.06  #Sup     : 2
% 1.52/1.06  #Fact    : 0
% 1.52/1.06  #Define  : 0
% 1.52/1.06  #Split   : 1
% 1.52/1.06  #Chain   : 0
% 1.52/1.06  #Close   : 0
% 1.52/1.06  
% 1.52/1.06  Ordering : KBO
% 1.52/1.06  
% 1.52/1.06  Simplification rules
% 1.52/1.06  ----------------------
% 1.52/1.06  #Subsume      : 0
% 1.52/1.06  #Demod        : 0
% 1.52/1.06  #Tautology    : 2
% 1.52/1.06  #SimpNegUnit  : 0
% 1.52/1.06  #BackRed      : 0
% 1.52/1.06  
% 1.52/1.06  #Partial instantiations: 0
% 1.52/1.06  #Strategies tried      : 1
% 1.52/1.06  
% 1.52/1.06  Timing (in seconds)
% 1.52/1.06  ----------------------
% 1.52/1.06  Preprocessing        : 0.26
% 1.52/1.06  Parsing              : 0.14
% 1.52/1.06  CNF conversion       : 0.02
% 1.52/1.06  Main loop            : 0.06
% 1.52/1.06  Inferencing          : 0.02
% 1.52/1.06  Reduction            : 0.01
% 1.52/1.06  Demodulation         : 0.01
% 1.52/1.06  BG Simplification    : 0.01
% 1.52/1.06  Subsumption          : 0.00
% 1.52/1.06  Abstraction          : 0.00
% 1.52/1.06  MUC search           : 0.00
% 1.52/1.06  Cooper               : 0.00
% 1.52/1.06  Total                : 0.33
% 1.52/1.06  Index Insertion      : 0.00
% 1.52/1.06  Index Deletion       : 0.00
% 1.52/1.06  Index Matching       : 0.00
% 1.52/1.06  BG Taut test         : 0.00
%------------------------------------------------------------------------------
