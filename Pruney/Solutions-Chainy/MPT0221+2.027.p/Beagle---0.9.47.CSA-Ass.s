%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:15 EST 2020

% Result     : CounterSatisfiable 1.75s
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
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:54:10 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.75/1.21  
% 1.75/1.21  % SZS status CounterSatisfiable for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.75/1.21  
% 1.75/1.21  Inference rules
% 1.75/1.21  ----------------------
% 1.75/1.21  #Ref     : 0
% 1.75/1.21  #Sup     : 10
% 1.75/1.21  #Fact    : 0
% 1.75/1.21  #Define  : 0
% 1.75/1.21  #Split   : 0
% 1.75/1.21  #Chain   : 0
% 1.75/1.21  #Close   : 0
% 1.75/1.22  
% 1.75/1.22  Ordering : KBO
% 1.75/1.22  
% 1.75/1.22  Simplification rules
% 1.75/1.22  ----------------------
% 1.75/1.22  #Subsume      : 0
% 1.75/1.22  #Demod        : 4
% 1.75/1.22  #Tautology    : 10
% 1.75/1.22  #SimpNegUnit  : 0
% 1.75/1.22  #BackRed      : 1
% 1.75/1.22  
% 1.75/1.22  #Partial instantiations: 0
% 1.75/1.22  #Strategies tried      : 1
% 1.75/1.22  
% 1.75/1.22  Timing (in seconds)
% 1.75/1.22  ----------------------
% 1.75/1.22  Preprocessing        : 0.30
% 1.75/1.22  Parsing              : 0.15
% 1.75/1.22  CNF conversion       : 0.02
% 1.75/1.22  Main loop            : 0.07
% 1.75/1.22  Inferencing          : 0.02
% 1.75/1.22  Reduction            : 0.02
% 1.75/1.22  Demodulation         : 0.02
% 1.75/1.22  BG Simplification    : 0.01
% 1.75/1.22  Subsumption          : 0.01
% 1.75/1.22  Abstraction          : 0.00
% 1.75/1.22  MUC search           : 0.00
% 1.75/1.22  Cooper               : 0.00
% 1.75/1.22  Total                : 0.37
% 1.75/1.22  Index Insertion      : 0.00
% 1.75/1.22  Index Deletion       : 0.00
% 1.75/1.22  Index Matching       : 0.00
% 1.75/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
