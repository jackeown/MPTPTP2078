%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:07 EST 2020

% Result     : CounterSatisfiable 1.75s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:17:34 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.75/1.12  
% 1.75/1.12  % SZS status CounterSatisfiable for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.75/1.12  
% 1.75/1.12  Inference rules
% 1.75/1.12  ----------------------
% 1.75/1.12  #Ref     : 0
% 1.75/1.12  #Sup     : 15
% 1.75/1.12  #Fact    : 0
% 1.75/1.12  #Define  : 0
% 1.75/1.12  #Split   : 1
% 1.75/1.12  #Chain   : 0
% 1.75/1.12  #Close   : 0
% 1.75/1.12  
% 1.75/1.12  Ordering : KBO
% 1.75/1.12  
% 1.75/1.12  Simplification rules
% 1.75/1.12  ----------------------
% 1.75/1.12  #Subsume      : 2
% 1.75/1.12  #Demod        : 9
% 1.75/1.12  #Tautology    : 10
% 1.75/1.12  #SimpNegUnit  : 0
% 1.75/1.12  #BackRed      : 0
% 1.75/1.12  
% 1.75/1.12  #Partial instantiations: 0
% 1.75/1.12  #Strategies tried      : 1
% 1.75/1.12  
% 1.75/1.12  Timing (in seconds)
% 1.75/1.12  ----------------------
% 1.75/1.12  Preprocessing        : 0.28
% 1.75/1.12  Parsing              : 0.16
% 1.75/1.12  CNF conversion       : 0.02
% 1.75/1.12  Main loop            : 0.13
% 1.75/1.12  Inferencing          : 0.05
% 1.75/1.12  Reduction            : 0.04
% 1.75/1.12  Demodulation         : 0.03
% 1.75/1.12  BG Simplification    : 0.01
% 1.75/1.12  Subsumption          : 0.02
% 1.75/1.12  Abstraction          : 0.00
% 1.75/1.12  MUC search           : 0.00
% 1.75/1.12  Cooper               : 0.00
% 1.75/1.12  Total                : 0.42
% 1.75/1.12  Index Insertion      : 0.00
% 1.75/1.12  Index Deletion       : 0.00
% 1.75/1.12  Index Matching       : 0.00
% 1.75/1.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
