%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:07 EST 2020

% Result     : CounterSatisfiable 1.83s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 17:37:17 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.83/1.15  
% 1.83/1.15  % SZS status CounterSatisfiable for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.83/1.15  
% 1.83/1.15  Inference rules
% 1.83/1.15  ----------------------
% 1.83/1.15  #Ref     : 0
% 1.83/1.15  #Sup     : 12
% 1.83/1.15  #Fact    : 0
% 1.83/1.15  #Define  : 0
% 1.83/1.15  #Split   : 1
% 1.83/1.15  #Chain   : 0
% 1.83/1.15  #Close   : 0
% 1.83/1.15  
% 1.83/1.15  Ordering : KBO
% 1.83/1.15  
% 1.83/1.15  Simplification rules
% 1.83/1.15  ----------------------
% 1.83/1.15  #Subsume      : 0
% 1.83/1.15  #Demod        : 3
% 1.83/1.15  #Tautology    : 9
% 1.83/1.15  #SimpNegUnit  : 0
% 1.83/1.15  #BackRed      : 0
% 1.83/1.15  
% 1.83/1.15  #Partial instantiations: 0
% 1.83/1.15  #Strategies tried      : 1
% 1.83/1.15  
% 1.83/1.15  Timing (in seconds)
% 1.83/1.15  ----------------------
% 2.09/1.16  Preprocessing        : 0.29
% 2.09/1.16  Parsing              : 0.15
% 2.09/1.16  CNF conversion       : 0.02
% 2.09/1.16  Main loop            : 0.12
% 2.09/1.16  Inferencing          : 0.05
% 2.09/1.16  Reduction            : 0.04
% 2.09/1.16  Demodulation         : 0.03
% 2.09/1.16  BG Simplification    : 0.01
% 2.09/1.16  Subsumption          : 0.02
% 2.09/1.16  Abstraction          : 0.01
% 2.09/1.16  MUC search           : 0.00
% 2.09/1.16  Cooper               : 0.00
% 2.09/1.16  Total                : 0.42
% 2.09/1.16  Index Insertion      : 0.00
% 2.09/1.16  Index Deletion       : 0.00
% 2.09/1.16  Index Matching       : 0.00
% 2.09/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
