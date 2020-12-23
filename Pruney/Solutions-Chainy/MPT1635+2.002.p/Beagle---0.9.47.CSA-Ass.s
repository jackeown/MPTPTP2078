%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:46 EST 2020

% Result     : CounterSatisfiable 2.13s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n020.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 09:54:52 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.13/1.54  
% 2.13/1.54  % SZS status CounterSatisfiable for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.54  
% 2.13/1.54  Inference rules
% 2.13/1.54  ----------------------
% 2.13/1.54  #Ref     : 0
% 2.13/1.54  #Sup     : 21
% 2.13/1.54  #Fact    : 0
% 2.13/1.54  #Define  : 0
% 2.13/1.54  #Split   : 1
% 2.13/1.54  #Chain   : 0
% 2.13/1.54  #Close   : 0
% 2.13/1.54  
% 2.13/1.54  Ordering : KBO
% 2.13/1.54  
% 2.13/1.54  Simplification rules
% 2.13/1.54  ----------------------
% 2.13/1.54  #Subsume      : 8
% 2.13/1.54  #Demod        : 0
% 2.13/1.54  #Tautology    : 2
% 2.13/1.54  #SimpNegUnit  : 0
% 2.13/1.54  #BackRed      : 0
% 2.13/1.54  
% 2.13/1.54  #Partial instantiations: 0
% 2.13/1.54  #Strategies tried      : 1
% 2.13/1.54  
% 2.13/1.54  Timing (in seconds)
% 2.13/1.54  ----------------------
% 2.29/1.54  Preprocessing        : 0.42
% 2.29/1.54  Parsing              : 0.22
% 2.29/1.54  CNF conversion       : 0.03
% 2.29/1.54  Main loop            : 0.25
% 2.29/1.54  Inferencing          : 0.10
% 2.29/1.55  Reduction            : 0.05
% 2.29/1.55  Demodulation         : 0.04
% 2.29/1.55  BG Simplification    : 0.01
% 2.29/1.55  Subsumption          : 0.07
% 2.29/1.55  Abstraction          : 0.01
% 2.29/1.55  MUC search           : 0.00
% 2.29/1.55  Cooper               : 0.00
% 2.29/1.55  Total                : 0.68
% 2.29/1.55  Index Insertion      : 0.00
% 2.29/1.55  Index Deletion       : 0.00
% 2.29/1.55  Index Matching       : 0.00
% 2.29/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
