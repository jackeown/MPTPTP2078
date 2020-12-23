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
% DateTime   : Thu Dec  3 09:49:18 EST 2020

% Result     : CounterSatisfiable 2.52s
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
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:33:49 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.52/1.32  
% 2.52/1.32  % SZS status CounterSatisfiable for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.52/1.32  
% 2.52/1.32  Inference rules
% 2.52/1.32  ----------------------
% 2.52/1.32  #Ref     : 0
% 2.52/1.32  #Sup     : 86
% 2.52/1.32  #Fact    : 0
% 2.52/1.32  #Define  : 0
% 2.52/1.32  #Split   : 1
% 2.52/1.32  #Chain   : 0
% 2.52/1.32  #Close   : 0
% 2.52/1.32  
% 2.52/1.32  Ordering : KBO
% 2.52/1.32  
% 2.52/1.32  Simplification rules
% 2.52/1.32  ----------------------
% 2.52/1.32  #Subsume      : 4
% 2.52/1.32  #Demod        : 21
% 2.52/1.32  #Tautology    : 63
% 2.52/1.32  #SimpNegUnit  : 0
% 2.52/1.32  #BackRed      : 1
% 2.52/1.32  
% 2.52/1.32  #Partial instantiations: 0
% 2.52/1.32  #Strategies tried      : 1
% 2.52/1.32  
% 2.52/1.32  Timing (in seconds)
% 2.52/1.32  ----------------------
% 2.52/1.32  Preprocessing        : 0.34
% 2.52/1.32  Parsing              : 0.18
% 2.52/1.32  CNF conversion       : 0.02
% 2.52/1.32  Main loop            : 0.24
% 2.52/1.32  Inferencing          : 0.10
% 2.52/1.32  Reduction            : 0.07
% 2.52/1.32  Demodulation         : 0.05
% 2.52/1.32  BG Simplification    : 0.02
% 2.52/1.33  Subsumption          : 0.03
% 2.52/1.33  Abstraction          : 0.01
% 2.52/1.33  MUC search           : 0.00
% 2.52/1.33  Cooper               : 0.00
% 2.52/1.33  Total                : 0.59
% 2.52/1.33  Index Insertion      : 0.00
% 2.52/1.33  Index Deletion       : 0.00
% 2.52/1.33  Index Matching       : 0.00
% 2.52/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
