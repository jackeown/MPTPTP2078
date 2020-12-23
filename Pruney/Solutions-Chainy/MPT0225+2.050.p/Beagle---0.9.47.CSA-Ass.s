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
% DateTime   : Thu Dec  3 09:48:37 EST 2020

% Result     : CounterSatisfiable 2.01s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:35:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.01/1.31  
% 2.01/1.31  % SZS status CounterSatisfiable for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.01/1.31  
% 2.01/1.31  Inference rules
% 2.01/1.31  ----------------------
% 2.01/1.31  #Ref     : 0
% 2.01/1.31  #Sup     : 50
% 2.01/1.31  #Fact    : 0
% 2.01/1.31  #Define  : 0
% 2.01/1.31  #Split   : 3
% 2.01/1.31  #Chain   : 0
% 2.01/1.31  #Close   : 0
% 2.01/1.31  
% 2.01/1.31  Ordering : KBO
% 2.01/1.31  
% 2.01/1.31  Simplification rules
% 2.01/1.31  ----------------------
% 2.01/1.31  #Subsume      : 2
% 2.01/1.31  #Demod        : 5
% 2.01/1.31  #Tautology    : 40
% 2.01/1.31  #SimpNegUnit  : 3
% 2.01/1.31  #BackRed      : 0
% 2.01/1.31  
% 2.01/1.31  #Partial instantiations: 0
% 2.01/1.31  #Strategies tried      : 1
% 2.01/1.31  
% 2.01/1.31  Timing (in seconds)
% 2.01/1.31  ----------------------
% 2.01/1.32  Preprocessing        : 0.33
% 2.01/1.32  Parsing              : 0.18
% 2.01/1.32  CNF conversion       : 0.02
% 2.01/1.32  Main loop            : 0.17
% 2.01/1.32  Inferencing          : 0.07
% 2.01/1.32  Reduction            : 0.05
% 2.01/1.32  Demodulation         : 0.03
% 2.01/1.32  BG Simplification    : 0.02
% 2.01/1.32  Subsumption          : 0.02
% 2.01/1.32  Abstraction          : 0.01
% 2.01/1.32  MUC search           : 0.00
% 2.01/1.32  Cooper               : 0.00
% 2.01/1.32  Total                : 0.50
% 2.01/1.32  Index Insertion      : 0.00
% 2.01/1.32  Index Deletion       : 0.00
% 2.01/1.32  Index Matching       : 0.00
% 2.01/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
