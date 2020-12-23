%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:55 EST 2020

% Result     : CounterSatisfiable 2.23s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.15  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.36  % Computer   : n022.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 12:00:56 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.23/1.30  
% 2.23/1.31  % SZS status CounterSatisfiable for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.31  
% 2.23/1.31  Inference rules
% 2.23/1.31  ----------------------
% 2.23/1.31  #Ref     : 0
% 2.23/1.31  #Sup     : 21
% 2.23/1.31  #Fact    : 0
% 2.23/1.31  #Define  : 0
% 2.23/1.31  #Split   : 1
% 2.23/1.31  #Chain   : 0
% 2.23/1.31  #Close   : 0
% 2.23/1.31  
% 2.23/1.31  Ordering : KBO
% 2.23/1.31  
% 2.23/1.31  Simplification rules
% 2.23/1.31  ----------------------
% 2.23/1.31  #Subsume      : 5
% 2.23/1.31  #Demod        : 2
% 2.23/1.31  #Tautology    : 2
% 2.23/1.31  #SimpNegUnit  : 1
% 2.23/1.31  #BackRed      : 0
% 2.23/1.31  
% 2.23/1.31  #Partial instantiations: 0
% 2.23/1.31  #Strategies tried      : 1
% 2.23/1.31  
% 2.23/1.31  Timing (in seconds)
% 2.23/1.31  ----------------------
% 2.50/1.31  Preprocessing        : 0.30
% 2.50/1.31  Parsing              : 0.16
% 2.50/1.31  CNF conversion       : 0.02
% 2.50/1.31  Main loop            : 0.24
% 2.50/1.31  Inferencing          : 0.11
% 2.50/1.31  Reduction            : 0.05
% 2.50/1.31  Demodulation         : 0.03
% 2.50/1.31  BG Simplification    : 0.02
% 2.50/1.31  Subsumption          : 0.05
% 2.50/1.31  Abstraction          : 0.01
% 2.50/1.31  MUC search           : 0.00
% 2.50/1.31  Cooper               : 0.00
% 2.50/1.31  Total                : 0.55
% 2.50/1.31  Index Insertion      : 0.00
% 2.50/1.31  Index Deletion       : 0.00
% 2.50/1.31  Index Matching       : 0.00
% 2.50/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
