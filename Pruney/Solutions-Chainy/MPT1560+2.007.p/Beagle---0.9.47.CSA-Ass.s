%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:05 EST 2020

% Result     : CounterSatisfiable 2.26s
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
% 0.12/0.33  % Computer   : n019.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 09:50:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.26/1.23  
% 2.26/1.23  % SZS status CounterSatisfiable for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.26/1.23  
% 2.26/1.23  Inference rules
% 2.26/1.23  ----------------------
% 2.26/1.23  #Ref     : 0
% 2.26/1.23  #Sup     : 10
% 2.26/1.23  #Fact    : 0
% 2.26/1.23  #Define  : 0
% 2.26/1.23  #Split   : 3
% 2.26/1.23  #Chain   : 0
% 2.26/1.23  #Close   : 0
% 2.26/1.23  
% 2.26/1.23  Ordering : KBO
% 2.26/1.23  
% 2.26/1.23  Simplification rules
% 2.26/1.23  ----------------------
% 2.26/1.23  #Subsume      : 0
% 2.26/1.23  #Demod        : 12
% 2.26/1.23  #Tautology    : 3
% 2.26/1.23  #SimpNegUnit  : 4
% 2.26/1.23  #BackRed      : 0
% 2.26/1.23  
% 2.26/1.23  #Partial instantiations: 0
% 2.26/1.23  #Strategies tried      : 1
% 2.26/1.23  
% 2.26/1.23  Timing (in seconds)
% 2.26/1.23  ----------------------
% 2.26/1.23  Preprocessing        : 0.31
% 2.26/1.23  Parsing              : 0.16
% 2.26/1.23  CNF conversion       : 0.02
% 2.26/1.23  Main loop            : 0.16
% 2.26/1.23  Inferencing          : 0.06
% 2.26/1.23  Reduction            : 0.05
% 2.26/1.23  Demodulation         : 0.03
% 2.26/1.23  BG Simplification    : 0.01
% 2.26/1.23  Subsumption          : 0.02
% 2.26/1.23  Abstraction          : 0.01
% 2.26/1.23  MUC search           : 0.00
% 2.26/1.23  Cooper               : 0.00
% 2.26/1.23  Total                : 0.48
% 2.26/1.23  Index Insertion      : 0.00
% 2.26/1.23  Index Deletion       : 0.00
% 2.26/1.23  Index Matching       : 0.00
% 2.26/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
