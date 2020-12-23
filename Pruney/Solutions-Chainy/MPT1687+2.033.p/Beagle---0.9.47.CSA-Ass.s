%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:06 EST 2020

% Result     : CounterSatisfiable 13.11s
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
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:25:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.11/10.22  
% 13.11/10.22  % SZS status CounterSatisfiable for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.11/10.22  
% 13.11/10.22  Inference rules
% 13.11/10.22  ----------------------
% 13.11/10.22  #Ref     : 0
% 13.11/10.22  #Sup     : 79
% 13.11/10.22  #Fact    : 0
% 13.11/10.22  #Define  : 0
% 13.11/10.22  #Split   : 4
% 13.11/10.22  #Chain   : 0
% 13.11/10.22  #Close   : 0
% 13.11/10.22  
% 13.11/10.22  Ordering : KBO
% 13.11/10.22  
% 13.11/10.22  Simplification rules
% 13.11/10.22  ----------------------
% 13.11/10.22  #Subsume      : 25
% 13.11/10.22  #Demod        : 40
% 13.11/10.22  #Tautology    : 23
% 13.11/10.22  #SimpNegUnit  : 2
% 13.11/10.22  #BackRed      : 3
% 13.11/10.22  
% 13.11/10.22  #Partial instantiations: 0
% 13.11/10.22  #Strategies tried      : 1
% 13.11/10.22  
% 13.11/10.22  Timing (in seconds)
% 13.11/10.22  ----------------------
% 13.26/10.23  Preprocessing        : 0.33
% 13.26/10.23  Parsing              : 0.18
% 13.26/10.23  CNF conversion       : 0.02
% 13.26/10.23  Main loop            : 9.15
% 13.26/10.23  Inferencing          : 0.16
% 13.26/10.23  Reduction            : 0.11
% 13.26/10.23  Demodulation         : 0.08
% 13.26/10.23  BG Simplification    : 0.02
% 13.26/10.23  Subsumption          : 8.83
% 13.26/10.23  Abstraction          : 0.02
% 13.26/10.23  MUC search           : 0.00
% 13.26/10.23  Cooper               : 0.00
% 13.26/10.23  Total                : 9.49
% 13.26/10.23  Index Insertion      : 0.00
% 13.26/10.23  Index Deletion       : 0.00
% 13.26/10.23  Index Matching       : 0.00
% 13.26/10.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
