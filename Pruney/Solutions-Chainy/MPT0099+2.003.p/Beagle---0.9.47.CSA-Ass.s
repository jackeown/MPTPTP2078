%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:36 EST 2020

% Result     : CounterSatisfiable 1.37s
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
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:03:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.37/1.12  
% 1.37/1.12  % SZS status CounterSatisfiable for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.37/1.12  
% 1.37/1.12  Inference rules
% 1.37/1.12  ----------------------
% 1.37/1.12  #Ref     : 0
% 1.37/1.12  #Sup     : 4
% 1.37/1.12  #Fact    : 0
% 1.37/1.12  #Define  : 0
% 1.37/1.12  #Split   : 0
% 1.37/1.12  #Chain   : 0
% 1.37/1.12  #Close   : 0
% 1.37/1.12  
% 1.37/1.12  Ordering : KBO
% 1.37/1.12  
% 1.37/1.12  Simplification rules
% 1.37/1.12  ----------------------
% 1.37/1.12  #Subsume      : 0
% 1.37/1.12  #Demod        : 0
% 1.37/1.12  #Tautology    : 3
% 1.37/1.12  #SimpNegUnit  : 0
% 1.37/1.12  #BackRed      : 0
% 1.37/1.12  
% 1.37/1.12  #Partial instantiations: 0
% 1.37/1.12  #Strategies tried      : 1
% 1.37/1.12  
% 1.37/1.12  Timing (in seconds)
% 1.37/1.12  ----------------------
% 1.37/1.13  Preprocessing        : 0.22
% 1.37/1.13  Parsing              : 0.12
% 1.37/1.13  CNF conversion       : 0.01
% 1.37/1.13  Main loop            : 0.06
% 1.37/1.13  Inferencing          : 0.03
% 1.37/1.13  Reduction            : 0.01
% 1.37/1.13  Demodulation         : 0.01
% 1.37/1.13  BG Simplification    : 0.01
% 1.37/1.13  Subsumption          : 0.01
% 1.37/1.13  Abstraction          : 0.00
% 1.37/1.13  MUC search           : 0.00
% 1.37/1.13  Cooper               : 0.00
% 1.37/1.13  Total                : 0.29
% 1.37/1.13  Index Insertion      : 0.00
% 1.37/1.13  Index Deletion       : 0.00
% 1.37/1.13  Index Matching       : 0.00
% 1.37/1.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
