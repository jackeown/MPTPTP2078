%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:08 EST 2020

% Result     : CounterSatisfiable 3.16s
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
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:35:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.16/1.46  
% 3.16/1.46  % SZS status CounterSatisfiable for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.16/1.46  
% 3.16/1.46  Inference rules
% 3.16/1.46  ----------------------
% 3.16/1.46  #Ref     : 0
% 3.16/1.46  #Sup     : 191
% 3.16/1.46  #Fact    : 0
% 3.16/1.46  #Define  : 0
% 3.16/1.46  #Split   : 16
% 3.16/1.46  #Chain   : 0
% 3.16/1.46  #Close   : 0
% 3.16/1.46  
% 3.16/1.46  Ordering : KBO
% 3.16/1.46  
% 3.16/1.46  Simplification rules
% 3.16/1.46  ----------------------
% 3.16/1.46  #Subsume      : 121
% 3.16/1.46  #Demod        : 40
% 3.16/1.46  #Tautology    : 35
% 3.16/1.46  #SimpNegUnit  : 11
% 3.16/1.46  #BackRed      : 0
% 3.16/1.46  
% 3.16/1.46  #Partial instantiations: 0
% 3.16/1.46  #Strategies tried      : 1
% 3.16/1.46  
% 3.16/1.46  Timing (in seconds)
% 3.16/1.46  ----------------------
% 3.16/1.47  Preprocessing        : 0.29
% 3.22/1.47  Parsing              : 0.16
% 3.22/1.47  CNF conversion       : 0.02
% 3.22/1.47  Main loop            : 0.42
% 3.22/1.47  Inferencing          : 0.16
% 3.22/1.47  Reduction            : 0.10
% 3.22/1.47  Demodulation         : 0.06
% 3.22/1.47  BG Simplification    : 0.02
% 3.22/1.47  Subsumption          : 0.11
% 3.22/1.47  Abstraction          : 0.01
% 3.22/1.47  MUC search           : 0.00
% 3.22/1.47  Cooper               : 0.00
% 3.22/1.47  Total                : 0.72
% 3.22/1.47  Index Insertion      : 0.00
% 3.22/1.47  Index Deletion       : 0.00
% 3.22/1.47  Index Matching       : 0.00
% 3.22/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
