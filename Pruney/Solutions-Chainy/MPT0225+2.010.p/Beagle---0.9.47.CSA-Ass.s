%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:32 EST 2020

% Result     : CounterSatisfiable 13.85s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:03:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.85/7.54  
% 13.85/7.54  % SZS status CounterSatisfiable for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.85/7.54  
% 13.85/7.54  Inference rules
% 13.85/7.54  ----------------------
% 13.85/7.54  #Ref     : 0
% 13.85/7.54  #Sup     : 8865
% 13.85/7.54  #Fact    : 0
% 13.85/7.54  #Define  : 0
% 13.85/7.54  #Split   : 2
% 13.85/7.54  #Chain   : 0
% 13.85/7.54  #Close   : 0
% 13.85/7.54  
% 13.85/7.54  Ordering : KBO
% 13.85/7.54  
% 13.85/7.54  Simplification rules
% 13.85/7.54  ----------------------
% 13.85/7.54  #Subsume      : 1609
% 13.85/7.54  #Demod        : 20982
% 13.85/7.54  #Tautology    : 7041
% 13.85/7.54  #SimpNegUnit  : 7
% 13.85/7.54  #BackRed      : 3
% 13.85/7.54  
% 13.85/7.54  #Partial instantiations: 0
% 13.85/7.54  #Strategies tried      : 1
% 13.85/7.54  
% 13.85/7.54  Timing (in seconds)
% 13.85/7.54  ----------------------
% 13.85/7.54  Preprocessing        : 0.36
% 13.85/7.54  Parsing              : 0.19
% 13.85/7.54  CNF conversion       : 0.02
% 13.85/7.54  Main loop            : 6.38
% 13.85/7.54  Inferencing          : 1.81
% 13.85/7.54  Reduction            : 3.79
% 13.85/7.54  Demodulation         : 3.49
% 13.85/7.54  BG Simplification    : 0.07
% 13.85/7.54  Subsumption          : 0.57
% 13.85/7.54  Abstraction          : 0.30
% 13.85/7.54  MUC search           : 0.00
% 13.85/7.54  Cooper               : 0.00
% 13.85/7.54  Total                : 6.75
% 13.85/7.54  Index Insertion      : 0.00
% 13.85/7.54  Index Deletion       : 0.00
% 13.85/7.54  Index Matching       : 0.00
% 13.85/7.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
