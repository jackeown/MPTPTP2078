%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:52 EST 2020

% Result     : CounterSatisfiable 2.01s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:16:59 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.01/1.24  
% 2.01/1.24  % SZS status CounterSatisfiable for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.01/1.24  
% 2.01/1.24  Inference rules
% 2.01/1.24  ----------------------
% 2.01/1.24  #Ref     : 7
% 2.01/1.24  #Sup     : 34
% 2.01/1.24  #Fact    : 0
% 2.01/1.24  #Define  : 0
% 2.01/1.24  #Split   : 3
% 2.01/1.24  #Chain   : 0
% 2.01/1.24  #Close   : 0
% 2.01/1.24  
% 2.01/1.24  Ordering : KBO
% 2.01/1.24  
% 2.01/1.24  Simplification rules
% 2.01/1.24  ----------------------
% 2.01/1.24  #Subsume      : 9
% 2.01/1.24  #Demod        : 63
% 2.01/1.24  #Tautology    : 26
% 2.01/1.24  #SimpNegUnit  : 0
% 2.01/1.24  #BackRed      : 7
% 2.01/1.24  
% 2.01/1.24  #Partial instantiations: 0
% 2.01/1.24  #Strategies tried      : 1
% 2.01/1.24  
% 2.01/1.24  Timing (in seconds)
% 2.01/1.24  ----------------------
% 2.15/1.24  Preprocessing        : 0.28
% 2.15/1.24  Parsing              : 0.15
% 2.15/1.24  CNF conversion       : 0.02
% 2.15/1.24  Main loop            : 0.19
% 2.15/1.24  Inferencing          : 0.06
% 2.15/1.24  Reduction            : 0.06
% 2.15/1.24  Demodulation         : 0.05
% 2.15/1.24  BG Simplification    : 0.01
% 2.15/1.24  Subsumption          : 0.03
% 2.15/1.24  Abstraction          : 0.01
% 2.15/1.24  MUC search           : 0.00
% 2.15/1.24  Cooper               : 0.00
% 2.15/1.24  Total                : 0.48
% 2.15/1.24  Index Insertion      : 0.00
% 2.15/1.24  Index Deletion       : 0.00
% 2.15/1.25  Index Matching       : 0.00
% 2.15/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
