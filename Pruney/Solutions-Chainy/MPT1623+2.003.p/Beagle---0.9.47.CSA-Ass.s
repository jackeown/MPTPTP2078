%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:43 EST 2020

% Result     : CounterSatisfiable 2.32s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n009.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:31:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.32/1.37  
% 2.32/1.38  % SZS status CounterSatisfiable for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/1.38  
% 2.32/1.38  Inference rules
% 2.32/1.38  ----------------------
% 2.32/1.38  #Ref     : 6
% 2.32/1.38  #Sup     : 24
% 2.32/1.38  #Fact    : 0
% 2.32/1.38  #Define  : 0
% 2.32/1.38  #Split   : 0
% 2.32/1.38  #Chain   : 0
% 2.32/1.38  #Close   : 0
% 2.32/1.38  
% 2.32/1.38  Ordering : KBO
% 2.32/1.38  
% 2.32/1.38  Simplification rules
% 2.32/1.38  ----------------------
% 2.32/1.38  #Subsume      : 7
% 2.32/1.38  #Demod        : 34
% 2.32/1.38  #Tautology    : 20
% 2.32/1.38  #SimpNegUnit  : 0
% 2.32/1.38  #BackRed      : 6
% 2.32/1.38  
% 2.32/1.38  #Partial instantiations: 0
% 2.32/1.38  #Strategies tried      : 1
% 2.32/1.38  
% 2.32/1.38  Timing (in seconds)
% 2.32/1.38  ----------------------
% 2.32/1.38  Preprocessing        : 0.37
% 2.32/1.38  Parsing              : 0.18
% 2.32/1.38  CNF conversion       : 0.04
% 2.32/1.38  Main loop            : 0.18
% 2.32/1.38  Inferencing          : 0.06
% 2.32/1.38  Reduction            : 0.06
% 2.32/1.38  Demodulation         : 0.05
% 2.32/1.38  BG Simplification    : 0.02
% 2.32/1.38  Subsumption          : 0.03
% 2.32/1.38  Abstraction          : 0.01
% 2.32/1.38  MUC search           : 0.00
% 2.32/1.38  Cooper               : 0.00
% 2.32/1.38  Total                : 0.56
% 2.32/1.38  Index Insertion      : 0.00
% 2.32/1.38  Index Deletion       : 0.00
% 2.32/1.38  Index Matching       : 0.00
% 2.32/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
