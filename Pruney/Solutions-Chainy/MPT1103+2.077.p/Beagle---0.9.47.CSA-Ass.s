%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:40 EST 2020

% Result     : CounterSatisfiable 3.48s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:27:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.48/1.54  
% 3.48/1.54  % SZS status CounterSatisfiable for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.48/1.54  
% 3.48/1.54  Inference rules
% 3.48/1.54  ----------------------
% 3.48/1.54  #Ref     : 0
% 3.48/1.54  #Sup     : 296
% 3.48/1.54  #Fact    : 0
% 3.48/1.54  #Define  : 0
% 3.48/1.54  #Split   : 8
% 3.48/1.54  #Chain   : 0
% 3.48/1.54  #Close   : 0
% 3.48/1.54  
% 3.48/1.54  Ordering : KBO
% 3.48/1.54  
% 3.48/1.54  Simplification rules
% 3.48/1.54  ----------------------
% 3.48/1.54  #Subsume      : 16
% 3.48/1.54  #Demod        : 195
% 3.48/1.54  #Tautology    : 223
% 3.48/1.54  #SimpNegUnit  : 0
% 3.48/1.54  #BackRed      : 9
% 3.48/1.54  
% 3.48/1.54  #Partial instantiations: 0
% 3.48/1.54  #Strategies tried      : 1
% 3.48/1.54  
% 3.48/1.54  Timing (in seconds)
% 3.48/1.54  ----------------------
% 3.48/1.55  Preprocessing        : 0.36
% 3.48/1.55  Parsing              : 0.19
% 3.48/1.55  CNF conversion       : 0.02
% 3.48/1.55  Main loop            : 0.45
% 3.48/1.55  Inferencing          : 0.16
% 3.48/1.55  Reduction            : 0.16
% 3.48/1.55  Demodulation         : 0.12
% 3.48/1.55  BG Simplification    : 0.02
% 3.48/1.55  Subsumption          : 0.07
% 3.48/1.55  Abstraction          : 0.03
% 3.48/1.55  MUC search           : 0.00
% 3.48/1.55  Cooper               : 0.00
% 3.48/1.55  Total                : 0.81
% 3.48/1.55  Index Insertion      : 0.00
% 3.48/1.55  Index Deletion       : 0.00
% 3.48/1.55  Index Matching       : 0.00
% 3.48/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
