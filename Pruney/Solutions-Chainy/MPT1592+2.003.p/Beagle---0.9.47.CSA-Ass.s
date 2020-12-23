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
% DateTime   : Thu Dec  3 10:25:19 EST 2020

% Result     : CounterSatisfiable 2.38s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:44:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.38/1.24  
% 2.38/1.25  % SZS status CounterSatisfiable for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.38/1.25  
% 2.38/1.25  Inference rules
% 2.38/1.25  ----------------------
% 2.38/1.25  #Ref     : 0
% 2.38/1.25  #Sup     : 27
% 2.38/1.25  #Fact    : 0
% 2.38/1.25  #Define  : 0
% 2.38/1.25  #Split   : 4
% 2.38/1.25  #Chain   : 0
% 2.38/1.25  #Close   : 0
% 2.38/1.25  
% 2.38/1.25  Ordering : KBO
% 2.38/1.25  
% 2.38/1.25  Simplification rules
% 2.38/1.25  ----------------------
% 2.38/1.25  #Subsume      : 0
% 2.38/1.25  #Demod        : 8
% 2.38/1.25  #Tautology    : 15
% 2.38/1.25  #SimpNegUnit  : 2
% 2.38/1.25  #BackRed      : 0
% 2.38/1.25  
% 2.38/1.25  #Partial instantiations: 0
% 2.38/1.25  #Strategies tried      : 1
% 2.38/1.25  
% 2.38/1.25  Timing (in seconds)
% 2.38/1.25  ----------------------
% 2.38/1.25  Preprocessing        : 0.32
% 2.38/1.25  Parsing              : 0.17
% 2.38/1.25  CNF conversion       : 0.03
% 2.38/1.25  Main loop            : 0.17
% 2.38/1.25  Inferencing          : 0.06
% 2.38/1.25  Reduction            : 0.05
% 2.38/1.25  Demodulation         : 0.04
% 2.38/1.25  BG Simplification    : 0.02
% 2.38/1.25  Subsumption          : 0.03
% 2.38/1.25  Abstraction          : 0.01
% 2.38/1.25  MUC search           : 0.00
% 2.38/1.25  Cooper               : 0.00
% 2.38/1.25  Total                : 0.50
% 2.38/1.25  Index Insertion      : 0.00
% 2.38/1.25  Index Deletion       : 0.00
% 2.38/1.25  Index Matching       : 0.00
% 2.38/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
