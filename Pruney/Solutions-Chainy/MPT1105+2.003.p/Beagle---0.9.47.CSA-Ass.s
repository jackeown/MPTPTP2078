%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:53 EST 2020

% Result     : CounterSatisfiable 1.51s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:36:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.51/1.07  
% 1.51/1.07  % SZS status CounterSatisfiable for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.51/1.07  
% 1.51/1.07  Inference rules
% 1.51/1.07  ----------------------
% 1.51/1.07  #Ref     : 0
% 1.51/1.07  #Sup     : 2
% 1.51/1.07  #Fact    : 0
% 1.51/1.07  #Define  : 0
% 1.51/1.07  #Split   : 0
% 1.51/1.07  #Chain   : 0
% 1.51/1.07  #Close   : 0
% 1.51/1.07  
% 1.51/1.07  Ordering : KBO
% 1.51/1.07  
% 1.51/1.07  Simplification rules
% 1.51/1.07  ----------------------
% 1.51/1.07  #Subsume      : 0
% 1.51/1.07  #Demod        : 0
% 1.51/1.07  #Tautology    : 2
% 1.51/1.07  #SimpNegUnit  : 0
% 1.51/1.07  #BackRed      : 0
% 1.51/1.07  
% 1.51/1.07  #Partial instantiations: 0
% 1.51/1.07  #Strategies tried      : 1
% 1.51/1.07  
% 1.51/1.07  Timing (in seconds)
% 1.51/1.07  ----------------------
% 1.51/1.07  Preprocessing        : 0.23
% 1.51/1.07  Parsing              : 0.12
% 1.51/1.07  CNF conversion       : 0.01
% 1.51/1.07  Main loop            : 0.04
% 1.51/1.07  Inferencing          : 0.02
% 1.51/1.07  Reduction            : 0.01
% 1.51/1.07  Demodulation         : 0.01
% 1.51/1.07  BG Simplification    : 0.01
% 1.51/1.07  Subsumption          : 0.00
% 1.51/1.07  Abstraction          : 0.01
% 1.51/1.07  MUC search           : 0.00
% 1.51/1.07  Cooper               : 0.00
% 1.51/1.07  Total                : 0.28
% 1.51/1.07  Index Insertion      : 0.00
% 1.51/1.07  Index Deletion       : 0.00
% 1.51/1.07  Index Matching       : 0.00
% 1.51/1.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------
