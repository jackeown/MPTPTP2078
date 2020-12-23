%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:07 EST 2020

% Result     : CounterSatisfiable 2.06s
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
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:34:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.06/1.46  
% 2.06/1.46  % SZS status CounterSatisfiable for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.46  
% 2.06/1.46  Inference rules
% 2.06/1.46  ----------------------
% 2.06/1.46  #Ref     : 0
% 2.06/1.46  #Sup     : 11
% 2.06/1.46  #Fact    : 0
% 2.06/1.46  #Define  : 0
% 2.06/1.46  #Split   : 1
% 2.06/1.46  #Chain   : 0
% 2.06/1.46  #Close   : 0
% 2.06/1.46  
% 2.06/1.46  Ordering : KBO
% 2.06/1.46  
% 2.06/1.46  Simplification rules
% 2.06/1.46  ----------------------
% 2.24/1.46  #Subsume      : 1
% 2.24/1.46  #Demod        : 6
% 2.24/1.46  #Tautology    : 7
% 2.24/1.46  #SimpNegUnit  : 0
% 2.24/1.46  #BackRed      : 0
% 2.24/1.46  
% 2.24/1.46  #Partial instantiations: 0
% 2.24/1.46  #Strategies tried      : 1
% 2.24/1.46  
% 2.24/1.46  Timing (in seconds)
% 2.24/1.46  ----------------------
% 2.24/1.47  Preprocessing        : 0.44
% 2.24/1.47  Parsing              : 0.24
% 2.24/1.47  CNF conversion       : 0.03
% 2.24/1.47  Main loop            : 0.19
% 2.24/1.47  Inferencing          : 0.07
% 2.24/1.47  Reduction            : 0.06
% 2.24/1.47  Demodulation         : 0.05
% 2.24/1.47  BG Simplification    : 0.01
% 2.24/1.47  Subsumption          : 0.03
% 2.24/1.47  Abstraction          : 0.01
% 2.24/1.47  MUC search           : 0.00
% 2.24/1.47  Cooper               : 0.00
% 2.24/1.47  Total                : 0.64
% 2.24/1.47  Index Insertion      : 0.00
% 2.24/1.47  Index Deletion       : 0.00
% 2.24/1.47  Index Matching       : 0.00
% 2.24/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
