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
% DateTime   : Thu Dec  3 10:18:49 EST 2020

% Result     : CounterSatisfiable 10.23s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:34:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.23/4.46  
% 10.23/4.46  % SZS status CounterSatisfiable for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.23/4.46  
% 10.23/4.46  Inference rules
% 10.23/4.46  ----------------------
% 10.23/4.46  #Ref     : 0
% 10.23/4.46  #Sup     : 6578
% 10.23/4.46  #Fact    : 0
% 10.23/4.46  #Define  : 0
% 10.23/4.46  #Split   : 2
% 10.23/4.46  #Chain   : 0
% 10.23/4.46  #Close   : 0
% 10.23/4.46  
% 10.23/4.46  Ordering : KBO
% 10.23/4.46  
% 10.23/4.46  Simplification rules
% 10.23/4.46  ----------------------
% 10.23/4.46  #Subsume      : 1008
% 10.23/4.46  #Demod        : 14069
% 10.23/4.46  #Tautology    : 5419
% 10.23/4.46  #SimpNegUnit  : 0
% 10.23/4.47  #BackRed      : 14
% 10.23/4.47  
% 10.23/4.47  #Partial instantiations: 0
% 10.23/4.47  #Strategies tried      : 1
% 10.23/4.47  
% 10.23/4.47  Timing (in seconds)
% 10.23/4.47  ----------------------
% 10.23/4.47  Preprocessing        : 0.31
% 10.23/4.47  Parsing              : 0.17
% 10.23/4.47  CNF conversion       : 0.02
% 10.23/4.47  Main loop            : 3.42
% 10.23/4.47  Inferencing          : 0.61
% 10.23/4.47  Reduction            : 2.24
% 10.23/4.47  Demodulation         : 2.05
% 10.23/4.47  BG Simplification    : 0.05
% 10.23/4.47  Subsumption          : 0.40
% 10.23/4.47  Abstraction          : 0.14
% 10.23/4.47  MUC search           : 0.00
% 10.23/4.47  Cooper               : 0.00
% 10.23/4.47  Total                : 3.74
% 10.23/4.47  Index Insertion      : 0.00
% 10.23/4.47  Index Deletion       : 0.00
% 10.23/4.47  Index Matching       : 0.00
% 10.23/4.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
