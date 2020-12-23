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
% DateTime   : Thu Dec  3 10:25:15 EST 2020

% Result     : CounterSatisfiable 1.58s
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
% 0.15/0.34  % Computer   : n004.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 19:58:08 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.15/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.58/1.03  
% 1.58/1.03  % SZS status CounterSatisfiable for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.58/1.03  
% 1.58/1.03  Inference rules
% 1.58/1.03  ----------------------
% 1.58/1.03  #Ref     : 0
% 1.58/1.03  #Sup     : 0
% 1.58/1.03  #Fact    : 0
% 1.58/1.03  #Define  : 0
% 1.58/1.03  #Split   : 1
% 1.58/1.03  #Chain   : 0
% 1.58/1.03  #Close   : 0
% 1.58/1.03  
% 1.58/1.03  Ordering : KBO
% 1.58/1.03  
% 1.58/1.03  Simplification rules
% 1.58/1.03  ----------------------
% 1.58/1.03  #Subsume      : 0
% 1.58/1.03  #Demod        : 0
% 1.58/1.03  #Tautology    : 0
% 1.58/1.03  #SimpNegUnit  : 0
% 1.58/1.03  #BackRed      : 0
% 1.58/1.03  
% 1.58/1.03  #Partial instantiations: 0
% 1.58/1.03  #Strategies tried      : 1
% 1.58/1.03  
% 1.58/1.03  Timing (in seconds)
% 1.58/1.03  ----------------------
% 1.58/1.03  Preprocessing        : 0.24
% 1.58/1.03  Parsing              : 0.13
% 1.58/1.03  CNF conversion       : 0.02
% 1.58/1.03  Main loop            : 0.05
% 1.58/1.04  Inferencing          : 0.01
% 1.58/1.04  Reduction            : 0.01
% 1.58/1.04  Demodulation         : 0.01
% 1.58/1.04  BG Simplification    : 0.01
% 1.58/1.04  Subsumption          : 0.00
% 1.58/1.04  Abstraction          : 0.00
% 1.58/1.04  MUC search           : 0.00
% 1.58/1.04  Cooper               : 0.00
% 1.58/1.04  Total                : 0.30
% 1.58/1.04  Index Insertion      : 0.00
% 1.58/1.04  Index Deletion       : 0.00
% 1.58/1.04  Index Matching       : 0.00
% 1.58/1.04  BG Taut test         : 0.00
%------------------------------------------------------------------------------
