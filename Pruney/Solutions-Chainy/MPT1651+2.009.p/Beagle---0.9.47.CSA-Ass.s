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
% DateTime   : Thu Dec  3 10:25:54 EST 2020

% Result     : CounterSatisfiable 1.97s
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
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:44:11 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.97/1.20  
% 1.97/1.20  % SZS status CounterSatisfiable for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.20  
% 1.97/1.20  Inference rules
% 1.97/1.20  ----------------------
% 1.97/1.20  #Ref     : 0
% 1.97/1.20  #Sup     : 8
% 1.97/1.20  #Fact    : 0
% 1.97/1.20  #Define  : 0
% 1.97/1.20  #Split   : 1
% 1.97/1.20  #Chain   : 0
% 1.97/1.20  #Close   : 0
% 1.97/1.20  
% 1.97/1.20  Ordering : KBO
% 1.97/1.20  
% 1.97/1.20  Simplification rules
% 1.97/1.20  ----------------------
% 1.97/1.20  #Subsume      : 1
% 1.97/1.20  #Demod        : 6
% 1.97/1.20  #Tautology    : 3
% 1.97/1.20  #SimpNegUnit  : 0
% 1.97/1.20  #BackRed      : 0
% 1.97/1.20  
% 1.97/1.20  #Partial instantiations: 0
% 1.97/1.20  #Strategies tried      : 1
% 1.97/1.20  
% 1.97/1.20  Timing (in seconds)
% 1.97/1.20  ----------------------
% 2.11/1.20  Preprocessing        : 0.29
% 2.11/1.20  Parsing              : 0.15
% 2.11/1.20  CNF conversion       : 0.02
% 2.11/1.20  Main loop            : 0.18
% 2.11/1.20  Inferencing          : 0.08
% 2.11/1.20  Reduction            : 0.04
% 2.11/1.20  Demodulation         : 0.03
% 2.11/1.20  BG Simplification    : 0.01
% 2.11/1.20  Subsumption          : 0.04
% 2.11/1.20  Abstraction          : 0.01
% 2.11/1.20  MUC search           : 0.00
% 2.11/1.20  Cooper               : 0.00
% 2.11/1.20  Total                : 0.47
% 2.11/1.20  Index Insertion      : 0.00
% 2.11/1.20  Index Deletion       : 0.00
% 2.11/1.20  Index Matching       : 0.00
% 2.11/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
