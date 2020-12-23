%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:51 EST 2020

% Result     : CounterSatisfiable 2.22s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:53:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.22/1.28  
% 2.22/1.28  % SZS status CounterSatisfiable for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.22/1.28  
% 2.22/1.28  Inference rules
% 2.22/1.28  ----------------------
% 2.22/1.28  #Ref     : 0
% 2.22/1.28  #Sup     : 31
% 2.22/1.28  #Fact    : 0
% 2.22/1.28  #Define  : 0
% 2.22/1.28  #Split   : 1
% 2.22/1.28  #Chain   : 0
% 2.22/1.28  #Close   : 0
% 2.22/1.28  
% 2.22/1.28  Ordering : KBO
% 2.22/1.28  
% 2.22/1.28  Simplification rules
% 2.22/1.28  ----------------------
% 2.22/1.28  #Subsume      : 9
% 2.22/1.28  #Demod        : 38
% 2.22/1.28  #Tautology    : 4
% 2.22/1.28  #SimpNegUnit  : 0
% 2.22/1.28  #BackRed      : 0
% 2.22/1.28  
% 2.22/1.28  #Partial instantiations: 0
% 2.22/1.28  #Strategies tried      : 1
% 2.22/1.28  
% 2.22/1.28  Timing (in seconds)
% 2.22/1.28  ----------------------
% 2.22/1.28  Preprocessing        : 0.30
% 2.22/1.28  Parsing              : 0.17
% 2.22/1.28  CNF conversion       : 0.03
% 2.22/1.28  Main loop            : 0.24
% 2.22/1.28  Inferencing          : 0.10
% 2.22/1.28  Reduction            : 0.06
% 2.22/1.28  Demodulation         : 0.04
% 2.22/1.28  BG Simplification    : 0.02
% 2.22/1.28  Subsumption          : 0.05
% 2.22/1.28  Abstraction          : 0.01
% 2.22/1.28  MUC search           : 0.00
% 2.22/1.28  Cooper               : 0.00
% 2.22/1.29  Total                : 0.54
% 2.22/1.29  Index Insertion      : 0.00
% 2.22/1.29  Index Deletion       : 0.00
% 2.22/1.29  Index Matching       : 0.00
% 2.22/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
