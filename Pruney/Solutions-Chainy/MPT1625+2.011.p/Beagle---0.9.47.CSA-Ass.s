%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:45 EST 2020

% Result     : CounterSatisfiable 2.18s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.15  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.36  % Computer   : n022.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 10:11:26 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.18/1.29  
% 2.18/1.29  % SZS status CounterSatisfiable for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/1.29  
% 2.18/1.29  Inference rules
% 2.18/1.29  ----------------------
% 2.18/1.29  #Ref     : 0
% 2.18/1.29  #Sup     : 23
% 2.18/1.29  #Fact    : 0
% 2.18/1.29  #Define  : 0
% 2.18/1.29  #Split   : 3
% 2.18/1.29  #Chain   : 0
% 2.18/1.29  #Close   : 0
% 2.18/1.29  
% 2.18/1.29  Ordering : KBO
% 2.18/1.29  
% 2.18/1.29  Simplification rules
% 2.18/1.29  ----------------------
% 2.18/1.29  #Subsume      : 0
% 2.18/1.29  #Demod        : 17
% 2.18/1.29  #Tautology    : 13
% 2.18/1.29  #SimpNegUnit  : 5
% 2.18/1.29  #BackRed      : 1
% 2.18/1.29  
% 2.18/1.29  #Partial instantiations: 0
% 2.18/1.29  #Strategies tried      : 1
% 2.18/1.29  
% 2.18/1.29  Timing (in seconds)
% 2.18/1.29  ----------------------
% 2.18/1.29  Preprocessing        : 0.32
% 2.18/1.29  Parsing              : 0.17
% 2.18/1.29  CNF conversion       : 0.02
% 2.18/1.29  Main loop            : 0.16
% 2.18/1.29  Inferencing          : 0.06
% 2.18/1.29  Reduction            : 0.05
% 2.18/1.29  Demodulation         : 0.03
% 2.18/1.29  BG Simplification    : 0.01
% 2.18/1.29  Subsumption          : 0.03
% 2.18/1.29  Abstraction          : 0.01
% 2.18/1.29  MUC search           : 0.00
% 2.18/1.29  Cooper               : 0.00
% 2.18/1.29  Total                : 0.49
% 2.18/1.29  Index Insertion      : 0.00
% 2.18/1.29  Index Deletion       : 0.00
% 2.18/1.29  Index Matching       : 0.00
% 2.18/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
