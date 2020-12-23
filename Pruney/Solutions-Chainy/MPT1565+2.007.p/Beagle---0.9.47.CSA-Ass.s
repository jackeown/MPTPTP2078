%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:12 EST 2020

% Result     : CounterSatisfiable 2.05s
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
% 0.14/0.33  % Computer   : n005.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 18:00:17 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.05/1.29  
% 2.05/1.29  % SZS status CounterSatisfiable for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.05/1.29  
% 2.05/1.29  Inference rules
% 2.05/1.29  ----------------------
% 2.05/1.29  #Ref     : 0
% 2.05/1.29  #Sup     : 19
% 2.05/1.29  #Fact    : 0
% 2.05/1.29  #Define  : 0
% 2.05/1.29  #Split   : 1
% 2.05/1.29  #Chain   : 0
% 2.05/1.29  #Close   : 0
% 2.05/1.29  
% 2.05/1.29  Ordering : KBO
% 2.05/1.29  
% 2.05/1.29  Simplification rules
% 2.05/1.29  ----------------------
% 2.05/1.29  #Subsume      : 0
% 2.05/1.29  #Demod        : 0
% 2.05/1.29  #Tautology    : 7
% 2.05/1.29  #SimpNegUnit  : 0
% 2.05/1.29  #BackRed      : 0
% 2.05/1.29  
% 2.05/1.29  #Partial instantiations: 0
% 2.05/1.29  #Strategies tried      : 1
% 2.05/1.29  
% 2.05/1.29  Timing (in seconds)
% 2.05/1.29  ----------------------
% 2.05/1.29  Preprocessing        : 0.30
% 2.05/1.29  Parsing              : 0.16
% 2.05/1.29  CNF conversion       : 0.02
% 2.05/1.29  Main loop            : 0.20
% 2.05/1.29  Inferencing          : 0.09
% 2.05/1.29  Reduction            : 0.04
% 2.05/1.29  Demodulation         : 0.02
% 2.05/1.29  BG Simplification    : 0.02
% 2.05/1.29  Subsumption          : 0.05
% 2.05/1.29  Abstraction          : 0.01
% 2.05/1.29  MUC search           : 0.00
% 2.05/1.29  Cooper               : 0.00
% 2.05/1.29  Total                : 0.51
% 2.05/1.29  Index Insertion      : 0.00
% 2.05/1.29  Index Deletion       : 0.00
% 2.05/1.30  Index Matching       : 0.00
% 2.05/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
