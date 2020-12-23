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
% DateTime   : Thu Dec  3 09:51:41 EST 2020

% Result     : CounterSatisfiable 4.44s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:40:53 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.44/1.83  
% 4.44/1.84  % SZS status CounterSatisfiable for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.44/1.84  
% 4.44/1.84  Inference rules
% 4.44/1.84  ----------------------
% 4.44/1.84  #Ref     : 0
% 4.44/1.84  #Sup     : 952
% 4.44/1.84  #Fact    : 0
% 4.44/1.84  #Define  : 0
% 4.44/1.84  #Split   : 2
% 4.44/1.84  #Chain   : 0
% 4.44/1.84  #Close   : 0
% 4.44/1.84  
% 4.44/1.84  Ordering : KBO
% 4.44/1.84  
% 4.44/1.84  Simplification rules
% 4.44/1.84  ----------------------
% 4.44/1.84  #Subsume      : 422
% 4.44/1.84  #Demod        : 696
% 4.44/1.84  #Tautology    : 430
% 4.44/1.84  #SimpNegUnit  : 102
% 4.44/1.84  #BackRed      : 20
% 4.44/1.84  
% 4.44/1.84  #Partial instantiations: 0
% 4.44/1.84  #Strategies tried      : 1
% 4.44/1.84  
% 4.44/1.84  Timing (in seconds)
% 4.44/1.84  ----------------------
% 4.44/1.84  Preprocessing        : 0.32
% 4.44/1.84  Parsing              : 0.17
% 4.44/1.84  CNF conversion       : 0.02
% 4.44/1.84  Main loop            : 0.77
% 4.44/1.84  Inferencing          : 0.25
% 4.44/1.84  Reduction            : 0.31
% 4.44/1.84  Demodulation         : 0.24
% 4.44/1.84  BG Simplification    : 0.02
% 4.44/1.84  Subsumption          : 0.13
% 4.44/1.84  Abstraction          : 0.03
% 4.44/1.84  MUC search           : 0.00
% 4.44/1.84  Cooper               : 0.00
% 4.44/1.84  Total                : 1.10
% 4.44/1.84  Index Insertion      : 0.00
% 4.44/1.84  Index Deletion       : 0.00
% 4.44/1.84  Index Matching       : 0.00
% 4.44/1.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
