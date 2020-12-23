%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:53 EST 2020

% Result     : CounterSatisfiable 2.02s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:12:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.02/1.24  
% 2.02/1.25  % SZS status CounterSatisfiable for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.25  
% 2.02/1.25  Inference rules
% 2.02/1.25  ----------------------
% 2.02/1.25  #Ref     : 0
% 2.02/1.25  #Sup     : 9
% 2.02/1.25  #Fact    : 0
% 2.02/1.25  #Define  : 0
% 2.02/1.25  #Split   : 1
% 2.02/1.25  #Chain   : 0
% 2.02/1.25  #Close   : 0
% 2.02/1.25  
% 2.02/1.25  Ordering : KBO
% 2.02/1.25  
% 2.02/1.25  Simplification rules
% 2.02/1.25  ----------------------
% 2.02/1.25  #Subsume      : 1
% 2.02/1.25  #Demod        : 11
% 2.02/1.25  #Tautology    : 3
% 2.02/1.25  #SimpNegUnit  : 0
% 2.02/1.25  #BackRed      : 0
% 2.02/1.25  
% 2.02/1.25  #Partial instantiations: 0
% 2.02/1.25  #Strategies tried      : 1
% 2.02/1.25  
% 2.02/1.25  Timing (in seconds)
% 2.02/1.25  ----------------------
% 2.02/1.25  Preprocessing        : 0.28
% 2.02/1.25  Parsing              : 0.16
% 2.02/1.25  CNF conversion       : 0.02
% 2.02/1.25  Main loop            : 0.16
% 2.02/1.25  Inferencing          : 0.07
% 2.02/1.25  Reduction            : 0.04
% 2.02/1.25  Demodulation         : 0.03
% 2.02/1.25  BG Simplification    : 0.01
% 2.02/1.25  Subsumption          : 0.03
% 2.02/1.25  Abstraction          : 0.01
% 2.02/1.25  MUC search           : 0.00
% 2.02/1.25  Cooper               : 0.00
% 2.02/1.25  Total                : 0.45
% 2.02/1.25  Index Insertion      : 0.00
% 2.02/1.25  Index Deletion       : 0.00
% 2.02/1.25  Index Matching       : 0.00
% 2.02/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
