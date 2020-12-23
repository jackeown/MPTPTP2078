%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:00 EST 2020

% Result     : CounterSatisfiable 2.19s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:47:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.19/1.25  
% 2.19/1.26  % SZS status CounterSatisfiable for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.26  
% 2.19/1.26  Inference rules
% 2.19/1.26  ----------------------
% 2.19/1.26  #Ref     : 0
% 2.19/1.26  #Sup     : 27
% 2.19/1.26  #Fact    : 0
% 2.19/1.26  #Define  : 0
% 2.19/1.26  #Split   : 3
% 2.19/1.26  #Chain   : 0
% 2.19/1.26  #Close   : 0
% 2.19/1.26  
% 2.19/1.26  Ordering : KBO
% 2.19/1.26  
% 2.19/1.26  Simplification rules
% 2.19/1.26  ----------------------
% 2.19/1.26  #Subsume      : 2
% 2.19/1.26  #Demod        : 14
% 2.19/1.26  #Tautology    : 11
% 2.19/1.26  #SimpNegUnit  : 2
% 2.19/1.26  #BackRed      : 0
% 2.19/1.26  
% 2.19/1.26  #Partial instantiations: 0
% 2.19/1.26  #Strategies tried      : 1
% 2.19/1.26  
% 2.19/1.26  Timing (in seconds)
% 2.19/1.26  ----------------------
% 2.19/1.26  Preprocessing        : 0.29
% 2.19/1.26  Parsing              : 0.16
% 2.19/1.26  CNF conversion       : 0.02
% 2.19/1.26  Main loop            : 0.23
% 2.19/1.26  Inferencing          : 0.10
% 2.19/1.26  Reduction            : 0.06
% 2.19/1.26  Demodulation         : 0.04
% 2.19/1.26  BG Simplification    : 0.01
% 2.19/1.26  Subsumption          : 0.05
% 2.19/1.26  Abstraction          : 0.01
% 2.19/1.26  MUC search           : 0.00
% 2.19/1.26  Cooper               : 0.00
% 2.19/1.26  Total                : 0.53
% 2.19/1.26  Index Insertion      : 0.00
% 2.19/1.26  Index Deletion       : 0.00
% 2.19/1.26  Index Matching       : 0.00
% 2.19/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
