%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:01 EST 2020

% Result     : CounterSatisfiable 2.03s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:27:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.03/1.41  
% 2.03/1.41  % SZS status CounterSatisfiable for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.41  
% 2.03/1.41  Inference rules
% 2.03/1.41  ----------------------
% 2.03/1.41  #Ref     : 0
% 2.03/1.41  #Sup     : 3
% 2.03/1.41  #Fact    : 0
% 2.03/1.41  #Define  : 0
% 2.03/1.41  #Split   : 2
% 2.03/1.41  #Chain   : 0
% 2.03/1.41  #Close   : 0
% 2.03/1.41  
% 2.03/1.41  Ordering : KBO
% 2.03/1.41  
% 2.03/1.41  Simplification rules
% 2.03/1.41  ----------------------
% 2.03/1.41  #Subsume      : 0
% 2.03/1.41  #Demod        : 7
% 2.03/1.41  #Tautology    : 2
% 2.03/1.41  #SimpNegUnit  : 1
% 2.03/1.41  #BackRed      : 0
% 2.03/1.41  
% 2.03/1.41  #Partial instantiations: 0
% 2.03/1.41  #Strategies tried      : 1
% 2.03/1.41  
% 2.03/1.41  Timing (in seconds)
% 2.03/1.41  ----------------------
% 2.03/1.41  Preprocessing        : 0.43
% 2.03/1.41  Parsing              : 0.24
% 2.03/1.41  CNF conversion       : 0.03
% 2.03/1.41  Main loop            : 0.18
% 2.03/1.41  Inferencing          : 0.08
% 2.03/1.41  Reduction            : 0.05
% 2.03/1.41  Demodulation         : 0.04
% 2.03/1.41  BG Simplification    : 0.02
% 2.03/1.41  Subsumption          : 0.02
% 2.03/1.42  Abstraction          : 0.01
% 2.03/1.42  MUC search           : 0.00
% 2.03/1.42  Cooper               : 0.00
% 2.03/1.42  Total                : 0.63
% 2.03/1.42  Index Insertion      : 0.00
% 2.03/1.42  Index Deletion       : 0.00
% 2.03/1.42  Index Matching       : 0.00
% 2.03/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
