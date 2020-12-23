%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:05 EST 2020

% Result     : CounterSatisfiable 12.63s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:38:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.63/9.22  
% 12.63/9.22  % SZS status CounterSatisfiable for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.63/9.22  
% 12.63/9.22  Inference rules
% 12.63/9.22  ----------------------
% 12.63/9.22  #Ref     : 0
% 12.63/9.22  #Sup     : 160
% 12.63/9.22  #Fact    : 0
% 12.63/9.22  #Define  : 0
% 12.63/9.22  #Split   : 7
% 12.63/9.22  #Chain   : 0
% 12.63/9.22  #Close   : 0
% 12.63/9.22  
% 12.63/9.22  Ordering : KBO
% 12.63/9.22  
% 12.63/9.22  Simplification rules
% 12.63/9.22  ----------------------
% 12.63/9.22  #Subsume      : 41
% 12.63/9.22  #Demod        : 40
% 12.63/9.22  #Tautology    : 49
% 12.63/9.22  #SimpNegUnit  : 2
% 12.63/9.22  #BackRed      : 3
% 12.63/9.22  
% 12.63/9.22  #Partial instantiations: 0
% 12.63/9.22  #Strategies tried      : 1
% 12.63/9.22  
% 12.63/9.22  Timing (in seconds)
% 12.63/9.22  ----------------------
% 12.63/9.23  Preprocessing        : 0.34
% 12.63/9.23  Parsing              : 0.18
% 12.63/9.23  CNF conversion       : 0.02
% 12.63/9.23  Main loop            : 8.16
% 12.63/9.23  Inferencing          : 0.26
% 12.63/9.23  Reduction            : 0.17
% 12.63/9.23  Demodulation         : 0.12
% 12.63/9.23  BG Simplification    : 0.03
% 12.63/9.23  Subsumption          : 7.64
% 12.63/9.23  Abstraction          : 0.04
% 12.63/9.23  MUC search           : 0.00
% 12.63/9.23  Cooper               : 0.00
% 12.63/9.23  Total                : 8.50
% 12.63/9.23  Index Insertion      : 0.00
% 12.63/9.23  Index Deletion       : 0.00
% 12.63/9.23  Index Matching       : 0.00
% 12.63/9.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
