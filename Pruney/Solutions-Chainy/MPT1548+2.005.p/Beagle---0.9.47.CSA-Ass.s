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
% DateTime   : Thu Dec  3 10:25:02 EST 2020

% Result     : CounterSatisfiable 1.69s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:55:50 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.69/1.10  
% 1.69/1.10  % SZS status CounterSatisfiable for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.69/1.10  
% 1.69/1.10  Inference rules
% 1.69/1.10  ----------------------
% 1.69/1.10  #Ref     : 6
% 1.69/1.10  #Sup     : 25
% 1.69/1.10  #Fact    : 0
% 1.69/1.10  #Define  : 0
% 1.69/1.10  #Split   : 0
% 1.69/1.10  #Chain   : 0
% 1.69/1.10  #Close   : 0
% 1.69/1.10  
% 1.69/1.10  Ordering : KBO
% 1.69/1.10  
% 1.69/1.10  Simplification rules
% 1.69/1.10  ----------------------
% 1.69/1.10  #Subsume      : 9
% 1.69/1.10  #Demod        : 29
% 1.69/1.10  #Tautology    : 18
% 1.69/1.10  #SimpNegUnit  : 0
% 1.69/1.10  #BackRed      : 5
% 1.69/1.10  
% 1.69/1.10  #Partial instantiations: 0
% 1.69/1.10  #Strategies tried      : 1
% 1.69/1.10  
% 1.69/1.10  Timing (in seconds)
% 1.69/1.10  ----------------------
% 1.69/1.10  Preprocessing        : 0.27
% 1.69/1.10  Parsing              : 0.15
% 1.69/1.10  CNF conversion       : 0.02
% 1.69/1.10  Main loop            : 0.14
% 1.69/1.10  Inferencing          : 0.05
% 1.69/1.10  Reduction            : 0.04
% 1.69/1.10  Demodulation         : 0.03
% 1.69/1.10  BG Simplification    : 0.01
% 1.69/1.10  Subsumption          : 0.03
% 1.69/1.10  Abstraction          : 0.01
% 1.69/1.10  MUC search           : 0.00
% 1.69/1.10  Cooper               : 0.00
% 1.69/1.10  Total                : 0.42
% 1.69/1.10  Index Insertion      : 0.00
% 1.69/1.10  Index Deletion       : 0.00
% 1.69/1.10  Index Matching       : 0.00
% 1.69/1.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
