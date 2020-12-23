%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:46 EST 2020

% Result     : CounterSatisfiable 3.72s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:45:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.72/1.63  
% 3.72/1.63  % SZS status CounterSatisfiable for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.72/1.63  
% 3.72/1.63  Inference rules
% 3.72/1.63  ----------------------
% 3.72/1.63  #Ref     : 0
% 3.72/1.63  #Sup     : 351
% 3.72/1.63  #Fact    : 0
% 3.72/1.63  #Define  : 0
% 3.72/1.63  #Split   : 0
% 3.72/1.63  #Chain   : 0
% 3.72/1.63  #Close   : 0
% 3.72/1.63  
% 3.72/1.63  Ordering : KBO
% 3.72/1.63  
% 3.72/1.63  Simplification rules
% 3.72/1.63  ----------------------
% 3.72/1.63  #Subsume      : 14
% 3.72/1.63  #Demod        : 170
% 3.72/1.63  #Tautology    : 267
% 3.72/1.63  #SimpNegUnit  : 0
% 3.72/1.63  #BackRed      : 5
% 3.72/1.63  
% 3.72/1.63  #Partial instantiations: 0
% 3.72/1.63  #Strategies tried      : 1
% 3.72/1.63  
% 3.72/1.63  Timing (in seconds)
% 3.72/1.63  ----------------------
% 3.72/1.64  Preprocessing        : 0.35
% 3.72/1.64  Parsing              : 0.19
% 3.72/1.64  CNF conversion       : 0.02
% 3.72/1.64  Main loop            : 0.50
% 3.72/1.64  Inferencing          : 0.19
% 3.72/1.64  Reduction            : 0.18
% 3.72/1.64  Demodulation         : 0.14
% 3.72/1.64  BG Simplification    : 0.02
% 3.72/1.64  Subsumption          : 0.08
% 3.72/1.64  Abstraction          : 0.03
% 3.72/1.64  MUC search           : 0.00
% 3.72/1.64  Cooper               : 0.00
% 3.72/1.64  Total                : 0.86
% 3.72/1.64  Index Insertion      : 0.00
% 3.72/1.64  Index Deletion       : 0.00
% 3.72/1.64  Index Matching       : 0.00
% 3.72/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
