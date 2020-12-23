%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:14 EST 2020

% Result     : CounterSatisfiable 2.35s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:51:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.35/1.63  
% 2.35/1.63  % SZS status CounterSatisfiable for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.35/1.63  
% 2.35/1.63  Inference rules
% 2.35/1.63  ----------------------
% 2.35/1.63  #Ref     : 0
% 2.35/1.63  #Sup     : 65
% 2.35/1.63  #Fact    : 0
% 2.35/1.63  #Define  : 0
% 2.35/1.63  #Split   : 0
% 2.35/1.63  #Chain   : 0
% 2.35/1.63  #Close   : 0
% 2.35/1.63  
% 2.35/1.63  Ordering : KBO
% 2.35/1.63  
% 2.35/1.63  Simplification rules
% 2.35/1.63  ----------------------
% 2.35/1.63  #Subsume      : 12
% 2.35/1.63  #Demod        : 30
% 2.35/1.63  #Tautology    : 41
% 2.35/1.63  #SimpNegUnit  : 1
% 2.35/1.63  #BackRed      : 2
% 2.35/1.63  
% 2.35/1.63  #Partial instantiations: 0
% 2.35/1.63  #Strategies tried      : 1
% 2.35/1.63  
% 2.35/1.63  Timing (in seconds)
% 2.35/1.63  ----------------------
% 2.35/1.64  Preprocessing        : 0.45
% 2.35/1.64  Parsing              : 0.24
% 2.35/1.64  CNF conversion       : 0.03
% 2.35/1.64  Main loop            : 0.29
% 2.35/1.64  Inferencing          : 0.12
% 2.35/1.64  Reduction            : 0.09
% 2.35/1.64  Demodulation         : 0.07
% 2.35/1.64  BG Simplification    : 0.02
% 2.35/1.64  Subsumption          : 0.04
% 2.52/1.64  Abstraction          : 0.01
% 2.52/1.64  MUC search           : 0.00
% 2.52/1.64  Cooper               : 0.00
% 2.52/1.64  Total                : 0.76
% 2.52/1.64  Index Insertion      : 0.00
% 2.52/1.64  Index Deletion       : 0.00
% 2.52/1.64  Index Matching       : 0.00
% 2.52/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
