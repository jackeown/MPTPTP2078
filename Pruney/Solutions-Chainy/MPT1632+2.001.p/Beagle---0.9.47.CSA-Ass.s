%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:46 EST 2020

% Result     : CounterSatisfiable 1.94s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:33:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.94/1.43  
% 1.94/1.44  % SZS status CounterSatisfiable for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.44  
% 1.94/1.44  Inference rules
% 1.94/1.44  ----------------------
% 1.94/1.44  #Ref     : 0
% 1.94/1.44  #Sup     : 0
% 1.94/1.44  #Fact    : 0
% 1.94/1.44  #Define  : 0
% 1.94/1.44  #Split   : 1
% 1.94/1.44  #Chain   : 0
% 1.94/1.44  #Close   : 0
% 1.94/1.44  
% 1.94/1.44  Ordering : KBO
% 1.94/1.44  
% 1.94/1.44  Simplification rules
% 1.94/1.44  ----------------------
% 1.94/1.44  #Subsume      : 11
% 1.94/1.44  #Demod        : 0
% 1.94/1.44  #Tautology    : 1
% 1.94/1.44  #SimpNegUnit  : 2
% 1.94/1.44  #BackRed      : 0
% 1.94/1.44  
% 1.94/1.44  #Partial instantiations: 0
% 1.94/1.44  #Strategies tried      : 1
% 1.94/1.44  
% 1.94/1.44  Timing (in seconds)
% 1.94/1.44  ----------------------
% 1.94/1.44  Preprocessing        : 0.42
% 1.94/1.44  Parsing              : 0.22
% 2.07/1.44  CNF conversion       : 0.04
% 2.07/1.44  Main loop            : 0.16
% 2.07/1.44  Inferencing          : 0.05
% 2.07/1.44  Reduction            : 0.04
% 2.07/1.44  Demodulation         : 0.02
% 2.07/1.44  BG Simplification    : 0.02
% 2.07/1.44  Subsumption          : 0.03
% 2.07/1.44  Abstraction          : 0.01
% 2.07/1.44  MUC search           : 0.00
% 2.07/1.44  Cooper               : 0.00
% 2.07/1.44  Total                : 0.60
% 2.07/1.44  Index Insertion      : 0.00
% 2.07/1.44  Index Deletion       : 0.00
% 2.07/1.45  Index Matching       : 0.00
% 2.07/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
