%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:46 EST 2020

% Result     : CounterSatisfiable 10.41s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n002.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 09:52:22 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.41/4.62  
% 10.41/4.62  % SZS status CounterSatisfiable for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.41/4.62  
% 10.41/4.62  Inference rules
% 10.41/4.62  ----------------------
% 10.41/4.62  #Ref     : 0
% 10.41/4.62  #Sup     : 6661
% 10.41/4.62  #Fact    : 0
% 10.41/4.62  #Define  : 0
% 10.41/4.62  #Split   : 0
% 10.41/4.62  #Chain   : 0
% 10.41/4.62  #Close   : 0
% 10.41/4.62  
% 10.41/4.62  Ordering : KBO
% 10.41/4.62  
% 10.41/4.62  Simplification rules
% 10.41/4.62  ----------------------
% 10.41/4.62  #Subsume      : 534
% 10.41/4.62  #Demod        : 14260
% 10.41/4.62  #Tautology    : 5960
% 10.41/4.62  #SimpNegUnit  : 0
% 10.41/4.62  #BackRed      : 16
% 10.41/4.62  
% 10.41/4.62  #Partial instantiations: 0
% 10.41/4.62  #Strategies tried      : 1
% 10.41/4.62  
% 10.41/4.62  Timing (in seconds)
% 10.41/4.62  ----------------------
% 10.41/4.63  Preprocessing        : 0.33
% 10.41/4.63  Parsing              : 0.18
% 10.41/4.63  CNF conversion       : 0.02
% 10.41/4.63  Main loop            : 3.58
% 10.41/4.63  Inferencing          : 0.60
% 10.41/4.63  Reduction            : 2.37
% 10.41/4.63  Demodulation         : 2.16
% 10.41/4.63  BG Simplification    : 0.05
% 10.41/4.63  Subsumption          : 0.44
% 10.41/4.63  Abstraction          : 0.13
% 10.41/4.63  MUC search           : 0.00
% 10.41/4.63  Cooper               : 0.00
% 10.41/4.63  Total                : 3.92
% 10.41/4.63  Index Insertion      : 0.00
% 10.41/4.63  Index Deletion       : 0.00
% 10.41/4.63  Index Matching       : 0.00
% 10.41/4.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
