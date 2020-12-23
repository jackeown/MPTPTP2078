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
% DateTime   : Thu Dec  3 10:25:02 EST 2020

% Result     : CounterSatisfiable 2.63s
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
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:50:44 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.63/1.41  
% 2.63/1.41  % SZS status CounterSatisfiable for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.63/1.41  
% 2.63/1.41  Inference rules
% 2.63/1.41  ----------------------
% 2.63/1.41  #Ref     : 6
% 2.63/1.41  #Sup     : 58
% 2.63/1.41  #Fact    : 0
% 2.63/1.41  #Define  : 0
% 2.63/1.41  #Split   : 0
% 2.63/1.41  #Chain   : 0
% 2.63/1.41  #Close   : 0
% 2.63/1.41  
% 2.63/1.41  Ordering : KBO
% 2.63/1.41  
% 2.63/1.41  Simplification rules
% 2.63/1.41  ----------------------
% 2.63/1.41  #Subsume      : 10
% 2.63/1.41  #Demod        : 65
% 2.63/1.41  #Tautology    : 26
% 2.63/1.41  #SimpNegUnit  : 0
% 2.63/1.41  #BackRed      : 5
% 2.63/1.41  
% 2.63/1.41  #Partial instantiations: 0
% 2.63/1.41  #Strategies tried      : 1
% 2.63/1.41  
% 2.63/1.41  Timing (in seconds)
% 2.63/1.41  ----------------------
% 2.63/1.42  Preprocessing        : 0.32
% 2.63/1.42  Parsing              : 0.17
% 2.63/1.42  CNF conversion       : 0.02
% 2.63/1.42  Main loop            : 0.30
% 2.63/1.42  Inferencing          : 0.12
% 2.63/1.42  Reduction            : 0.08
% 2.63/1.42  Demodulation         : 0.06
% 2.63/1.42  BG Simplification    : 0.02
% 2.63/1.42  Subsumption          : 0.06
% 2.63/1.42  Abstraction          : 0.01
% 2.63/1.42  MUC search           : 0.00
% 2.63/1.42  Cooper               : 0.00
% 2.63/1.42  Total                : 0.63
% 2.63/1.42  Index Insertion      : 0.00
% 2.63/1.42  Index Deletion       : 0.00
% 2.63/1.42  Index Matching       : 0.00
% 2.63/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
