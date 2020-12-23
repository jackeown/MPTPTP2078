%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:39 EST 2020

% Result     : CounterSatisfiable 1.64s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:27:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.64/1.08  
% 1.64/1.08  % SZS status CounterSatisfiable for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.08  
% 1.64/1.08  Inference rules
% 1.64/1.08  ----------------------
% 1.64/1.08  #Ref     : 0
% 1.64/1.08  #Sup     : 5
% 1.64/1.08  #Fact    : 0
% 1.64/1.08  #Define  : 0
% 1.64/1.08  #Split   : 0
% 1.64/1.08  #Chain   : 0
% 1.64/1.08  #Close   : 0
% 1.64/1.08  
% 1.64/1.08  Ordering : KBO
% 1.64/1.08  
% 1.64/1.08  Simplification rules
% 1.64/1.08  ----------------------
% 1.64/1.08  #Subsume      : 0
% 1.64/1.08  #Demod        : 0
% 1.64/1.08  #Tautology    : 0
% 1.64/1.08  #SimpNegUnit  : 1
% 1.64/1.08  #BackRed      : 0
% 1.64/1.08  
% 1.64/1.08  #Partial instantiations: 0
% 1.64/1.08  #Strategies tried      : 1
% 1.64/1.08  
% 1.64/1.08  Timing (in seconds)
% 1.64/1.08  ----------------------
% 1.64/1.09  Preprocessing        : 0.24
% 1.64/1.09  Parsing              : 0.13
% 1.64/1.09  CNF conversion       : 0.01
% 1.64/1.09  Main loop            : 0.10
% 1.64/1.09  Inferencing          : 0.05
% 1.64/1.09  Reduction            : 0.02
% 1.64/1.09  Demodulation         : 0.01
% 1.64/1.09  BG Simplification    : 0.01
% 1.64/1.09  Subsumption          : 0.02
% 1.64/1.09  Abstraction          : 0.01
% 1.64/1.09  MUC search           : 0.00
% 1.64/1.09  Cooper               : 0.00
% 1.64/1.09  Total                : 0.35
% 1.64/1.09  Index Insertion      : 0.00
% 1.64/1.09  Index Deletion       : 0.00
% 1.64/1.09  Index Matching       : 0.00
% 1.64/1.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
