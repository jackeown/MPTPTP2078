%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:19 EST 2020

% Result     : CounterSatisfiable 1.68s
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
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.20/0.34  % CPULimit   : 60
% 0.20/0.34  % DateTime   : Tue Dec  1 19:14:54 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.68/1.09  
% 1.68/1.09  % SZS status CounterSatisfiable for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.68/1.09  
% 1.68/1.09  Inference rules
% 1.68/1.09  ----------------------
% 1.68/1.09  #Ref     : 0
% 1.68/1.09  #Sup     : 0
% 1.68/1.09  #Fact    : 0
% 1.68/1.09  #Define  : 0
% 1.68/1.09  #Split   : 0
% 1.68/1.09  #Chain   : 0
% 1.68/1.09  #Close   : 0
% 1.68/1.09  
% 1.68/1.09  Ordering : KBO
% 1.68/1.09  
% 1.68/1.09  Simplification rules
% 1.68/1.09  ----------------------
% 1.68/1.09  #Subsume      : 0
% 1.68/1.09  #Demod        : 0
% 1.68/1.09  #Tautology    : 0
% 1.68/1.09  #SimpNegUnit  : 0
% 1.68/1.10  #BackRed      : 0
% 1.68/1.10  
% 1.68/1.10  #Partial instantiations: 0
% 1.68/1.10  #Strategies tried      : 1
% 1.68/1.10  
% 1.68/1.10  Timing (in seconds)
% 1.68/1.10  ----------------------
% 1.68/1.10  Preprocessing        : 0.28
% 1.68/1.10  Parsing              : 0.15
% 1.68/1.10  CNF conversion       : 0.02
% 1.68/1.10  Main loop            : 0.06
% 1.68/1.10  Inferencing          : 0.02
% 1.68/1.10  Reduction            : 0.02
% 1.68/1.10  Demodulation         : 0.01
% 1.68/1.10  BG Simplification    : 0.01
% 1.68/1.10  Subsumption          : 0.01
% 1.68/1.10  Abstraction          : 0.00
% 1.68/1.10  MUC search           : 0.00
% 1.68/1.10  Cooper               : 0.00
% 1.68/1.10  Total                : 0.35
% 1.68/1.10  Index Insertion      : 0.00
% 1.68/1.10  Index Deletion       : 0.00
% 1.68/1.10  Index Matching       : 0.00
% 1.68/1.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
