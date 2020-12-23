%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:06 EST 2020

% Result     : CounterSatisfiable 1.68s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:59:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.68/1.08  
% 1.68/1.08  % SZS status CounterSatisfiable for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.68/1.08  
% 1.68/1.08  Inference rules
% 1.68/1.08  ----------------------
% 1.68/1.08  #Ref     : 0
% 1.68/1.08  #Sup     : 19
% 1.68/1.08  #Fact    : 0
% 1.68/1.08  #Define  : 0
% 1.68/1.08  #Split   : 1
% 1.68/1.08  #Chain   : 0
% 1.68/1.08  #Close   : 0
% 1.68/1.08  
% 1.68/1.08  Ordering : KBO
% 1.68/1.08  
% 1.68/1.08  Simplification rules
% 1.68/1.08  ----------------------
% 1.68/1.08  #Subsume      : 0
% 1.68/1.08  #Demod        : 2
% 1.68/1.08  #Tautology    : 19
% 1.68/1.08  #SimpNegUnit  : 1
% 1.68/1.08  #BackRed      : 1
% 1.68/1.08  
% 1.68/1.08  #Partial instantiations: 0
% 1.68/1.08  #Strategies tried      : 1
% 1.68/1.08  
% 1.68/1.08  Timing (in seconds)
% 1.68/1.08  ----------------------
% 1.68/1.08  Preprocessing        : 0.27
% 1.68/1.08  Parsing              : 0.14
% 1.68/1.08  CNF conversion       : 0.01
% 1.68/1.08  Main loop            : 0.09
% 1.68/1.08  Inferencing          : 0.03
% 1.68/1.08  Reduction            : 0.03
% 1.68/1.08  Demodulation         : 0.02
% 1.68/1.08  BG Simplification    : 0.01
% 1.68/1.08  Subsumption          : 0.02
% 1.68/1.08  Abstraction          : 0.00
% 1.68/1.08  MUC search           : 0.00
% 1.68/1.09  Cooper               : 0.00
% 1.68/1.09  Total                : 0.36
% 1.68/1.09  Index Insertion      : 0.00
% 1.68/1.09  Index Deletion       : 0.00
% 1.68/1.09  Index Matching       : 0.00
% 1.68/1.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
