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
% DateTime   : Thu Dec  3 10:26:03 EST 2020

% Result     : CounterSatisfiable 3.47s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:33:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.47/1.53  
% 3.47/1.53  % SZS status CounterSatisfiable for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.47/1.53  
% 3.47/1.53  Inference rules
% 3.47/1.53  ----------------------
% 3.47/1.53  #Ref     : 0
% 3.47/1.53  #Sup     : 58
% 3.47/1.53  #Fact    : 0
% 3.47/1.53  #Define  : 0
% 3.47/1.53  #Split   : 3
% 3.47/1.53  #Chain   : 0
% 3.47/1.53  #Close   : 0
% 3.47/1.53  
% 3.47/1.53  Ordering : KBO
% 3.47/1.53  
% 3.47/1.53  Simplification rules
% 3.47/1.53  ----------------------
% 3.47/1.53  #Subsume      : 4
% 3.47/1.53  #Demod        : 5
% 3.47/1.53  #Tautology    : 35
% 3.47/1.53  #SimpNegUnit  : 1
% 3.47/1.53  #BackRed      : 0
% 3.47/1.53  
% 3.47/1.53  #Partial instantiations: 0
% 3.47/1.53  #Strategies tried      : 1
% 3.47/1.53  
% 3.47/1.53  Timing (in seconds)
% 3.47/1.53  ----------------------
% 3.47/1.54  Preprocessing        : 0.35
% 3.47/1.54  Parsing              : 0.18
% 3.47/1.54  CNF conversion       : 0.03
% 3.47/1.54  Main loop            : 0.44
% 3.47/1.54  Inferencing          : 0.18
% 3.47/1.54  Reduction            : 0.10
% 3.47/1.54  Demodulation         : 0.06
% 3.47/1.54  BG Simplification    : 0.03
% 3.47/1.54  Subsumption          : 0.11
% 3.47/1.54  Abstraction          : 0.02
% 3.47/1.54  MUC search           : 0.00
% 3.47/1.54  Cooper               : 0.00
% 3.47/1.54  Total                : 0.80
% 3.47/1.54  Index Insertion      : 0.00
% 3.47/1.54  Index Deletion       : 0.00
% 3.47/1.54  Index Matching       : 0.00
% 3.47/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
