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
% DateTime   : Thu Dec  3 10:18:37 EST 2020

% Result     : CounterSatisfiable 2.46s
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
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:27:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.46/1.35  
% 2.46/1.35  % SZS status CounterSatisfiable for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.46/1.35  
% 2.46/1.35  Inference rules
% 2.46/1.35  ----------------------
% 2.46/1.35  #Ref     : 0
% 2.46/1.35  #Sup     : 111
% 2.46/1.35  #Fact    : 0
% 2.46/1.35  #Define  : 0
% 2.46/1.35  #Split   : 2
% 2.46/1.35  #Chain   : 0
% 2.46/1.35  #Close   : 0
% 2.46/1.35  
% 2.46/1.35  Ordering : KBO
% 2.46/1.35  
% 2.46/1.35  Simplification rules
% 2.46/1.35  ----------------------
% 2.46/1.35  #Subsume      : 0
% 2.46/1.35  #Demod        : 22
% 2.46/1.35  #Tautology    : 89
% 2.46/1.35  #SimpNegUnit  : 2
% 2.46/1.35  #BackRed      : 2
% 2.46/1.35  
% 2.46/1.35  #Partial instantiations: 0
% 2.46/1.35  #Strategies tried      : 1
% 2.46/1.35  
% 2.46/1.35  Timing (in seconds)
% 2.46/1.36  ----------------------
% 2.46/1.36  Preprocessing        : 0.34
% 2.46/1.36  Parsing              : 0.19
% 2.46/1.36  CNF conversion       : 0.02
% 2.46/1.36  Main loop            : 0.27
% 2.46/1.36  Inferencing          : 0.10
% 2.46/1.36  Reduction            : 0.08
% 2.46/1.36  Demodulation         : 0.06
% 2.46/1.36  BG Simplification    : 0.02
% 2.46/1.36  Subsumption          : 0.04
% 2.46/1.36  Abstraction          : 0.02
% 2.46/1.36  MUC search           : 0.00
% 2.46/1.36  Cooper               : 0.00
% 2.46/1.36  Total                : 0.62
% 2.46/1.36  Index Insertion      : 0.00
% 2.46/1.36  Index Deletion       : 0.00
% 2.46/1.36  Index Matching       : 0.00
% 2.46/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
