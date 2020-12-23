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
% DateTime   : Thu Dec  3 10:25:01 EST 2020

% Result     : CounterSatisfiable 2.06s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:43:44 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.06/1.25  
% 2.06/1.25  % SZS status CounterSatisfiable for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.25  
% 2.06/1.25  Inference rules
% 2.06/1.25  ----------------------
% 2.06/1.25  #Ref     : 0
% 2.06/1.25  #Sup     : 11
% 2.06/1.25  #Fact    : 0
% 2.06/1.25  #Define  : 0
% 2.06/1.25  #Split   : 3
% 2.06/1.25  #Chain   : 0
% 2.06/1.25  #Close   : 0
% 2.06/1.25  
% 2.06/1.25  Ordering : KBO
% 2.06/1.25  
% 2.06/1.25  Simplification rules
% 2.06/1.25  ----------------------
% 2.06/1.25  #Subsume      : 1
% 2.06/1.25  #Demod        : 5
% 2.06/1.25  #Tautology    : 5
% 2.06/1.25  #SimpNegUnit  : 2
% 2.06/1.25  #BackRed      : 0
% 2.06/1.25  
% 2.06/1.26  #Partial instantiations: 0
% 2.06/1.26  #Strategies tried      : 1
% 2.06/1.26  
% 2.06/1.26  Timing (in seconds)
% 2.06/1.26  ----------------------
% 2.23/1.26  Preprocessing        : 0.30
% 2.23/1.26  Parsing              : 0.16
% 2.23/1.26  CNF conversion       : 0.02
% 2.23/1.26  Main loop            : 0.15
% 2.23/1.26  Inferencing          : 0.06
% 2.23/1.26  Reduction            : 0.04
% 2.23/1.26  Demodulation         : 0.03
% 2.23/1.26  BG Simplification    : 0.02
% 2.23/1.26  Subsumption          : 0.03
% 2.23/1.26  Abstraction          : 0.01
% 2.23/1.26  MUC search           : 0.00
% 2.23/1.26  Cooper               : 0.00
% 2.23/1.26  Total                : 0.46
% 2.23/1.26  Index Insertion      : 0.00
% 2.23/1.26  Index Deletion       : 0.00
% 2.23/1.26  Index Matching       : 0.00
% 2.23/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
