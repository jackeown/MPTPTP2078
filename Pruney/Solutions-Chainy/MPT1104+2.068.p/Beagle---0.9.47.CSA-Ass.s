%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:50 EST 2020

% Result     : CounterSatisfiable 10.64s
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
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:00:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.64/5.02  
% 10.64/5.02  % SZS status CounterSatisfiable for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.64/5.02  
% 10.64/5.02  Inference rules
% 10.64/5.02  ----------------------
% 10.64/5.02  #Ref     : 0
% 10.64/5.02  #Sup     : 7484
% 10.64/5.02  #Fact    : 0
% 10.64/5.02  #Define  : 0
% 10.64/5.02  #Split   : 0
% 10.64/5.02  #Chain   : 0
% 10.64/5.02  #Close   : 0
% 10.64/5.02  
% 10.64/5.02  Ordering : KBO
% 10.64/5.02  
% 10.64/5.02  Simplification rules
% 10.64/5.02  ----------------------
% 10.64/5.02  #Subsume      : 518
% 10.64/5.02  #Demod        : 16860
% 10.64/5.02  #Tautology    : 6832
% 10.64/5.02  #SimpNegUnit  : 0
% 10.64/5.02  #BackRed      : 10
% 10.64/5.02  
% 10.64/5.02  #Partial instantiations: 0
% 10.64/5.02  #Strategies tried      : 1
% 10.64/5.02  
% 10.64/5.02  Timing (in seconds)
% 10.64/5.02  ----------------------
% 10.64/5.03  Preprocessing        : 0.30
% 10.64/5.03  Parsing              : 0.16
% 10.64/5.03  CNF conversion       : 0.02
% 10.64/5.03  Main loop            : 3.93
% 10.64/5.03  Inferencing          : 0.65
% 10.64/5.03  Reduction            : 2.67
% 10.64/5.03  Demodulation         : 2.47
% 10.64/5.03  BG Simplification    : 0.07
% 10.64/5.03  Subsumption          : 0.41
% 10.64/5.03  Abstraction          : 0.17
% 10.64/5.03  MUC search           : 0.00
% 10.64/5.03  Cooper               : 0.00
% 10.64/5.03  Total                : 4.24
% 10.64/5.03  Index Insertion      : 0.00
% 10.64/5.03  Index Deletion       : 0.00
% 10.64/5.03  Index Matching       : 0.00
% 10.64/5.03  BG Taut test         : 0.00
%------------------------------------------------------------------------------
