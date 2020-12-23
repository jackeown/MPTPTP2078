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
% DateTime   : Thu Dec  3 10:18:43 EST 2020

% Result     : CounterSatisfiable 1.86s
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
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:30:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.86/1.18  
% 1.86/1.18  % SZS status CounterSatisfiable for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.86/1.18  
% 1.86/1.18  Inference rules
% 1.86/1.18  ----------------------
% 1.86/1.18  #Ref     : 0
% 1.86/1.18  #Sup     : 37
% 1.86/1.18  #Fact    : 0
% 1.86/1.18  #Define  : 0
% 1.86/1.18  #Split   : 3
% 1.86/1.18  #Chain   : 0
% 1.86/1.18  #Close   : 0
% 1.86/1.18  
% 1.86/1.18  Ordering : KBO
% 1.86/1.18  
% 1.86/1.18  Simplification rules
% 1.86/1.18  ----------------------
% 1.86/1.18  #Subsume      : 0
% 1.86/1.18  #Demod        : 10
% 1.86/1.18  #Tautology    : 28
% 1.86/1.18  #SimpNegUnit  : 0
% 1.86/1.18  #BackRed      : 1
% 1.86/1.18  
% 1.86/1.18  #Partial instantiations: 0
% 1.86/1.18  #Strategies tried      : 1
% 1.86/1.18  
% 1.86/1.18  Timing (in seconds)
% 1.86/1.18  ----------------------
% 1.86/1.19  Preprocessing        : 0.29
% 1.86/1.19  Parsing              : 0.15
% 1.86/1.19  CNF conversion       : 0.02
% 1.86/1.19  Main loop            : 0.14
% 1.86/1.19  Inferencing          : 0.06
% 1.86/1.19  Reduction            : 0.04
% 1.86/1.19  Demodulation         : 0.03
% 1.86/1.19  BG Simplification    : 0.01
% 1.86/1.19  Subsumption          : 0.02
% 1.86/1.19  Abstraction          : 0.01
% 1.86/1.19  MUC search           : 0.00
% 1.86/1.19  Cooper               : 0.00
% 1.86/1.19  Total                : 0.44
% 1.86/1.19  Index Insertion      : 0.00
% 1.86/1.19  Index Deletion       : 0.00
% 1.86/1.19  Index Matching       : 0.00
% 1.86/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
