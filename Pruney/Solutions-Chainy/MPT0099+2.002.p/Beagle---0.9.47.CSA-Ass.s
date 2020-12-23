%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:36 EST 2020

% Result     : CounterSatisfiable 1.50s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:35:35 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.50/1.07  
% 1.50/1.07  % SZS status CounterSatisfiable for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.50/1.07  
% 1.50/1.07  Inference rules
% 1.50/1.07  ----------------------
% 1.50/1.07  #Ref     : 0
% 1.50/1.07  #Sup     : 9
% 1.50/1.07  #Fact    : 0
% 1.50/1.07  #Define  : 0
% 1.50/1.07  #Split   : 0
% 1.50/1.07  #Chain   : 0
% 1.50/1.07  #Close   : 0
% 1.50/1.07  
% 1.50/1.07  Ordering : KBO
% 1.50/1.07  
% 1.50/1.07  Simplification rules
% 1.50/1.07  ----------------------
% 1.50/1.07  #Subsume      : 0
% 1.50/1.07  #Demod        : 2
% 1.50/1.07  #Tautology    : 8
% 1.50/1.07  #SimpNegUnit  : 0
% 1.50/1.07  #BackRed      : 1
% 1.50/1.07  
% 1.50/1.07  #Partial instantiations: 0
% 1.50/1.07  #Strategies tried      : 1
% 1.50/1.07  
% 1.50/1.07  Timing (in seconds)
% 1.50/1.07  ----------------------
% 1.50/1.08  Preprocessing        : 0.25
% 1.50/1.08  Parsing              : 0.14
% 1.50/1.08  CNF conversion       : 0.01
% 1.50/1.08  Main loop            : 0.08
% 1.50/1.08  Inferencing          : 0.04
% 1.50/1.08  Reduction            : 0.02
% 1.50/1.08  Demodulation         : 0.01
% 1.50/1.08  BG Simplification    : 0.01
% 1.50/1.08  Subsumption          : 0.01
% 1.50/1.08  Abstraction          : 0.00
% 1.50/1.08  MUC search           : 0.00
% 1.50/1.08  Cooper               : 0.00
% 1.50/1.08  Total                : 0.34
% 1.50/1.08  Index Insertion      : 0.00
% 1.50/1.08  Index Deletion       : 0.00
% 1.50/1.08  Index Matching       : 0.00
% 1.60/1.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
