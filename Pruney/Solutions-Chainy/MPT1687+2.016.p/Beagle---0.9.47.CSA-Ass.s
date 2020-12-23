%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:05 EST 2020

% Result     : CounterSatisfiable 14.54s
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
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:52:00 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.54/10.76  
% 14.54/10.76  % SZS status CounterSatisfiable for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.54/10.76  
% 14.54/10.76  Inference rules
% 14.54/10.77  ----------------------
% 14.54/10.77  #Ref     : 0
% 14.54/10.77  #Sup     : 214
% 14.54/10.77  #Fact    : 0
% 14.54/10.77  #Define  : 0
% 14.54/10.77  #Split   : 8
% 14.54/10.77  #Chain   : 0
% 14.54/10.77  #Close   : 0
% 14.54/10.77  
% 14.54/10.77  Ordering : KBO
% 14.54/10.77  
% 14.54/10.77  Simplification rules
% 14.54/10.77  ----------------------
% 14.54/10.77  #Subsume      : 72
% 14.54/10.77  #Demod        : 55
% 14.54/10.77  #Tautology    : 58
% 14.54/10.77  #SimpNegUnit  : 5
% 14.54/10.77  #BackRed      : 6
% 14.54/10.77  
% 14.54/10.77  #Partial instantiations: 0
% 14.65/10.77  #Strategies tried      : 1
% 14.65/10.77  
% 14.65/10.77  Timing (in seconds)
% 14.65/10.77  ----------------------
% 14.65/10.77  Preprocessing        : 0.37
% 14.65/10.77  Parsing              : 0.20
% 14.65/10.77  CNF conversion       : 0.02
% 14.65/10.77  Main loop            : 9.64
% 14.65/10.77  Inferencing          : 0.31
% 14.65/10.77  Reduction            : 0.22
% 14.65/10.77  Demodulation         : 0.15
% 14.65/10.77  BG Simplification    : 0.04
% 14.65/10.77  Subsumption          : 9.03
% 14.65/10.77  Abstraction          : 0.04
% 14.65/10.77  MUC search           : 0.00
% 14.65/10.77  Cooper               : 0.00
% 14.65/10.77  Total                : 10.02
% 14.65/10.77  Index Insertion      : 0.00
% 14.65/10.77  Index Deletion       : 0.00
% 14.65/10.77  Index Matching       : 0.00
% 14.65/10.77  BG Taut test         : 0.00
%------------------------------------------------------------------------------
