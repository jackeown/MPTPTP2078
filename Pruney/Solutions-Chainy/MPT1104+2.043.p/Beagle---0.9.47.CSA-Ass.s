%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:48 EST 2020

% Result     : CounterSatisfiable 11.68s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:30:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.68/5.53  
% 11.68/5.53  % SZS status CounterSatisfiable for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.68/5.53  
% 11.68/5.53  Inference rules
% 11.68/5.53  ----------------------
% 11.68/5.53  #Ref     : 0
% 11.68/5.53  #Sup     : 7783
% 11.68/5.53  #Fact    : 0
% 11.68/5.53  #Define  : 0
% 11.68/5.53  #Split   : 0
% 11.68/5.53  #Chain   : 0
% 11.68/5.53  #Close   : 0
% 11.68/5.53  
% 11.68/5.53  Ordering : KBO
% 11.68/5.53  
% 11.68/5.53  Simplification rules
% 11.68/5.53  ----------------------
% 11.68/5.53  #Subsume      : 667
% 11.68/5.53  #Demod        : 18392
% 11.68/5.53  #Tautology    : 6952
% 11.68/5.53  #SimpNegUnit  : 0
% 11.68/5.53  #BackRed      : 32
% 11.68/5.53  
% 11.68/5.53  #Partial instantiations: 0
% 11.68/5.53  #Strategies tried      : 1
% 11.68/5.53  
% 11.68/5.53  Timing (in seconds)
% 11.68/5.53  ----------------------
% 11.68/5.53  Preprocessing        : 0.34
% 11.68/5.53  Parsing              : 0.18
% 11.68/5.53  CNF conversion       : 0.02
% 11.68/5.53  Main loop            : 4.46
% 11.68/5.53  Inferencing          : 0.75
% 11.68/5.53  Reduction            : 2.94
% 11.68/5.53  Demodulation         : 2.69
% 11.78/5.53  BG Simplification    : 0.06
% 11.78/5.53  Subsumption          : 0.55
% 11.78/5.53  Abstraction          : 0.16
% 11.78/5.54  MUC search           : 0.00
% 11.78/5.54  Cooper               : 0.00
% 11.78/5.54  Total                : 4.81
% 11.78/5.54  Index Insertion      : 0.00
% 11.78/5.54  Index Deletion       : 0.00
% 11.78/5.54  Index Matching       : 0.00
% 11.78/5.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
