%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:33 EST 2020

% Result     : CounterSatisfiable 1.58s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:44:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.58/1.14  
% 1.58/1.14  % SZS status CounterSatisfiable for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.58/1.14  
% 1.58/1.14  Inference rules
% 1.58/1.14  ----------------------
% 1.58/1.14  #Ref     : 0
% 1.58/1.14  #Sup     : 3
% 1.58/1.14  #Fact    : 0
% 1.58/1.14  #Define  : 0
% 1.58/1.14  #Split   : 0
% 1.58/1.14  #Chain   : 0
% 1.58/1.14  #Close   : 0
% 1.58/1.14  
% 1.58/1.14  Ordering : KBO
% 1.58/1.14  
% 1.58/1.14  Simplification rules
% 1.58/1.14  ----------------------
% 1.58/1.14  #Subsume      : 0
% 1.58/1.14  #Demod        : 1
% 1.58/1.14  #Tautology    : 2
% 1.58/1.14  #SimpNegUnit  : 0
% 1.58/1.14  #BackRed      : 0
% 1.58/1.14  
% 1.58/1.14  #Partial instantiations: 0
% 1.58/1.14  #Strategies tried      : 1
% 1.58/1.14  
% 1.58/1.14  Timing (in seconds)
% 1.58/1.14  ----------------------
% 1.58/1.14  Preprocessing        : 0.27
% 1.58/1.15  Parsing              : 0.14
% 1.58/1.15  CNF conversion       : 0.02
% 1.58/1.15  Main loop            : 0.06
% 1.58/1.15  Inferencing          : 0.03
% 1.58/1.15  Reduction            : 0.02
% 1.58/1.15  Demodulation         : 0.01
% 1.58/1.15  BG Simplification    : 0.01
% 1.58/1.15  Subsumption          : 0.00
% 1.58/1.15  Abstraction          : 0.00
% 1.58/1.15  MUC search           : 0.00
% 1.58/1.15  Cooper               : 0.00
% 1.58/1.15  Total                : 0.34
% 1.58/1.15  Index Insertion      : 0.00
% 1.58/1.15  Index Deletion       : 0.00
% 1.58/1.15  Index Matching       : 0.00
% 1.58/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
