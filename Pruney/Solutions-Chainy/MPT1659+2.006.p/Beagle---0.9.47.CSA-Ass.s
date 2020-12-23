%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:58 EST 2020

% Result     : CounterSatisfiable 2.80s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:16:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.80/1.68  
% 2.80/1.68  % SZS status CounterSatisfiable for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.80/1.68  
% 2.80/1.68  Inference rules
% 2.80/1.68  ----------------------
% 2.80/1.68  #Ref     : 0
% 2.80/1.68  #Sup     : 59
% 2.80/1.68  #Fact    : 0
% 2.80/1.68  #Define  : 0
% 2.80/1.68  #Split   : 1
% 2.80/1.68  #Chain   : 0
% 2.80/1.68  #Close   : 0
% 2.80/1.68  
% 2.80/1.68  Ordering : KBO
% 2.80/1.68  
% 2.80/1.68  Simplification rules
% 2.80/1.68  ----------------------
% 2.80/1.68  #Subsume      : 26
% 2.80/1.68  #Demod        : 3
% 2.80/1.68  #Tautology    : 7
% 2.80/1.68  #SimpNegUnit  : 1
% 2.80/1.68  #BackRed      : 0
% 2.80/1.68  
% 2.80/1.68  #Partial instantiations: 0
% 2.80/1.68  #Strategies tried      : 1
% 2.80/1.68  
% 2.80/1.68  Timing (in seconds)
% 2.80/1.68  ----------------------
% 2.80/1.68  Preprocessing        : 0.35
% 2.80/1.68  Parsing              : 0.18
% 2.80/1.69  CNF conversion       : 0.03
% 2.80/1.69  Main loop            : 0.38
% 2.80/1.69  Inferencing          : 0.17
% 2.80/1.69  Reduction            : 0.09
% 2.80/1.69  Demodulation         : 0.06
% 2.80/1.69  BG Simplification    : 0.02
% 2.80/1.69  Subsumption          : 0.09
% 2.80/1.69  Abstraction          : 0.02
% 2.80/1.69  MUC search           : 0.00
% 2.80/1.69  Cooper               : 0.00
% 2.80/1.69  Total                : 0.74
% 2.80/1.69  Index Insertion      : 0.00
% 2.80/1.69  Index Deletion       : 0.00
% 2.80/1.69  Index Matching       : 0.00
% 2.80/1.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
