%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:06 EST 2020

% Result     : CounterSatisfiable 2.54s
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
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:59:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.54/1.68  
% 2.54/1.68  % SZS status CounterSatisfiable for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.54/1.68  
% 2.54/1.68  Inference rules
% 2.54/1.68  ----------------------
% 2.54/1.68  #Ref     : 0
% 2.54/1.68  #Sup     : 31
% 2.54/1.68  #Fact    : 0
% 2.54/1.68  #Define  : 0
% 2.54/1.68  #Split   : 2
% 2.54/1.68  #Chain   : 0
% 2.54/1.68  #Close   : 0
% 2.54/1.68  
% 2.54/1.68  Ordering : KBO
% 2.54/1.68  
% 2.54/1.68  Simplification rules
% 2.54/1.68  ----------------------
% 2.54/1.68  #Subsume      : 3
% 2.54/1.68  #Demod        : 11
% 2.54/1.68  #Tautology    : 11
% 2.54/1.68  #SimpNegUnit  : 2
% 2.54/1.68  #BackRed      : 1
% 2.54/1.68  
% 2.54/1.68  #Partial instantiations: 0
% 2.54/1.68  #Strategies tried      : 1
% 2.54/1.68  
% 2.54/1.68  Timing (in seconds)
% 2.54/1.68  ----------------------
% 2.54/1.69  Preprocessing        : 0.49
% 2.54/1.69  Parsing              : 0.26
% 2.54/1.69  CNF conversion       : 0.04
% 2.54/1.69  Main loop            : 0.31
% 2.54/1.69  Inferencing          : 0.14
% 2.54/1.69  Reduction            : 0.08
% 2.54/1.69  Demodulation         : 0.06
% 2.54/1.69  BG Simplification    : 0.02
% 2.54/1.69  Subsumption          : 0.04
% 2.54/1.69  Abstraction          : 0.02
% 2.54/1.69  MUC search           : 0.00
% 2.54/1.69  Cooper               : 0.00
% 2.54/1.69  Total                : 0.81
% 2.54/1.69  Index Insertion      : 0.00
% 2.54/1.69  Index Deletion       : 0.00
% 2.54/1.69  Index Matching       : 0.00
% 2.54/1.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
