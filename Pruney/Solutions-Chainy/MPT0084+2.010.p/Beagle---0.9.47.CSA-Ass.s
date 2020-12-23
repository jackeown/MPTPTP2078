%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:05 EST 2020

% Result     : CounterSatisfiable 16.51s
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
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:48:55 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 16.51/9.46  
% 16.51/9.46  % SZS status CounterSatisfiable for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.51/9.46  
% 16.51/9.46  Inference rules
% 16.51/9.46  ----------------------
% 16.51/9.46  #Ref     : 0
% 16.51/9.46  #Sup     : 8437
% 16.51/9.46  #Fact    : 0
% 16.51/9.46  #Define  : 0
% 16.51/9.46  #Split   : 22
% 16.51/9.46  #Chain   : 0
% 16.51/9.46  #Close   : 0
% 16.51/9.46  
% 16.51/9.46  Ordering : KBO
% 16.51/9.46  
% 16.51/9.46  Simplification rules
% 16.51/9.46  ----------------------
% 16.51/9.46  #Subsume      : 7633
% 16.51/9.46  #Demod        : 3364
% 16.51/9.46  #Tautology    : 405
% 16.51/9.46  #SimpNegUnit  : 136
% 16.51/9.46  #BackRed      : 0
% 16.51/9.46  
% 16.51/9.46  #Partial instantiations: 0
% 16.51/9.46  #Strategies tried      : 1
% 16.51/9.46  
% 16.51/9.46  Timing (in seconds)
% 16.51/9.46  ----------------------
% 16.51/9.47  Preprocessing        : 0.26
% 16.51/9.47  Parsing              : 0.15
% 16.51/9.47  CNF conversion       : 0.02
% 16.51/9.47  Main loop            : 8.46
% 16.51/9.47  Inferencing          : 0.96
% 16.51/9.47  Reduction            : 2.71
% 16.51/9.47  Demodulation         : 2.14
% 16.51/9.47  BG Simplification    : 0.07
% 16.51/9.47  Subsumption          : 4.44
% 16.51/9.47  Abstraction          : 0.13
% 16.51/9.47  MUC search           : 0.00
% 16.51/9.47  Cooper               : 0.00
% 16.51/9.47  Total                : 8.73
% 16.51/9.47  Index Insertion      : 0.00
% 16.51/9.47  Index Deletion       : 0.00
% 16.51/9.47  Index Matching       : 0.00
% 16.51/9.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
