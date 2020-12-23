%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:00 EST 2020

% Result     : CounterSatisfiable 2.91s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.19/0.33  % CPULimit   : 60
% 0.19/0.33  % DateTime   : Tue Dec  1 10:14:42 EST 2020
% 0.19/0.33  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.91/1.44  
% 2.91/1.44  % SZS status CounterSatisfiable for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.91/1.44  
% 2.91/1.44  Inference rules
% 2.91/1.44  ----------------------
% 2.91/1.44  #Ref     : 0
% 2.91/1.44  #Sup     : 110
% 2.91/1.44  #Fact    : 0
% 2.91/1.44  #Define  : 0
% 2.91/1.44  #Split   : 5
% 2.91/1.44  #Chain   : 0
% 2.91/1.44  #Close   : 0
% 2.91/1.44  
% 2.91/1.44  Ordering : KBO
% 2.91/1.44  
% 2.91/1.44  Simplification rules
% 2.91/1.44  ----------------------
% 2.91/1.44  #Subsume      : 39
% 2.91/1.44  #Demod        : 23
% 2.91/1.44  #Tautology    : 18
% 2.91/1.44  #SimpNegUnit  : 1
% 2.91/1.44  #BackRed      : 0
% 2.91/1.44  
% 2.91/1.44  #Partial instantiations: 0
% 2.91/1.44  #Strategies tried      : 1
% 2.91/1.44  
% 2.91/1.44  Timing (in seconds)
% 2.91/1.44  ----------------------
% 2.91/1.44  Preprocessing        : 0.30
% 2.91/1.44  Parsing              : 0.16
% 2.91/1.44  CNF conversion       : 0.02
% 2.91/1.44  Main loop            : 0.41
% 2.91/1.44  Inferencing          : 0.17
% 2.91/1.44  Reduction            : 0.10
% 2.91/1.44  Demodulation         : 0.06
% 2.91/1.44  BG Simplification    : 0.02
% 2.91/1.44  Subsumption          : 0.09
% 2.91/1.44  Abstraction          : 0.01
% 2.91/1.44  MUC search           : 0.00
% 2.91/1.44  Cooper               : 0.00
% 2.91/1.44  Total                : 0.72
% 2.91/1.44  Index Insertion      : 0.00
% 2.91/1.44  Index Deletion       : 0.00
% 2.91/1.44  Index Matching       : 0.00
% 2.91/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
