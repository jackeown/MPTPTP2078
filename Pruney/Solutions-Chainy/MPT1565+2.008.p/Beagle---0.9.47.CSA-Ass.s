%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:12 EST 2020

% Result     : CounterSatisfiable 2.72s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:12:32 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.72/1.43  
% 2.72/1.43  % SZS status CounterSatisfiable for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.72/1.43  
% 2.72/1.43  Inference rules
% 2.72/1.43  ----------------------
% 2.72/1.43  #Ref     : 0
% 2.72/1.43  #Sup     : 93
% 2.72/1.43  #Fact    : 0
% 2.72/1.43  #Define  : 0
% 2.72/1.43  #Split   : 2
% 2.72/1.43  #Chain   : 0
% 2.72/1.43  #Close   : 0
% 2.72/1.43  
% 2.72/1.43  Ordering : KBO
% 2.72/1.43  
% 2.72/1.43  Simplification rules
% 2.72/1.43  ----------------------
% 2.72/1.43  #Subsume      : 42
% 2.72/1.43  #Demod        : 0
% 2.72/1.43  #Tautology    : 5
% 2.72/1.43  #SimpNegUnit  : 0
% 2.72/1.43  #BackRed      : 0
% 2.72/1.43  
% 2.72/1.43  #Partial instantiations: 0
% 2.72/1.43  #Strategies tried      : 1
% 2.72/1.43  
% 2.72/1.43  Timing (in seconds)
% 2.72/1.43  ----------------------
% 3.02/1.44  Preprocessing        : 0.30
% 3.02/1.44  Parsing              : 0.17
% 3.02/1.44  CNF conversion       : 0.02
% 3.02/1.44  Main loop            : 0.36
% 3.02/1.44  Inferencing          : 0.16
% 3.02/1.44  Reduction            : 0.07
% 3.02/1.44  Demodulation         : 0.04
% 3.02/1.44  BG Simplification    : 0.02
% 3.02/1.44  Subsumption          : 0.09
% 3.02/1.44  Abstraction          : 0.01
% 3.02/1.44  MUC search           : 0.00
% 3.02/1.44  Cooper               : 0.00
% 3.02/1.44  Total                : 0.67
% 3.02/1.44  Index Insertion      : 0.00
% 3.02/1.44  Index Deletion       : 0.00
% 3.02/1.44  Index Matching       : 0.00
% 3.02/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
