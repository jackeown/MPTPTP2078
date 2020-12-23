%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:58 EST 2020

% Result     : CounterSatisfiable 2.88s
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
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:34:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.88/1.43  
% 2.88/1.43  % SZS status CounterSatisfiable for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.88/1.43  
% 2.88/1.43  Inference rules
% 2.88/1.43  ----------------------
% 2.88/1.43  #Ref     : 0
% 2.88/1.43  #Sup     : 222
% 2.88/1.43  #Fact    : 0
% 2.88/1.43  #Define  : 0
% 2.88/1.43  #Split   : 2
% 2.88/1.43  #Chain   : 0
% 2.88/1.43  #Close   : 0
% 2.88/1.43  
% 2.88/1.43  Ordering : KBO
% 2.88/1.43  
% 2.88/1.43  Simplification rules
% 2.88/1.43  ----------------------
% 2.88/1.43  #Subsume      : 20
% 2.88/1.43  #Demod        : 96
% 2.88/1.43  #Tautology    : 159
% 2.88/1.43  #SimpNegUnit  : 3
% 2.88/1.43  #BackRed      : 1
% 2.88/1.43  
% 2.88/1.43  #Partial instantiations: 0
% 2.88/1.43  #Strategies tried      : 1
% 2.88/1.43  
% 2.88/1.43  Timing (in seconds)
% 2.88/1.43  ----------------------
% 2.88/1.44  Preprocessing        : 0.31
% 2.88/1.44  Parsing              : 0.16
% 2.88/1.44  CNF conversion       : 0.02
% 2.88/1.44  Main loop            : 0.34
% 2.88/1.44  Inferencing          : 0.14
% 2.88/1.44  Reduction            : 0.10
% 2.88/1.44  Demodulation         : 0.08
% 2.88/1.44  BG Simplification    : 0.02
% 2.88/1.44  Subsumption          : 0.05
% 2.88/1.44  Abstraction          : 0.02
% 2.88/1.44  MUC search           : 0.00
% 2.88/1.44  Cooper               : 0.00
% 2.88/1.44  Total                : 0.66
% 2.88/1.44  Index Insertion      : 0.00
% 2.88/1.44  Index Deletion       : 0.00
% 2.88/1.44  Index Matching       : 0.00
% 2.88/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
