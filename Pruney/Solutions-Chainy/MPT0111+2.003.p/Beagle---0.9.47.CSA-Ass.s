%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:08 EST 2020

% Result     : CounterSatisfiable 1.83s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:11:55 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.83/1.25  
% 1.83/1.25  % SZS status CounterSatisfiable for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.83/1.25  
% 1.83/1.25  Inference rules
% 1.83/1.25  ----------------------
% 1.83/1.25  #Ref     : 0
% 1.83/1.25  #Sup     : 5
% 1.83/1.25  #Fact    : 0
% 1.83/1.25  #Define  : 0
% 1.83/1.25  #Split   : 5
% 1.83/1.25  #Chain   : 0
% 1.83/1.25  #Close   : 0
% 1.83/1.25  
% 1.83/1.25  Ordering : KBO
% 1.83/1.25  
% 1.83/1.25  Simplification rules
% 1.83/1.25  ----------------------
% 1.83/1.25  #Subsume      : 3
% 1.83/1.25  #Demod        : 0
% 1.83/1.25  #Tautology    : 2
% 1.83/1.25  #SimpNegUnit  : 2
% 1.83/1.25  #BackRed      : 0
% 1.83/1.25  
% 1.83/1.25  #Partial instantiations: 0
% 1.83/1.25  #Strategies tried      : 1
% 1.83/1.25  
% 1.83/1.25  Timing (in seconds)
% 1.83/1.25  ----------------------
% 1.83/1.26  Preprocessing        : 0.32
% 1.83/1.26  Parsing              : 0.15
% 1.83/1.26  CNF conversion       : 0.02
% 1.83/1.26  Main loop            : 0.11
% 1.83/1.26  Inferencing          : 0.04
% 1.83/1.26  Reduction            : 0.02
% 1.83/1.26  Demodulation         : 0.01
% 1.83/1.26  BG Simplification    : 0.01
% 1.83/1.26  Subsumption          : 0.02
% 1.83/1.26  Abstraction          : 0.00
% 1.83/1.26  MUC search           : 0.00
% 1.83/1.26  Cooper               : 0.00
% 1.83/1.26  Total                : 0.44
% 1.83/1.26  Index Insertion      : 0.00
% 1.83/1.26  Index Deletion       : 0.00
% 1.83/1.26  Index Matching       : 0.00
% 1.83/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
