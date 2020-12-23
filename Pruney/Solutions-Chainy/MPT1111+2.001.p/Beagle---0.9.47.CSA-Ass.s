%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:58 EST 2020

% Result     : CounterSatisfiable 2.09s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n008.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 12:24:30 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.09/1.22  
% 2.09/1.22  % SZS status CounterSatisfiable for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.22  
% 2.09/1.22  Inference rules
% 2.09/1.22  ----------------------
% 2.09/1.22  #Ref     : 0
% 2.09/1.22  #Sup     : 50
% 2.09/1.22  #Fact    : 0
% 2.09/1.22  #Define  : 0
% 2.09/1.22  #Split   : 0
% 2.09/1.22  #Chain   : 0
% 2.09/1.22  #Close   : 0
% 2.09/1.22  
% 2.09/1.22  Ordering : KBO
% 2.09/1.22  
% 2.09/1.22  Simplification rules
% 2.09/1.22  ----------------------
% 2.09/1.22  #Subsume      : 14
% 2.09/1.22  #Demod        : 12
% 2.09/1.22  #Tautology    : 22
% 2.09/1.22  #SimpNegUnit  : 0
% 2.09/1.22  #BackRed      : 2
% 2.09/1.22  
% 2.09/1.22  #Partial instantiations: 0
% 2.09/1.22  #Strategies tried      : 1
% 2.09/1.22  
% 2.09/1.22  Timing (in seconds)
% 2.09/1.22  ----------------------
% 2.09/1.23  Preprocessing        : 0.29
% 2.09/1.23  Parsing              : 0.16
% 2.09/1.23  CNF conversion       : 0.02
% 2.09/1.23  Main loop            : 0.20
% 2.09/1.23  Inferencing          : 0.08
% 2.09/1.23  Reduction            : 0.05
% 2.09/1.23  Demodulation         : 0.04
% 2.09/1.23  BG Simplification    : 0.01
% 2.09/1.23  Subsumption          : 0.04
% 2.09/1.23  Abstraction          : 0.01
% 2.09/1.23  MUC search           : 0.00
% 2.09/1.23  Cooper               : 0.00
% 2.09/1.23  Total                : 0.50
% 2.09/1.23  Index Insertion      : 0.00
% 2.09/1.23  Index Deletion       : 0.00
% 2.09/1.23  Index Matching       : 0.00
% 2.09/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
