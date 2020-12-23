%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:01 EST 2020

% Result     : CounterSatisfiable 1.96s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.36  % Computer   : n010.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 10:10:29 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.88/1.24  
% 1.96/1.24  % SZS status CounterSatisfiable for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.96/1.24  
% 1.96/1.24  Inference rules
% 1.96/1.24  ----------------------
% 1.96/1.24  #Ref     : 0
% 1.96/1.24  #Sup     : 14
% 1.96/1.24  #Fact    : 0
% 1.96/1.24  #Define  : 0
% 1.96/1.24  #Split   : 3
% 1.96/1.24  #Chain   : 0
% 1.96/1.24  #Close   : 0
% 1.96/1.24  
% 1.96/1.24  Ordering : KBO
% 1.96/1.24  
% 1.96/1.24  Simplification rules
% 1.96/1.24  ----------------------
% 1.96/1.24  #Subsume      : 1
% 1.96/1.24  #Demod        : 26
% 1.96/1.24  #Tautology    : 5
% 1.96/1.24  #SimpNegUnit  : 7
% 1.96/1.24  #BackRed      : 0
% 1.96/1.24  
% 1.96/1.24  #Partial instantiations: 0
% 1.96/1.24  #Strategies tried      : 1
% 1.96/1.24  
% 1.96/1.24  Timing (in seconds)
% 1.96/1.24  ----------------------
% 1.96/1.25  Preprocessing        : 0.30
% 1.96/1.25  Parsing              : 0.16
% 1.96/1.25  CNF conversion       : 0.02
% 1.96/1.25  Main loop            : 0.15
% 1.96/1.25  Inferencing          : 0.06
% 1.96/1.25  Reduction            : 0.04
% 1.96/1.25  Demodulation         : 0.03
% 1.96/1.25  BG Simplification    : 0.01
% 1.96/1.25  Subsumption          : 0.02
% 1.96/1.25  Abstraction          : 0.01
% 1.96/1.25  MUC search           : 0.00
% 1.96/1.25  Cooper               : 0.00
% 1.96/1.25  Total                : 0.45
% 1.96/1.25  Index Insertion      : 0.00
% 1.96/1.25  Index Deletion       : 0.00
% 1.96/1.25  Index Matching       : 0.00
% 1.96/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
