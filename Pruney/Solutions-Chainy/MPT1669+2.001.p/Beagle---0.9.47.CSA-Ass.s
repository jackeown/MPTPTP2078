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
% DateTime   : Thu Dec  3 10:26:00 EST 2020

% Result     : CounterSatisfiable 2.92s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n020.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 14:39:07 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.92/1.42  
% 2.92/1.43  % SZS status CounterSatisfiable for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.92/1.43  
% 2.92/1.43  Inference rules
% 2.92/1.43  ----------------------
% 2.92/1.43  #Ref     : 0
% 2.92/1.43  #Sup     : 66
% 2.92/1.43  #Fact    : 2
% 2.92/1.43  #Define  : 0
% 2.92/1.43  #Split   : 3
% 2.92/1.43  #Chain   : 0
% 2.92/1.43  #Close   : 0
% 2.92/1.43  
% 2.92/1.43  Ordering : KBO
% 2.92/1.43  
% 2.92/1.43  Simplification rules
% 2.92/1.43  ----------------------
% 2.92/1.43  #Subsume      : 18
% 2.92/1.43  #Demod        : 61
% 2.92/1.43  #Tautology    : 20
% 2.92/1.43  #SimpNegUnit  : 20
% 2.92/1.43  #BackRed      : 0
% 2.92/1.43  
% 2.92/1.43  #Partial instantiations: 0
% 2.92/1.43  #Strategies tried      : 1
% 2.92/1.43  
% 2.92/1.43  Timing (in seconds)
% 2.92/1.43  ----------------------
% 2.92/1.43  Preprocessing        : 0.29
% 2.92/1.43  Parsing              : 0.16
% 2.92/1.43  CNF conversion       : 0.02
% 2.92/1.43  Main loop            : 0.36
% 2.92/1.43  Inferencing          : 0.14
% 2.92/1.43  Reduction            : 0.09
% 2.92/1.43  Demodulation         : 0.06
% 2.92/1.43  BG Simplification    : 0.02
% 2.92/1.43  Subsumption          : 0.08
% 2.92/1.43  Abstraction          : 0.01
% 2.92/1.43  MUC search           : 0.00
% 2.92/1.43  Cooper               : 0.00
% 2.92/1.43  Total                : 0.66
% 2.92/1.43  Index Insertion      : 0.00
% 2.92/1.43  Index Deletion       : 0.00
% 2.92/1.43  Index Matching       : 0.00
% 2.92/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
