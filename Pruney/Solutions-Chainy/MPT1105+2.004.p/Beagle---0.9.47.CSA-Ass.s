%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:53 EST 2020

% Result     : CounterSatisfiable 1.92s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:27:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.92/1.17  
% 1.92/1.17  % SZS status CounterSatisfiable for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.17  
% 1.92/1.17  Inference rules
% 1.92/1.17  ----------------------
% 1.92/1.17  #Ref     : 0
% 1.92/1.17  #Sup     : 31
% 1.92/1.17  #Fact    : 0
% 1.92/1.17  #Define  : 0
% 1.92/1.17  #Split   : 0
% 1.92/1.17  #Chain   : 0
% 1.92/1.17  #Close   : 0
% 1.92/1.17  
% 1.92/1.17  Ordering : KBO
% 1.92/1.17  
% 1.92/1.17  Simplification rules
% 1.92/1.17  ----------------------
% 1.92/1.17  #Subsume      : 1
% 1.92/1.17  #Demod        : 17
% 1.92/1.17  #Tautology    : 20
% 1.92/1.17  #SimpNegUnit  : 0
% 1.92/1.17  #BackRed      : 0
% 1.92/1.17  
% 1.92/1.17  #Partial instantiations: 0
% 1.92/1.17  #Strategies tried      : 1
% 1.92/1.17  
% 1.92/1.17  Timing (in seconds)
% 1.92/1.17  ----------------------
% 1.92/1.18  Preprocessing        : 0.29
% 1.92/1.18  Parsing              : 0.16
% 1.92/1.18  CNF conversion       : 0.02
% 1.92/1.18  Main loop            : 0.14
% 1.92/1.18  Inferencing          : 0.06
% 1.92/1.18  Reduction            : 0.04
% 1.92/1.18  Demodulation         : 0.03
% 1.92/1.18  BG Simplification    : 0.01
% 1.92/1.18  Subsumption          : 0.02
% 1.92/1.18  Abstraction          : 0.01
% 1.92/1.18  MUC search           : 0.00
% 1.92/1.18  Cooper               : 0.00
% 1.92/1.18  Total                : 0.44
% 1.92/1.18  Index Insertion      : 0.00
% 1.92/1.18  Index Deletion       : 0.00
% 1.92/1.18  Index Matching       : 0.00
% 1.92/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
