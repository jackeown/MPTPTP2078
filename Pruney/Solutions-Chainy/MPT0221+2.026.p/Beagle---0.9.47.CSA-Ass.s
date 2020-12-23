%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:15 EST 2020

% Result     : CounterSatisfiable 1.52s
% Output     : Assurance 0s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:47:09 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.52/1.07  
% 1.52/1.07  % SZS status CounterSatisfiable for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.52/1.07  
% 1.52/1.07  Inference rules
% 1.52/1.07  ----------------------
% 1.52/1.07  #Ref     : 0
% 1.52/1.07  #Sup     : 12
% 1.52/1.07  #Fact    : 0
% 1.52/1.07  #Define  : 0
% 1.52/1.07  #Split   : 0
% 1.52/1.07  #Chain   : 0
% 1.52/1.07  #Close   : 0
% 1.52/1.07  
% 1.52/1.07  Ordering : KBO
% 1.52/1.07  
% 1.52/1.07  Simplification rules
% 1.52/1.07  ----------------------
% 1.52/1.07  #Subsume      : 0
% 1.52/1.07  #Demod        : 4
% 1.52/1.07  #Tautology    : 12
% 1.52/1.07  #SimpNegUnit  : 0
% 1.52/1.07  #BackRed      : 1
% 1.52/1.07  
% 1.52/1.07  #Partial instantiations: 0
% 1.52/1.07  #Strategies tried      : 1
% 1.52/1.07  
% 1.52/1.07  Timing (in seconds)
% 1.52/1.07  ----------------------
% 1.52/1.08  Preprocessing        : 0.27
% 1.52/1.08  Parsing              : 0.14
% 1.52/1.08  CNF conversion       : 0.01
% 1.52/1.08  Main loop            : 0.08
% 1.52/1.08  Inferencing          : 0.03
% 1.52/1.08  Reduction            : 0.02
% 1.52/1.08  Demodulation         : 0.02
% 1.52/1.08  BG Simplification    : 0.01
% 1.52/1.08  Subsumption          : 0.01
% 1.52/1.08  Abstraction          : 0.00
% 1.52/1.08  MUC search           : 0.00
% 1.52/1.08  Cooper               : 0.00
% 1.52/1.08  Total                : 0.36
% 1.52/1.08  Index Insertion      : 0.00
% 1.52/1.08  Index Deletion       : 0.00
% 1.52/1.08  Index Matching       : 0.00
% 1.52/1.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
