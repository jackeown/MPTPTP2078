%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:07 EST 2020

% Result     : Theorem 1.48s
% Output     : CNFRefutation 1.48s
% Verified   : 
% Statistics : Number of formulae       :   21 (  21 expanded)
%              Number of leaves         :   14 (  14 expanded)
%              Depth                    :    4
%              Number of atoms          :   11 (  11 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k4_xboole_0(k2_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t101_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_34,negated_conjecture,(
    ~ ! [A,B,C] : k4_xboole_0(A,k5_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,k2_xboole_0(B,C)),k3_xboole_0(k3_xboole_0(A,B),C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_xboole_1)).

tff(c_2,plain,(
    ! [A_1,B_2] : k4_xboole_0(k2_xboole_0(A_1,B_2),k3_xboole_0(A_1,B_2)) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_6,B_7,C_8] : k2_xboole_0(k4_xboole_0(A_6,B_7),k3_xboole_0(A_6,C_8)) = k4_xboole_0(A_6,k4_xboole_0(B_7,C_8)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_3,B_4,C_5] : k3_xboole_0(k3_xboole_0(A_3,B_4),C_5) = k3_xboole_0(A_3,k3_xboole_0(B_4,C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_8,plain,(
    k2_xboole_0(k4_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3')),k3_xboole_0(k3_xboole_0('#skF_1','#skF_2'),'#skF_3')) != k4_xboole_0('#skF_1',k5_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_9,plain,(
    k2_xboole_0(k4_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3')),k3_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3'))) != k4_xboole_0('#skF_1',k5_xboole_0('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_8])).

tff(c_10,plain,(
    k4_xboole_0('#skF_1',k4_xboole_0(k2_xboole_0('#skF_2','#skF_3'),k3_xboole_0('#skF_2','#skF_3'))) != k4_xboole_0('#skF_1',k5_xboole_0('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_9])).

tff(c_12,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:15:04 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.48/1.02  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.48/1.02  
% 1.48/1.02  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.48/1.03  %$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.48/1.03  
% 1.48/1.03  %Foreground sorts:
% 1.48/1.03  
% 1.48/1.03  
% 1.48/1.03  %Background operators:
% 1.48/1.03  
% 1.48/1.03  
% 1.48/1.03  %Foreground operators:
% 1.48/1.03  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.48/1.03  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.48/1.03  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.48/1.03  tff('#skF_2', type, '#skF_2': $i).
% 1.48/1.03  tff('#skF_3', type, '#skF_3': $i).
% 1.48/1.03  tff('#skF_1', type, '#skF_1': $i).
% 1.48/1.03  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.48/1.03  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.48/1.03  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.48/1.03  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.48/1.03  
% 1.48/1.04  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k4_xboole_0(k2_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t101_xboole_1)).
% 1.48/1.04  tff(f_31, axiom, (![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_xboole_1)).
% 1.48/1.04  tff(f_29, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 1.48/1.04  tff(f_34, negated_conjecture, ~(![A, B, C]: (k4_xboole_0(A, k5_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, k2_xboole_0(B, C)), k3_xboole_0(k3_xboole_0(A, B), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t102_xboole_1)).
% 1.48/1.04  tff(c_2, plain, (![A_1, B_2]: (k4_xboole_0(k2_xboole_0(A_1, B_2), k3_xboole_0(A_1, B_2))=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.48/1.04  tff(c_6, plain, (![A_6, B_7, C_8]: (k2_xboole_0(k4_xboole_0(A_6, B_7), k3_xboole_0(A_6, C_8))=k4_xboole_0(A_6, k4_xboole_0(B_7, C_8)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.48/1.04  tff(c_4, plain, (![A_3, B_4, C_5]: (k3_xboole_0(k3_xboole_0(A_3, B_4), C_5)=k3_xboole_0(A_3, k3_xboole_0(B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.48/1.04  tff(c_8, plain, (k2_xboole_0(k4_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3')), k3_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), '#skF_3'))!=k4_xboole_0('#skF_1', k5_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.48/1.04  tff(c_9, plain, (k2_xboole_0(k4_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3')), k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3')))!=k4_xboole_0('#skF_1', k5_xboole_0('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_8])).
% 1.48/1.04  tff(c_10, plain, (k4_xboole_0('#skF_1', k4_xboole_0(k2_xboole_0('#skF_2', '#skF_3'), k3_xboole_0('#skF_2', '#skF_3')))!=k4_xboole_0('#skF_1', k5_xboole_0('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_9])).
% 1.48/1.04  tff(c_12, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_10])).
% 1.48/1.04  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.48/1.04  
% 1.48/1.04  Inference rules
% 1.48/1.04  ----------------------
% 1.48/1.04  #Ref     : 0
% 1.48/1.04  #Sup     : 0
% 1.48/1.04  #Fact    : 0
% 1.48/1.04  #Define  : 0
% 1.48/1.04  #Split   : 0
% 1.48/1.04  #Chain   : 0
% 1.48/1.04  #Close   : 0
% 1.48/1.04  
% 1.48/1.04  Ordering : KBO
% 1.48/1.04  
% 1.48/1.04  Simplification rules
% 1.48/1.04  ----------------------
% 1.48/1.04  #Subsume      : 3
% 1.48/1.04  #Demod        : 3
% 1.48/1.04  #Tautology    : 0
% 1.48/1.04  #SimpNegUnit  : 0
% 1.48/1.04  #BackRed      : 0
% 1.48/1.04  
% 1.48/1.04  #Partial instantiations: 0
% 1.48/1.04  #Strategies tried      : 1
% 1.48/1.04  
% 1.48/1.04  Timing (in seconds)
% 1.48/1.04  ----------------------
% 1.48/1.04  Preprocessing        : 0.25
% 1.48/1.04  Parsing              : 0.14
% 1.48/1.04  CNF conversion       : 0.01
% 1.48/1.04  Main loop            : 0.03
% 1.48/1.04  Inferencing          : 0.00
% 1.48/1.04  Reduction            : 0.02
% 1.48/1.04  Demodulation         : 0.02
% 1.48/1.04  BG Simplification    : 0.01
% 1.48/1.05  Subsumption          : 0.01
% 1.48/1.05  Abstraction          : 0.00
% 1.48/1.05  MUC search           : 0.00
% 1.48/1.05  Cooper               : 0.00
% 1.48/1.05  Total                : 0.31
% 1.48/1.05  Index Insertion      : 0.00
% 1.48/1.05  Index Deletion       : 0.00
% 1.48/1.05  Index Matching       : 0.00
% 1.48/1.05  BG Taut test         : 0.00
%------------------------------------------------------------------------------
