%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:31 EST 2020

% Result     : Theorem 3.10s
% Output     : CNFRefutation 3.26s
% Verified   : 
% Statistics : Number of formulae       :   28 (  31 expanded)
%              Number of leaves         :   20 (  22 expanded)
%              Depth                    :    4
%              Number of atoms          :   13 (  17 expanded)
%              Number of equality atoms :   12 (  16 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k3_zfmisc_1 > k3_mcart_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_43,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k1_tarski(A),k2_tarski(B,C)) = k2_tarski(k4_tarski(A,B),k4_tarski(A,C))
      & k2_zfmisc_1(k2_tarski(A,B),k1_tarski(C)) = k2_tarski(k4_tarski(A,C),k4_tarski(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).

tff(f_46,negated_conjecture,(
    ~ ! [A,B,C,D] : k3_zfmisc_1(k1_tarski(A),k2_tarski(B,C),k1_tarski(D)) = k2_tarski(k3_mcart_1(A,B,D),k3_mcart_1(A,C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_mcart_1)).

tff(c_16,plain,(
    ! [A_15,B_16,C_17] : k2_zfmisc_1(k2_zfmisc_1(A_15,B_16),C_17) = k3_zfmisc_1(A_15,B_16,C_17) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_14,plain,(
    ! [A_12,B_13,C_14] : k4_tarski(k4_tarski(A_12,B_13),C_14) = k3_mcart_1(A_12,B_13,C_14) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_10,plain,(
    ! [A_9,B_10,C_11] : k2_zfmisc_1(k1_tarski(A_9),k2_tarski(B_10,C_11)) = k2_tarski(k4_tarski(A_9,B_10),k4_tarski(A_9,C_11)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_220,plain,(
    ! [A_47,B_48,C_49] : k2_zfmisc_1(k2_tarski(A_47,B_48),k1_tarski(C_49)) = k2_tarski(k4_tarski(A_47,C_49),k4_tarski(B_48,C_49)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_254,plain,(
    ! [A_9,B_10,C_11,C_49] : k2_zfmisc_1(k2_zfmisc_1(k1_tarski(A_9),k2_tarski(B_10,C_11)),k1_tarski(C_49)) = k2_tarski(k4_tarski(k4_tarski(A_9,B_10),C_49),k4_tarski(k4_tarski(A_9,C_11),C_49)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_220])).

tff(c_271,plain,(
    ! [A_9,B_10,C_11,C_49] : k3_zfmisc_1(k1_tarski(A_9),k2_tarski(B_10,C_11),k1_tarski(C_49)) = k2_tarski(k3_mcart_1(A_9,B_10,C_49),k3_mcart_1(A_9,C_11,C_49)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_14,c_254])).

tff(c_18,plain,(
    k3_zfmisc_1(k1_tarski('#skF_1'),k2_tarski('#skF_2','#skF_3'),k1_tarski('#skF_4')) != k2_tarski(k3_mcart_1('#skF_1','#skF_2','#skF_4'),k3_mcart_1('#skF_1','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1165,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_271,c_18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:54:34 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.10/1.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.26/1.46  
% 3.26/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.26/1.46  %$ k3_zfmisc_1 > k3_mcart_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.26/1.46  
% 3.26/1.46  %Foreground sorts:
% 3.26/1.46  
% 3.26/1.46  
% 3.26/1.46  %Background operators:
% 3.26/1.46  
% 3.26/1.46  
% 3.26/1.46  %Foreground operators:
% 3.26/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.26/1.46  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.26/1.46  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.26/1.46  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.26/1.46  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 3.26/1.46  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.26/1.46  tff('#skF_2', type, '#skF_2': $i).
% 3.26/1.46  tff('#skF_3', type, '#skF_3': $i).
% 3.26/1.46  tff('#skF_1', type, '#skF_1': $i).
% 3.26/1.46  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 3.26/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.26/1.46  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.26/1.46  tff('#skF_4', type, '#skF_4': $i).
% 3.26/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.26/1.46  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.26/1.46  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.26/1.46  
% 3.26/1.47  tff(f_43, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 3.26/1.47  tff(f_41, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 3.26/1.47  tff(f_39, axiom, (![A, B, C]: ((k2_zfmisc_1(k1_tarski(A), k2_tarski(B, C)) = k2_tarski(k4_tarski(A, B), k4_tarski(A, C))) & (k2_zfmisc_1(k2_tarski(A, B), k1_tarski(C)) = k2_tarski(k4_tarski(A, C), k4_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_zfmisc_1)).
% 3.26/1.47  tff(f_46, negated_conjecture, ~(![A, B, C, D]: (k3_zfmisc_1(k1_tarski(A), k2_tarski(B, C), k1_tarski(D)) = k2_tarski(k3_mcart_1(A, B, D), k3_mcart_1(A, C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_mcart_1)).
% 3.26/1.47  tff(c_16, plain, (![A_15, B_16, C_17]: (k2_zfmisc_1(k2_zfmisc_1(A_15, B_16), C_17)=k3_zfmisc_1(A_15, B_16, C_17))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.26/1.47  tff(c_14, plain, (![A_12, B_13, C_14]: (k4_tarski(k4_tarski(A_12, B_13), C_14)=k3_mcart_1(A_12, B_13, C_14))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.26/1.47  tff(c_10, plain, (![A_9, B_10, C_11]: (k2_zfmisc_1(k1_tarski(A_9), k2_tarski(B_10, C_11))=k2_tarski(k4_tarski(A_9, B_10), k4_tarski(A_9, C_11)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.26/1.47  tff(c_220, plain, (![A_47, B_48, C_49]: (k2_zfmisc_1(k2_tarski(A_47, B_48), k1_tarski(C_49))=k2_tarski(k4_tarski(A_47, C_49), k4_tarski(B_48, C_49)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.26/1.47  tff(c_254, plain, (![A_9, B_10, C_11, C_49]: (k2_zfmisc_1(k2_zfmisc_1(k1_tarski(A_9), k2_tarski(B_10, C_11)), k1_tarski(C_49))=k2_tarski(k4_tarski(k4_tarski(A_9, B_10), C_49), k4_tarski(k4_tarski(A_9, C_11), C_49)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_220])).
% 3.26/1.47  tff(c_271, plain, (![A_9, B_10, C_11, C_49]: (k3_zfmisc_1(k1_tarski(A_9), k2_tarski(B_10, C_11), k1_tarski(C_49))=k2_tarski(k3_mcart_1(A_9, B_10, C_49), k3_mcart_1(A_9, C_11, C_49)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_14, c_14, c_254])).
% 3.26/1.47  tff(c_18, plain, (k3_zfmisc_1(k1_tarski('#skF_1'), k2_tarski('#skF_2', '#skF_3'), k1_tarski('#skF_4'))!=k2_tarski(k3_mcart_1('#skF_1', '#skF_2', '#skF_4'), k3_mcart_1('#skF_1', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.26/1.47  tff(c_1165, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_271, c_18])).
% 3.26/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.26/1.47  
% 3.26/1.47  Inference rules
% 3.26/1.47  ----------------------
% 3.26/1.47  #Ref     : 0
% 3.26/1.47  #Sup     : 289
% 3.26/1.47  #Fact    : 0
% 3.26/1.47  #Define  : 0
% 3.26/1.47  #Split   : 0
% 3.26/1.47  #Chain   : 0
% 3.26/1.47  #Close   : 0
% 3.26/1.47  
% 3.26/1.47  Ordering : KBO
% 3.26/1.47  
% 3.26/1.47  Simplification rules
% 3.26/1.47  ----------------------
% 3.26/1.47  #Subsume      : 25
% 3.26/1.47  #Demod        : 135
% 3.26/1.47  #Tautology    : 113
% 3.26/1.47  #SimpNegUnit  : 0
% 3.26/1.47  #BackRed      : 1
% 3.26/1.47  
% 3.26/1.47  #Partial instantiations: 0
% 3.26/1.47  #Strategies tried      : 1
% 3.26/1.47  
% 3.26/1.47  Timing (in seconds)
% 3.26/1.47  ----------------------
% 3.26/1.47  Preprocessing        : 0.28
% 3.26/1.47  Parsing              : 0.15
% 3.26/1.47  CNF conversion       : 0.01
% 3.26/1.47  Main loop            : 0.45
% 3.26/1.47  Inferencing          : 0.17
% 3.26/1.47  Reduction            : 0.17
% 3.26/1.47  Demodulation         : 0.14
% 3.26/1.47  BG Simplification    : 0.03
% 3.26/1.47  Subsumption          : 0.06
% 3.26/1.47  Abstraction          : 0.04
% 3.26/1.47  MUC search           : 0.00
% 3.26/1.47  Cooper               : 0.00
% 3.26/1.47  Total                : 0.75
% 3.26/1.47  Index Insertion      : 0.00
% 3.26/1.47  Index Deletion       : 0.00
% 3.26/1.47  Index Matching       : 0.00
% 3.26/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
