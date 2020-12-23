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
% DateTime   : Thu Dec  3 10:09:53 EST 2020

% Result     : Theorem 2.17s
% Output     : CNFRefutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :   40 (  60 expanded)
%              Number of leaves         :   23 (  32 expanded)
%              Depth                    :    6
%              Number of atoms          :   25 (  47 expanded)
%              Number of equality atoms :   24 (  46 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_zfmisc_1 > k4_mcart_1 > k2_enumset1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff(k4_zfmisc_1,type,(
    k4_zfmisc_1: ( $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff(k4_mcart_1,type,(
    k4_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(f_39,axiom,(
    ! [A,B,C,D] : k4_mcart_1(A,B,C,D) = k4_tarski(k3_mcart_1(A,B,C),D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_mcart_1)).

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k1_tarski(A),k2_tarski(B,C)) = k2_tarski(k4_tarski(A,B),k4_tarski(A,C))
      & k2_zfmisc_1(k2_tarski(A,B),k1_tarski(C)) = k2_tarski(k4_tarski(A,C),k4_tarski(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_37,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B,C,D] : k4_zfmisc_1(A,B,C,D) = k2_zfmisc_1(k3_zfmisc_1(A,B,C),D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).

tff(f_44,negated_conjecture,(
    ~ ! [A,B,C,D] : k4_zfmisc_1(k1_tarski(A),k1_tarski(B),k1_tarski(C),k1_tarski(D)) = k1_tarski(k4_mcart_1(A,B,C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_mcart_1)).

tff(c_14,plain,(
    ! [A_13,B_14,C_15,D_16] : k4_tarski(k3_mcart_1(A_13,B_14,C_15),D_16) = k4_mcart_1(A_13,B_14,C_15,D_16) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_131,plain,(
    ! [A_46,B_47,C_48] : k2_zfmisc_1(k2_tarski(A_46,B_47),k1_tarski(C_48)) = k2_tarski(k4_tarski(A_46,C_48),k4_tarski(B_47,C_48)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_150,plain,(
    ! [B_47,C_48] : k2_zfmisc_1(k2_tarski(B_47,B_47),k1_tarski(C_48)) = k1_tarski(k4_tarski(B_47,C_48)) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_2])).

tff(c_182,plain,(
    ! [B_47,C_48] : k2_zfmisc_1(k1_tarski(B_47),k1_tarski(C_48)) = k1_tarski(k4_tarski(B_47,C_48)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_150])).

tff(c_10,plain,(
    ! [A_7,B_8,C_9] : k4_tarski(k4_tarski(A_7,B_8),C_9) = k3_mcart_1(A_7,B_8,C_9) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_188,plain,(
    ! [B_49,C_50] : k2_zfmisc_1(k1_tarski(B_49),k1_tarski(C_50)) = k1_tarski(k4_tarski(B_49,C_50)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_150])).

tff(c_12,plain,(
    ! [A_10,B_11,C_12] : k2_zfmisc_1(k2_zfmisc_1(A_10,B_11),C_12) = k3_zfmisc_1(A_10,B_11,C_12) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_197,plain,(
    ! [B_49,C_50,C_12] : k3_zfmisc_1(k1_tarski(B_49),k1_tarski(C_50),C_12) = k2_zfmisc_1(k1_tarski(k4_tarski(B_49,C_50)),C_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_188,c_12])).

tff(c_16,plain,(
    ! [A_17,B_18,C_19,D_20] : k2_zfmisc_1(k3_zfmisc_1(A_17,B_18,C_19),D_20) = k4_zfmisc_1(A_17,B_18,C_19,D_20) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_52,plain,(
    ! [A_27,B_28,C_29] : k2_zfmisc_1(k2_zfmisc_1(A_27,B_28),C_29) = k3_zfmisc_1(A_27,B_28,C_29) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_61,plain,(
    ! [A_10,B_11,C_12,C_29] : k3_zfmisc_1(k2_zfmisc_1(A_10,B_11),C_12,C_29) = k2_zfmisc_1(k3_zfmisc_1(A_10,B_11,C_12),C_29) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_52])).

tff(c_91,plain,(
    ! [A_10,B_11,C_12,C_29] : k3_zfmisc_1(k2_zfmisc_1(A_10,B_11),C_12,C_29) = k4_zfmisc_1(A_10,B_11,C_12,C_29) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_61])).

tff(c_194,plain,(
    ! [B_49,C_50,C_12,C_29] : k4_zfmisc_1(k1_tarski(B_49),k1_tarski(C_50),C_12,C_29) = k3_zfmisc_1(k1_tarski(k4_tarski(B_49,C_50)),C_12,C_29) ),
    inference(superposition,[status(thm),theory(equality)],[c_188,c_91])).

tff(c_18,plain,(
    k4_zfmisc_1(k1_tarski('#skF_1'),k1_tarski('#skF_2'),k1_tarski('#skF_3'),k1_tarski('#skF_4')) != k1_tarski(k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_388,plain,(
    k3_zfmisc_1(k1_tarski(k4_tarski('#skF_1','#skF_2')),k1_tarski('#skF_3'),k1_tarski('#skF_4')) != k1_tarski(k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_18])).

tff(c_391,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_182,c_10,c_197,c_388])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 09:29:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.17/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.29  
% 2.17/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.30  %$ k4_zfmisc_1 > k4_mcart_1 > k2_enumset1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.17/1.30  
% 2.17/1.30  %Foreground sorts:
% 2.17/1.30  
% 2.17/1.30  
% 2.17/1.30  %Background operators:
% 2.17/1.30  
% 2.17/1.30  
% 2.17/1.30  %Foreground operators:
% 2.17/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.17/1.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.17/1.30  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.17/1.30  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 2.17/1.30  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 2.17/1.30  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.17/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.17/1.30  tff('#skF_2', type, '#skF_2': $i).
% 2.17/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.17/1.30  tff('#skF_1', type, '#skF_1': $i).
% 2.17/1.30  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 2.17/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.17/1.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.17/1.30  tff('#skF_4', type, '#skF_4': $i).
% 2.17/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.17/1.30  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 2.17/1.30  
% 2.17/1.31  tff(f_39, axiom, (![A, B, C, D]: (k4_mcart_1(A, B, C, D) = k4_tarski(k3_mcart_1(A, B, C), D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_mcart_1)).
% 2.17/1.31  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.17/1.31  tff(f_33, axiom, (![A, B, C]: ((k2_zfmisc_1(k1_tarski(A), k2_tarski(B, C)) = k2_tarski(k4_tarski(A, B), k4_tarski(A, C))) & (k2_zfmisc_1(k2_tarski(A, B), k1_tarski(C)) = k2_tarski(k4_tarski(A, C), k4_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_zfmisc_1)).
% 2.17/1.31  tff(f_35, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 2.17/1.31  tff(f_37, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 2.17/1.31  tff(f_41, axiom, (![A, B, C, D]: (k4_zfmisc_1(A, B, C, D) = k2_zfmisc_1(k3_zfmisc_1(A, B, C), D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 2.17/1.31  tff(f_44, negated_conjecture, ~(![A, B, C, D]: (k4_zfmisc_1(k1_tarski(A), k1_tarski(B), k1_tarski(C), k1_tarski(D)) = k1_tarski(k4_mcart_1(A, B, C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_mcart_1)).
% 2.17/1.31  tff(c_14, plain, (![A_13, B_14, C_15, D_16]: (k4_tarski(k3_mcart_1(A_13, B_14, C_15), D_16)=k4_mcart_1(A_13, B_14, C_15, D_16))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.17/1.31  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.17/1.31  tff(c_131, plain, (![A_46, B_47, C_48]: (k2_zfmisc_1(k2_tarski(A_46, B_47), k1_tarski(C_48))=k2_tarski(k4_tarski(A_46, C_48), k4_tarski(B_47, C_48)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.17/1.31  tff(c_150, plain, (![B_47, C_48]: (k2_zfmisc_1(k2_tarski(B_47, B_47), k1_tarski(C_48))=k1_tarski(k4_tarski(B_47, C_48)))), inference(superposition, [status(thm), theory('equality')], [c_131, c_2])).
% 2.17/1.31  tff(c_182, plain, (![B_47, C_48]: (k2_zfmisc_1(k1_tarski(B_47), k1_tarski(C_48))=k1_tarski(k4_tarski(B_47, C_48)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_150])).
% 2.17/1.31  tff(c_10, plain, (![A_7, B_8, C_9]: (k4_tarski(k4_tarski(A_7, B_8), C_9)=k3_mcart_1(A_7, B_8, C_9))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.17/1.31  tff(c_188, plain, (![B_49, C_50]: (k2_zfmisc_1(k1_tarski(B_49), k1_tarski(C_50))=k1_tarski(k4_tarski(B_49, C_50)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_150])).
% 2.17/1.31  tff(c_12, plain, (![A_10, B_11, C_12]: (k2_zfmisc_1(k2_zfmisc_1(A_10, B_11), C_12)=k3_zfmisc_1(A_10, B_11, C_12))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.17/1.31  tff(c_197, plain, (![B_49, C_50, C_12]: (k3_zfmisc_1(k1_tarski(B_49), k1_tarski(C_50), C_12)=k2_zfmisc_1(k1_tarski(k4_tarski(B_49, C_50)), C_12))), inference(superposition, [status(thm), theory('equality')], [c_188, c_12])).
% 2.17/1.31  tff(c_16, plain, (![A_17, B_18, C_19, D_20]: (k2_zfmisc_1(k3_zfmisc_1(A_17, B_18, C_19), D_20)=k4_zfmisc_1(A_17, B_18, C_19, D_20))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.17/1.31  tff(c_52, plain, (![A_27, B_28, C_29]: (k2_zfmisc_1(k2_zfmisc_1(A_27, B_28), C_29)=k3_zfmisc_1(A_27, B_28, C_29))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.17/1.31  tff(c_61, plain, (![A_10, B_11, C_12, C_29]: (k3_zfmisc_1(k2_zfmisc_1(A_10, B_11), C_12, C_29)=k2_zfmisc_1(k3_zfmisc_1(A_10, B_11, C_12), C_29))), inference(superposition, [status(thm), theory('equality')], [c_12, c_52])).
% 2.17/1.31  tff(c_91, plain, (![A_10, B_11, C_12, C_29]: (k3_zfmisc_1(k2_zfmisc_1(A_10, B_11), C_12, C_29)=k4_zfmisc_1(A_10, B_11, C_12, C_29))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_61])).
% 2.17/1.31  tff(c_194, plain, (![B_49, C_50, C_12, C_29]: (k4_zfmisc_1(k1_tarski(B_49), k1_tarski(C_50), C_12, C_29)=k3_zfmisc_1(k1_tarski(k4_tarski(B_49, C_50)), C_12, C_29))), inference(superposition, [status(thm), theory('equality')], [c_188, c_91])).
% 2.17/1.31  tff(c_18, plain, (k4_zfmisc_1(k1_tarski('#skF_1'), k1_tarski('#skF_2'), k1_tarski('#skF_3'), k1_tarski('#skF_4'))!=k1_tarski(k4_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.17/1.31  tff(c_388, plain, (k3_zfmisc_1(k1_tarski(k4_tarski('#skF_1', '#skF_2')), k1_tarski('#skF_3'), k1_tarski('#skF_4'))!=k1_tarski(k4_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_194, c_18])).
% 2.17/1.31  tff(c_391, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_182, c_10, c_197, c_388])).
% 2.17/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.31  
% 2.17/1.31  Inference rules
% 2.17/1.31  ----------------------
% 2.17/1.31  #Ref     : 0
% 2.17/1.31  #Sup     : 93
% 2.17/1.31  #Fact    : 0
% 2.17/1.31  #Define  : 0
% 2.17/1.31  #Split   : 0
% 2.17/1.31  #Chain   : 0
% 2.17/1.31  #Close   : 0
% 2.17/1.31  
% 2.17/1.31  Ordering : KBO
% 2.17/1.31  
% 2.17/1.31  Simplification rules
% 2.17/1.31  ----------------------
% 2.17/1.31  #Subsume      : 0
% 2.17/1.31  #Demod        : 53
% 2.17/1.31  #Tautology    : 46
% 2.17/1.31  #SimpNegUnit  : 0
% 2.17/1.31  #BackRed      : 1
% 2.17/1.31  
% 2.17/1.31  #Partial instantiations: 0
% 2.17/1.31  #Strategies tried      : 1
% 2.17/1.31  
% 2.17/1.31  Timing (in seconds)
% 2.17/1.31  ----------------------
% 2.17/1.31  Preprocessing        : 0.30
% 2.17/1.31  Parsing              : 0.16
% 2.17/1.31  CNF conversion       : 0.02
% 2.17/1.31  Main loop            : 0.26
% 2.17/1.31  Inferencing          : 0.11
% 2.17/1.31  Reduction            : 0.09
% 2.17/1.31  Demodulation         : 0.07
% 2.17/1.31  BG Simplification    : 0.02
% 2.17/1.31  Subsumption          : 0.03
% 2.17/1.31  Abstraction          : 0.03
% 2.17/1.31  MUC search           : 0.00
% 2.17/1.31  Cooper               : 0.00
% 2.17/1.31  Total                : 0.58
% 2.17/1.31  Index Insertion      : 0.00
% 2.17/1.31  Index Deletion       : 0.00
% 2.17/1.31  Index Matching       : 0.00
% 2.17/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
