%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:54 EST 2020

% Result     : Theorem 2.32s
% Output     : CNFRefutation 2.53s
% Verified   : 
% Statistics : Number of formulae       :   41 (  65 expanded)
%              Number of leaves         :   22 (  33 expanded)
%              Depth                    :    6
%              Number of atoms          :   27 (  53 expanded)
%              Number of equality atoms :   26 (  52 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_zfmisc_1 > k4_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_33,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_37,axiom,(
    ! [A,B,C,D] : k4_mcart_1(A,B,C,D) = k4_tarski(k4_tarski(k4_tarski(A,B),C),D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_mcart_1)).

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k1_tarski(A),k2_tarski(B,C)) = k2_tarski(k4_tarski(A,B),k4_tarski(A,C))
      & k2_zfmisc_1(k2_tarski(A,B),k1_tarski(C)) = k2_tarski(k4_tarski(A,C),k4_tarski(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B,C,D] : k4_zfmisc_1(A,B,C,D) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A,B),C),D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_mcart_1)).

tff(f_44,negated_conjecture,(
    ~ ! [A,B,C,D] : k4_zfmisc_1(k1_tarski(A),k1_tarski(B),k1_tarski(C),k1_tarski(D)) = k1_tarski(k4_mcart_1(A,B,C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_mcart_1)).

tff(c_8,plain,(
    ! [A_5,B_6,C_7] : k4_tarski(k4_tarski(A_5,B_6),C_7) = k3_mcart_1(A_5,B_6,C_7) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12,plain,(
    ! [A_11,B_12,C_13,D_14] : k4_tarski(k4_tarski(k4_tarski(A_11,B_12),C_13),D_14) = k4_mcart_1(A_11,B_12,C_13,D_14) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_20,plain,(
    ! [A_11,B_12,C_13,D_14] : k4_tarski(k3_mcart_1(A_11,B_12,C_13),D_14) = k4_mcart_1(A_11,B_12,C_13,D_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_12])).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_84,plain,(
    ! [A_38,B_39,C_40] : k2_zfmisc_1(k1_tarski(A_38),k2_tarski(B_39,C_40)) = k2_tarski(k4_tarski(A_38,B_39),k4_tarski(A_38,C_40)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_100,plain,(
    ! [A_38,C_40] : k2_zfmisc_1(k1_tarski(A_38),k2_tarski(C_40,C_40)) = k1_tarski(k4_tarski(A_38,C_40)) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_2])).

tff(c_131,plain,(
    ! [A_38,C_40] : k2_zfmisc_1(k1_tarski(A_38),k1_tarski(C_40)) = k1_tarski(k4_tarski(A_38,C_40)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_100])).

tff(c_140,plain,(
    ! [A_41,C_42] : k2_zfmisc_1(k1_tarski(A_41),k1_tarski(C_42)) = k1_tarski(k4_tarski(A_41,C_42)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_100])).

tff(c_10,plain,(
    ! [A_8,B_9,C_10] : k2_zfmisc_1(k2_zfmisc_1(A_8,B_9),C_10) = k3_zfmisc_1(A_8,B_9,C_10) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_146,plain,(
    ! [A_41,C_42,C_10] : k3_zfmisc_1(k1_tarski(A_41),k1_tarski(C_42),C_10) = k2_zfmisc_1(k1_tarski(k4_tarski(A_41,C_42)),C_10) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_10])).

tff(c_16,plain,(
    ! [A_19,B_20,C_21,D_22] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_19,B_20),C_21),D_22) = k4_zfmisc_1(A_19,B_20,C_21,D_22) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_19,plain,(
    ! [A_19,B_20,C_21,D_22] : k2_zfmisc_1(k3_zfmisc_1(A_19,B_20,C_21),D_22) = k4_zfmisc_1(A_19,B_20,C_21,D_22) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_16])).

tff(c_30,plain,(
    ! [A_24,B_25,C_26] : k2_zfmisc_1(k2_zfmisc_1(A_24,B_25),C_26) = k3_zfmisc_1(A_24,B_25,C_26) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_33,plain,(
    ! [A_24,B_25,C_26,C_10] : k3_zfmisc_1(k2_zfmisc_1(A_24,B_25),C_26,C_10) = k2_zfmisc_1(k3_zfmisc_1(A_24,B_25,C_26),C_10) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_10])).

tff(c_155,plain,(
    ! [A_43,B_44,C_45,C_46] : k3_zfmisc_1(k2_zfmisc_1(A_43,B_44),C_45,C_46) = k4_zfmisc_1(A_43,B_44,C_45,C_46) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19,c_33])).

tff(c_167,plain,(
    ! [A_38,C_40,C_45,C_46] : k4_zfmisc_1(k1_tarski(A_38),k1_tarski(C_40),C_45,C_46) = k3_zfmisc_1(k1_tarski(k4_tarski(A_38,C_40)),C_45,C_46) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_155])).

tff(c_18,plain,(
    k4_zfmisc_1(k1_tarski('#skF_1'),k1_tarski('#skF_2'),k1_tarski('#skF_3'),k1_tarski('#skF_4')) != k1_tarski(k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_510,plain,(
    k3_zfmisc_1(k1_tarski(k4_tarski('#skF_1','#skF_2')),k1_tarski('#skF_3'),k1_tarski('#skF_4')) != k1_tarski(k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_18])).

tff(c_513,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_131,c_8,c_146,c_510])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:18:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.32/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/1.35  
% 2.32/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/1.35  %$ k4_zfmisc_1 > k4_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.32/1.35  
% 2.32/1.35  %Foreground sorts:
% 2.32/1.35  
% 2.32/1.35  
% 2.32/1.35  %Background operators:
% 2.32/1.35  
% 2.32/1.35  
% 2.32/1.35  %Foreground operators:
% 2.32/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.32/1.35  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.32/1.35  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.32/1.35  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 2.32/1.35  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 2.32/1.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.32/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.32/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.32/1.35  tff('#skF_1', type, '#skF_1': $i).
% 2.32/1.35  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 2.32/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.32/1.35  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.32/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.32/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.32/1.35  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 2.32/1.35  
% 2.53/1.36  tff(f_33, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 2.53/1.36  tff(f_37, axiom, (![A, B, C, D]: (k4_mcart_1(A, B, C, D) = k4_tarski(k4_tarski(k4_tarski(A, B), C), D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_mcart_1)).
% 2.53/1.36  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.53/1.36  tff(f_31, axiom, (![A, B, C]: ((k2_zfmisc_1(k1_tarski(A), k2_tarski(B, C)) = k2_tarski(k4_tarski(A, B), k4_tarski(A, C))) & (k2_zfmisc_1(k2_tarski(A, B), k1_tarski(C)) = k2_tarski(k4_tarski(A, C), k4_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_zfmisc_1)).
% 2.53/1.36  tff(f_35, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 2.53/1.36  tff(f_41, axiom, (![A, B, C, D]: (k4_zfmisc_1(A, B, C, D) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A, B), C), D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_mcart_1)).
% 2.53/1.36  tff(f_44, negated_conjecture, ~(![A, B, C, D]: (k4_zfmisc_1(k1_tarski(A), k1_tarski(B), k1_tarski(C), k1_tarski(D)) = k1_tarski(k4_mcart_1(A, B, C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_mcart_1)).
% 2.53/1.36  tff(c_8, plain, (![A_5, B_6, C_7]: (k4_tarski(k4_tarski(A_5, B_6), C_7)=k3_mcart_1(A_5, B_6, C_7))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.53/1.36  tff(c_12, plain, (![A_11, B_12, C_13, D_14]: (k4_tarski(k4_tarski(k4_tarski(A_11, B_12), C_13), D_14)=k4_mcart_1(A_11, B_12, C_13, D_14))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.53/1.36  tff(c_20, plain, (![A_11, B_12, C_13, D_14]: (k4_tarski(k3_mcart_1(A_11, B_12, C_13), D_14)=k4_mcart_1(A_11, B_12, C_13, D_14))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_12])).
% 2.53/1.36  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.53/1.36  tff(c_84, plain, (![A_38, B_39, C_40]: (k2_zfmisc_1(k1_tarski(A_38), k2_tarski(B_39, C_40))=k2_tarski(k4_tarski(A_38, B_39), k4_tarski(A_38, C_40)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.53/1.36  tff(c_100, plain, (![A_38, C_40]: (k2_zfmisc_1(k1_tarski(A_38), k2_tarski(C_40, C_40))=k1_tarski(k4_tarski(A_38, C_40)))), inference(superposition, [status(thm), theory('equality')], [c_84, c_2])).
% 2.53/1.36  tff(c_131, plain, (![A_38, C_40]: (k2_zfmisc_1(k1_tarski(A_38), k1_tarski(C_40))=k1_tarski(k4_tarski(A_38, C_40)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_100])).
% 2.53/1.36  tff(c_140, plain, (![A_41, C_42]: (k2_zfmisc_1(k1_tarski(A_41), k1_tarski(C_42))=k1_tarski(k4_tarski(A_41, C_42)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_100])).
% 2.53/1.36  tff(c_10, plain, (![A_8, B_9, C_10]: (k2_zfmisc_1(k2_zfmisc_1(A_8, B_9), C_10)=k3_zfmisc_1(A_8, B_9, C_10))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.53/1.36  tff(c_146, plain, (![A_41, C_42, C_10]: (k3_zfmisc_1(k1_tarski(A_41), k1_tarski(C_42), C_10)=k2_zfmisc_1(k1_tarski(k4_tarski(A_41, C_42)), C_10))), inference(superposition, [status(thm), theory('equality')], [c_140, c_10])).
% 2.53/1.36  tff(c_16, plain, (![A_19, B_20, C_21, D_22]: (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_19, B_20), C_21), D_22)=k4_zfmisc_1(A_19, B_20, C_21, D_22))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.53/1.36  tff(c_19, plain, (![A_19, B_20, C_21, D_22]: (k2_zfmisc_1(k3_zfmisc_1(A_19, B_20, C_21), D_22)=k4_zfmisc_1(A_19, B_20, C_21, D_22))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_16])).
% 2.53/1.36  tff(c_30, plain, (![A_24, B_25, C_26]: (k2_zfmisc_1(k2_zfmisc_1(A_24, B_25), C_26)=k3_zfmisc_1(A_24, B_25, C_26))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.53/1.36  tff(c_33, plain, (![A_24, B_25, C_26, C_10]: (k3_zfmisc_1(k2_zfmisc_1(A_24, B_25), C_26, C_10)=k2_zfmisc_1(k3_zfmisc_1(A_24, B_25, C_26), C_10))), inference(superposition, [status(thm), theory('equality')], [c_30, c_10])).
% 2.53/1.36  tff(c_155, plain, (![A_43, B_44, C_45, C_46]: (k3_zfmisc_1(k2_zfmisc_1(A_43, B_44), C_45, C_46)=k4_zfmisc_1(A_43, B_44, C_45, C_46))), inference(demodulation, [status(thm), theory('equality')], [c_19, c_33])).
% 2.53/1.36  tff(c_167, plain, (![A_38, C_40, C_45, C_46]: (k4_zfmisc_1(k1_tarski(A_38), k1_tarski(C_40), C_45, C_46)=k3_zfmisc_1(k1_tarski(k4_tarski(A_38, C_40)), C_45, C_46))), inference(superposition, [status(thm), theory('equality')], [c_131, c_155])).
% 2.53/1.36  tff(c_18, plain, (k4_zfmisc_1(k1_tarski('#skF_1'), k1_tarski('#skF_2'), k1_tarski('#skF_3'), k1_tarski('#skF_4'))!=k1_tarski(k4_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.53/1.36  tff(c_510, plain, (k3_zfmisc_1(k1_tarski(k4_tarski('#skF_1', '#skF_2')), k1_tarski('#skF_3'), k1_tarski('#skF_4'))!=k1_tarski(k4_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_167, c_18])).
% 2.53/1.36  tff(c_513, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_131, c_8, c_146, c_510])).
% 2.53/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.53/1.36  
% 2.53/1.36  Inference rules
% 2.53/1.36  ----------------------
% 2.53/1.36  #Ref     : 0
% 2.53/1.36  #Sup     : 125
% 2.53/1.36  #Fact    : 0
% 2.53/1.36  #Define  : 0
% 2.53/1.36  #Split   : 0
% 2.53/1.36  #Chain   : 0
% 2.53/1.36  #Close   : 0
% 2.53/1.36  
% 2.53/1.36  Ordering : KBO
% 2.53/1.36  
% 2.53/1.36  Simplification rules
% 2.53/1.36  ----------------------
% 2.53/1.36  #Subsume      : 0
% 2.53/1.36  #Demod        : 80
% 2.53/1.36  #Tautology    : 58
% 2.53/1.36  #SimpNegUnit  : 0
% 2.53/1.36  #BackRed      : 1
% 2.53/1.36  
% 2.53/1.36  #Partial instantiations: 0
% 2.53/1.36  #Strategies tried      : 1
% 2.53/1.36  
% 2.53/1.36  Timing (in seconds)
% 2.53/1.36  ----------------------
% 2.53/1.36  Preprocessing        : 0.28
% 2.53/1.36  Parsing              : 0.14
% 2.53/1.36  CNF conversion       : 0.01
% 2.53/1.36  Main loop            : 0.27
% 2.53/1.36  Inferencing          : 0.11
% 2.53/1.36  Reduction            : 0.10
% 2.53/1.36  Demodulation         : 0.08
% 2.53/1.36  BG Simplification    : 0.02
% 2.53/1.36  Subsumption          : 0.03
% 2.53/1.36  Abstraction          : 0.03
% 2.53/1.36  MUC search           : 0.00
% 2.53/1.36  Cooper               : 0.00
% 2.53/1.36  Total                : 0.57
% 2.53/1.36  Index Insertion      : 0.00
% 2.53/1.36  Index Deletion       : 0.00
% 2.53/1.36  Index Matching       : 0.00
% 2.53/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
