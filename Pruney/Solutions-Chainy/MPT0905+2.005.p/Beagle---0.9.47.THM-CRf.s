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
% DateTime   : Thu Dec  3 10:09:53 EST 2020

% Result     : Theorem 2.00s
% Output     : CNFRefutation 2.00s
% Verified   : 
% Statistics : Number of formulae       :   38 (  45 expanded)
%              Number of leaves         :   21 (  25 expanded)
%              Depth                    :    6
%              Number of atoms          :   24 (  31 expanded)
%              Number of equality atoms :   23 (  30 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_zfmisc_1 > k4_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_29,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_33,axiom,(
    ! [A,B,C,D] : k4_mcart_1(A,B,C,D) = k4_tarski(k4_tarski(k4_tarski(A,B),C),D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_mcart_1)).

tff(f_35,axiom,(
    ! [A,B,C] : k3_zfmisc_1(k1_tarski(A),k1_tarski(B),k1_tarski(C)) = k1_tarski(k3_mcart_1(A,B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_mcart_1)).

tff(f_31,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_zfmisc_1(k1_tarski(A),k1_tarski(B)) = k1_tarski(k4_tarski(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B,C,D] : k4_zfmisc_1(A,B,C,D) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A,B),C),D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_mcart_1)).

tff(f_40,negated_conjecture,(
    ~ ! [A,B,C,D] : k4_zfmisc_1(k1_tarski(A),k1_tarski(B),k1_tarski(C),k1_tarski(D)) = k1_tarski(k4_mcart_1(A,B,C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_mcart_1)).

tff(c_4,plain,(
    ! [A_3,B_4,C_5] : k4_tarski(k4_tarski(A_3,B_4),C_5) = k3_mcart_1(A_3,B_4,C_5) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_8,plain,(
    ! [A_9,B_10,C_11,D_12] : k4_tarski(k4_tarski(k4_tarski(A_9,B_10),C_11),D_12) = k4_mcart_1(A_9,B_10,C_11,D_12) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_16,plain,(
    ! [A_9,B_10,C_11,D_12] : k4_tarski(k3_mcart_1(A_9,B_10,C_11),D_12) = k4_mcart_1(A_9,B_10,C_11,D_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_8])).

tff(c_32,plain,(
    ! [A_23,B_24,C_25] : k4_tarski(k4_tarski(A_23,B_24),C_25) = k3_mcart_1(A_23,B_24,C_25) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_41,plain,(
    ! [A_3,B_4,C_5,C_25] : k3_mcart_1(k4_tarski(A_3,B_4),C_5,C_25) = k4_tarski(k3_mcart_1(A_3,B_4,C_5),C_25) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_32])).

tff(c_117,plain,(
    ! [A_3,B_4,C_5,C_25] : k3_mcart_1(k4_tarski(A_3,B_4),C_5,C_25) = k4_mcart_1(A_3,B_4,C_5,C_25) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_41])).

tff(c_10,plain,(
    ! [A_13,B_14,C_15] : k3_zfmisc_1(k1_tarski(A_13),k1_tarski(B_14),k1_tarski(C_15)) = k1_tarski(k3_mcart_1(A_13,B_14,C_15)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6,plain,(
    ! [A_6,B_7,C_8] : k2_zfmisc_1(k2_zfmisc_1(A_6,B_7),C_8) = k3_zfmisc_1(A_6,B_7,C_8) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_47,plain,(
    ! [A_26,B_27] : k2_zfmisc_1(k1_tarski(A_26),k1_tarski(B_27)) = k1_tarski(k4_tarski(A_26,B_27)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_136,plain,(
    ! [A_47,B_48,C_49] : k3_zfmisc_1(k1_tarski(A_47),k1_tarski(B_48),C_49) = k2_zfmisc_1(k1_tarski(k4_tarski(A_47,B_48)),C_49) ),
    inference(superposition,[status(thm),theory(equality)],[c_47,c_6])).

tff(c_12,plain,(
    ! [A_16,B_17,C_18,D_19] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_16,B_17),C_18),D_19) = k4_zfmisc_1(A_16,B_17,C_18,D_19) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_15,plain,(
    ! [A_16,B_17,C_18,D_19] : k2_zfmisc_1(k3_zfmisc_1(A_16,B_17,C_18),D_19) = k4_zfmisc_1(A_16,B_17,C_18,D_19) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_12])).

tff(c_146,plain,(
    ! [A_47,B_48,C_49,D_19] : k2_zfmisc_1(k2_zfmisc_1(k1_tarski(k4_tarski(A_47,B_48)),C_49),D_19) = k4_zfmisc_1(k1_tarski(A_47),k1_tarski(B_48),C_49,D_19) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_15])).

tff(c_154,plain,(
    ! [A_47,B_48,C_49,D_19] : k4_zfmisc_1(k1_tarski(A_47),k1_tarski(B_48),C_49,D_19) = k3_zfmisc_1(k1_tarski(k4_tarski(A_47,B_48)),C_49,D_19) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_146])).

tff(c_14,plain,(
    k4_zfmisc_1(k1_tarski('#skF_1'),k1_tarski('#skF_2'),k1_tarski('#skF_3'),k1_tarski('#skF_4')) != k1_tarski(k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_285,plain,(
    k3_zfmisc_1(k1_tarski(k4_tarski('#skF_1','#skF_2')),k1_tarski('#skF_3'),k1_tarski('#skF_4')) != k1_tarski(k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_14])).

tff(c_288,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_10,c_285])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:40:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.00/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.22  
% 2.00/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.22  %$ k4_zfmisc_1 > k4_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.00/1.22  
% 2.00/1.22  %Foreground sorts:
% 2.00/1.22  
% 2.00/1.22  
% 2.00/1.22  %Background operators:
% 2.00/1.22  
% 2.00/1.22  
% 2.00/1.22  %Foreground operators:
% 2.00/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.00/1.22  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.00/1.22  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.00/1.22  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 2.00/1.22  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 2.00/1.22  tff('#skF_2', type, '#skF_2': $i).
% 2.00/1.22  tff('#skF_3', type, '#skF_3': $i).
% 2.00/1.22  tff('#skF_1', type, '#skF_1': $i).
% 2.00/1.22  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 2.00/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.00/1.22  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.00/1.22  tff('#skF_4', type, '#skF_4': $i).
% 2.00/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.00/1.22  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 2.00/1.22  
% 2.00/1.23  tff(f_29, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 2.00/1.23  tff(f_33, axiom, (![A, B, C, D]: (k4_mcart_1(A, B, C, D) = k4_tarski(k4_tarski(k4_tarski(A, B), C), D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_mcart_1)).
% 2.00/1.23  tff(f_35, axiom, (![A, B, C]: (k3_zfmisc_1(k1_tarski(A), k1_tarski(B), k1_tarski(C)) = k1_tarski(k3_mcart_1(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_mcart_1)).
% 2.00/1.23  tff(f_31, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 2.00/1.23  tff(f_27, axiom, (![A, B]: (k2_zfmisc_1(k1_tarski(A), k1_tarski(B)) = k1_tarski(k4_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_zfmisc_1)).
% 2.00/1.23  tff(f_37, axiom, (![A, B, C, D]: (k4_zfmisc_1(A, B, C, D) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A, B), C), D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_mcart_1)).
% 2.00/1.23  tff(f_40, negated_conjecture, ~(![A, B, C, D]: (k4_zfmisc_1(k1_tarski(A), k1_tarski(B), k1_tarski(C), k1_tarski(D)) = k1_tarski(k4_mcart_1(A, B, C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_mcart_1)).
% 2.00/1.23  tff(c_4, plain, (![A_3, B_4, C_5]: (k4_tarski(k4_tarski(A_3, B_4), C_5)=k3_mcart_1(A_3, B_4, C_5))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.00/1.23  tff(c_8, plain, (![A_9, B_10, C_11, D_12]: (k4_tarski(k4_tarski(k4_tarski(A_9, B_10), C_11), D_12)=k4_mcart_1(A_9, B_10, C_11, D_12))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.00/1.23  tff(c_16, plain, (![A_9, B_10, C_11, D_12]: (k4_tarski(k3_mcart_1(A_9, B_10, C_11), D_12)=k4_mcart_1(A_9, B_10, C_11, D_12))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_8])).
% 2.00/1.23  tff(c_32, plain, (![A_23, B_24, C_25]: (k4_tarski(k4_tarski(A_23, B_24), C_25)=k3_mcart_1(A_23, B_24, C_25))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.00/1.23  tff(c_41, plain, (![A_3, B_4, C_5, C_25]: (k3_mcart_1(k4_tarski(A_3, B_4), C_5, C_25)=k4_tarski(k3_mcart_1(A_3, B_4, C_5), C_25))), inference(superposition, [status(thm), theory('equality')], [c_4, c_32])).
% 2.00/1.23  tff(c_117, plain, (![A_3, B_4, C_5, C_25]: (k3_mcart_1(k4_tarski(A_3, B_4), C_5, C_25)=k4_mcart_1(A_3, B_4, C_5, C_25))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_41])).
% 2.00/1.23  tff(c_10, plain, (![A_13, B_14, C_15]: (k3_zfmisc_1(k1_tarski(A_13), k1_tarski(B_14), k1_tarski(C_15))=k1_tarski(k3_mcart_1(A_13, B_14, C_15)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.00/1.23  tff(c_6, plain, (![A_6, B_7, C_8]: (k2_zfmisc_1(k2_zfmisc_1(A_6, B_7), C_8)=k3_zfmisc_1(A_6, B_7, C_8))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.00/1.23  tff(c_47, plain, (![A_26, B_27]: (k2_zfmisc_1(k1_tarski(A_26), k1_tarski(B_27))=k1_tarski(k4_tarski(A_26, B_27)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.00/1.23  tff(c_136, plain, (![A_47, B_48, C_49]: (k3_zfmisc_1(k1_tarski(A_47), k1_tarski(B_48), C_49)=k2_zfmisc_1(k1_tarski(k4_tarski(A_47, B_48)), C_49))), inference(superposition, [status(thm), theory('equality')], [c_47, c_6])).
% 2.00/1.23  tff(c_12, plain, (![A_16, B_17, C_18, D_19]: (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_16, B_17), C_18), D_19)=k4_zfmisc_1(A_16, B_17, C_18, D_19))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.00/1.23  tff(c_15, plain, (![A_16, B_17, C_18, D_19]: (k2_zfmisc_1(k3_zfmisc_1(A_16, B_17, C_18), D_19)=k4_zfmisc_1(A_16, B_17, C_18, D_19))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_12])).
% 2.00/1.23  tff(c_146, plain, (![A_47, B_48, C_49, D_19]: (k2_zfmisc_1(k2_zfmisc_1(k1_tarski(k4_tarski(A_47, B_48)), C_49), D_19)=k4_zfmisc_1(k1_tarski(A_47), k1_tarski(B_48), C_49, D_19))), inference(superposition, [status(thm), theory('equality')], [c_136, c_15])).
% 2.00/1.23  tff(c_154, plain, (![A_47, B_48, C_49, D_19]: (k4_zfmisc_1(k1_tarski(A_47), k1_tarski(B_48), C_49, D_19)=k3_zfmisc_1(k1_tarski(k4_tarski(A_47, B_48)), C_49, D_19))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_146])).
% 2.00/1.23  tff(c_14, plain, (k4_zfmisc_1(k1_tarski('#skF_1'), k1_tarski('#skF_2'), k1_tarski('#skF_3'), k1_tarski('#skF_4'))!=k1_tarski(k4_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.00/1.23  tff(c_285, plain, (k3_zfmisc_1(k1_tarski(k4_tarski('#skF_1', '#skF_2')), k1_tarski('#skF_3'), k1_tarski('#skF_4'))!=k1_tarski(k4_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_14])).
% 2.00/1.23  tff(c_288, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_117, c_10, c_285])).
% 2.00/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.23  
% 2.00/1.23  Inference rules
% 2.00/1.23  ----------------------
% 2.00/1.23  #Ref     : 0
% 2.00/1.23  #Sup     : 68
% 2.00/1.23  #Fact    : 0
% 2.00/1.23  #Define  : 0
% 2.00/1.23  #Split   : 0
% 2.00/1.23  #Chain   : 0
% 2.00/1.23  #Close   : 0
% 2.00/1.23  
% 2.00/1.23  Ordering : KBO
% 2.00/1.23  
% 2.00/1.23  Simplification rules
% 2.00/1.23  ----------------------
% 2.00/1.23  #Subsume      : 0
% 2.00/1.23  #Demod        : 31
% 2.00/1.23  #Tautology    : 34
% 2.00/1.23  #SimpNegUnit  : 0
% 2.00/1.23  #BackRed      : 1
% 2.00/1.23  
% 2.00/1.23  #Partial instantiations: 0
% 2.00/1.23  #Strategies tried      : 1
% 2.00/1.23  
% 2.00/1.23  Timing (in seconds)
% 2.00/1.23  ----------------------
% 2.09/1.23  Preprocessing        : 0.27
% 2.09/1.23  Parsing              : 0.14
% 2.09/1.23  CNF conversion       : 0.02
% 2.09/1.23  Main loop            : 0.22
% 2.09/1.23  Inferencing          : 0.10
% 2.09/1.23  Reduction            : 0.07
% 2.09/1.23  Demodulation         : 0.05
% 2.09/1.23  BG Simplification    : 0.02
% 2.09/1.23  Subsumption          : 0.02
% 2.09/1.23  Abstraction          : 0.02
% 2.09/1.23  MUC search           : 0.00
% 2.09/1.23  Cooper               : 0.00
% 2.09/1.23  Total                : 0.51
% 2.09/1.23  Index Insertion      : 0.00
% 2.09/1.23  Index Deletion       : 0.00
% 2.09/1.23  Index Matching       : 0.00
% 2.09/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
