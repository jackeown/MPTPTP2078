%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:11 EST 2020

% Result     : Theorem 1.58s
% Output     : CNFRefutation 1.76s
% Verified   : 
% Statistics : Number of formulae       :   42 (  48 expanded)
%              Number of leaves         :   24 (  27 expanded)
%              Depth                    :   11
%              Number of atoms          :   26 (  32 expanded)
%              Number of equality atoms :   25 (  31 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_35,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_33,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k2_tarski(F,G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_enumset1)).

tff(f_46,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_zfmisc_1)).

tff(c_10,plain,(
    ! [A_13,B_14] : k1_enumset1(A_13,A_13,B_14) = k2_tarski(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_15,B_16,C_17] : k2_enumset1(A_15,A_15,B_16,C_17) = k1_enumset1(A_15,B_16,C_17) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_8,plain,(
    ! [A_12] : k2_tarski(A_12,A_12) = k1_tarski(A_12) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_14,plain,(
    ! [A_18,B_19,C_20,D_21] : k3_enumset1(A_18,A_18,B_19,C_20,D_21) = k2_enumset1(A_18,B_19,C_20,D_21) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ! [E_26,A_22,B_23,D_25,C_24] : k4_enumset1(A_22,A_22,B_23,C_24,D_25,E_26) = k3_enumset1(A_22,B_23,C_24,D_25,E_26) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_18,plain,(
    ! [C_29,D_30,B_28,F_32,A_27,E_31] : k5_enumset1(A_27,A_27,B_28,C_29,D_30,E_31,F_32) = k4_enumset1(A_27,B_28,C_29,D_30,E_31,F_32) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_93,plain,(
    ! [G_60,C_62,A_63,F_59,B_61,E_64,D_58] : k2_xboole_0(k3_enumset1(A_63,B_61,C_62,D_58,E_64),k2_tarski(F_59,G_60)) = k5_enumset1(A_63,B_61,C_62,D_58,E_64,F_59,G_60) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_102,plain,(
    ! [G_60,D_21,F_59,A_18,C_20,B_19] : k5_enumset1(A_18,A_18,B_19,C_20,D_21,F_59,G_60) = k2_xboole_0(k2_enumset1(A_18,B_19,C_20,D_21),k2_tarski(F_59,G_60)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_93])).

tff(c_109,plain,(
    ! [G_68,B_70,A_65,F_67,C_66,D_69] : k2_xboole_0(k2_enumset1(A_65,B_70,C_66,D_69),k2_tarski(F_67,G_68)) = k4_enumset1(A_65,B_70,C_66,D_69,F_67,G_68) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_102])).

tff(c_118,plain,(
    ! [B_16,G_68,A_15,F_67,C_17] : k4_enumset1(A_15,A_15,B_16,C_17,F_67,G_68) = k2_xboole_0(k1_enumset1(A_15,B_16,C_17),k2_tarski(F_67,G_68)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_109])).

tff(c_125,plain,(
    ! [F_74,G_73,B_72,C_71,A_75] : k2_xboole_0(k1_enumset1(A_75,B_72,C_71),k2_tarski(F_74,G_73)) = k3_enumset1(A_75,B_72,C_71,F_74,G_73) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_118])).

tff(c_134,plain,(
    ! [A_13,B_14,F_74,G_73] : k3_enumset1(A_13,A_13,B_14,F_74,G_73) = k2_xboole_0(k2_tarski(A_13,B_14),k2_tarski(F_74,G_73)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_125])).

tff(c_141,plain,(
    ! [A_76,B_77,F_78,G_79] : k2_xboole_0(k2_tarski(A_76,B_77),k2_tarski(F_78,G_79)) = k2_enumset1(A_76,B_77,F_78,G_79) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_134])).

tff(c_150,plain,(
    ! [A_12,F_78,G_79] : k2_xboole_0(k1_tarski(A_12),k2_tarski(F_78,G_79)) = k2_enumset1(A_12,A_12,F_78,G_79) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_141])).

tff(c_156,plain,(
    ! [A_12,F_78,G_79] : k2_xboole_0(k1_tarski(A_12),k2_tarski(F_78,G_79)) = k1_enumset1(A_12,F_78,G_79) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_150])).

tff(c_20,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k2_tarski('#skF_1','#skF_2')) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_157,plain,(
    k1_enumset1('#skF_1','#skF_1','#skF_2') != k2_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_20])).

tff(c_160,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_157])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:38:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.58/1.04  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.58/1.05  
% 1.58/1.05  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.58/1.05  %$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1
% 1.58/1.05  
% 1.58/1.05  %Foreground sorts:
% 1.58/1.05  
% 1.58/1.05  
% 1.58/1.05  %Background operators:
% 1.58/1.05  
% 1.58/1.05  
% 1.58/1.05  %Foreground operators:
% 1.58/1.05  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.58/1.05  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.58/1.05  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.58/1.05  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.58/1.05  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.58/1.05  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.58/1.05  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.58/1.05  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.58/1.05  tff('#skF_2', type, '#skF_2': $i).
% 1.58/1.05  tff('#skF_1', type, '#skF_1': $i).
% 1.58/1.05  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.58/1.05  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.58/1.05  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.58/1.05  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.58/1.05  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.58/1.05  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.58/1.05  
% 1.76/1.06  tff(f_35, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 1.76/1.06  tff(f_37, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 1.76/1.06  tff(f_33, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.76/1.06  tff(f_39, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 1.76/1.06  tff(f_41, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 1.76/1.06  tff(f_43, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 1.76/1.06  tff(f_31, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k2_tarski(F, G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_enumset1)).
% 1.76/1.06  tff(f_46, negated_conjecture, ~(![A, B]: (k2_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_zfmisc_1)).
% 1.76/1.06  tff(c_10, plain, (![A_13, B_14]: (k1_enumset1(A_13, A_13, B_14)=k2_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.76/1.06  tff(c_12, plain, (![A_15, B_16, C_17]: (k2_enumset1(A_15, A_15, B_16, C_17)=k1_enumset1(A_15, B_16, C_17))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.76/1.06  tff(c_8, plain, (![A_12]: (k2_tarski(A_12, A_12)=k1_tarski(A_12))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.76/1.06  tff(c_14, plain, (![A_18, B_19, C_20, D_21]: (k3_enumset1(A_18, A_18, B_19, C_20, D_21)=k2_enumset1(A_18, B_19, C_20, D_21))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.76/1.06  tff(c_16, plain, (![E_26, A_22, B_23, D_25, C_24]: (k4_enumset1(A_22, A_22, B_23, C_24, D_25, E_26)=k3_enumset1(A_22, B_23, C_24, D_25, E_26))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.76/1.06  tff(c_18, plain, (![C_29, D_30, B_28, F_32, A_27, E_31]: (k5_enumset1(A_27, A_27, B_28, C_29, D_30, E_31, F_32)=k4_enumset1(A_27, B_28, C_29, D_30, E_31, F_32))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.76/1.06  tff(c_93, plain, (![G_60, C_62, A_63, F_59, B_61, E_64, D_58]: (k2_xboole_0(k3_enumset1(A_63, B_61, C_62, D_58, E_64), k2_tarski(F_59, G_60))=k5_enumset1(A_63, B_61, C_62, D_58, E_64, F_59, G_60))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.76/1.06  tff(c_102, plain, (![G_60, D_21, F_59, A_18, C_20, B_19]: (k5_enumset1(A_18, A_18, B_19, C_20, D_21, F_59, G_60)=k2_xboole_0(k2_enumset1(A_18, B_19, C_20, D_21), k2_tarski(F_59, G_60)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_93])).
% 1.76/1.06  tff(c_109, plain, (![G_68, B_70, A_65, F_67, C_66, D_69]: (k2_xboole_0(k2_enumset1(A_65, B_70, C_66, D_69), k2_tarski(F_67, G_68))=k4_enumset1(A_65, B_70, C_66, D_69, F_67, G_68))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_102])).
% 1.76/1.06  tff(c_118, plain, (![B_16, G_68, A_15, F_67, C_17]: (k4_enumset1(A_15, A_15, B_16, C_17, F_67, G_68)=k2_xboole_0(k1_enumset1(A_15, B_16, C_17), k2_tarski(F_67, G_68)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_109])).
% 1.76/1.06  tff(c_125, plain, (![F_74, G_73, B_72, C_71, A_75]: (k2_xboole_0(k1_enumset1(A_75, B_72, C_71), k2_tarski(F_74, G_73))=k3_enumset1(A_75, B_72, C_71, F_74, G_73))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_118])).
% 1.76/1.06  tff(c_134, plain, (![A_13, B_14, F_74, G_73]: (k3_enumset1(A_13, A_13, B_14, F_74, G_73)=k2_xboole_0(k2_tarski(A_13, B_14), k2_tarski(F_74, G_73)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_125])).
% 1.76/1.06  tff(c_141, plain, (![A_76, B_77, F_78, G_79]: (k2_xboole_0(k2_tarski(A_76, B_77), k2_tarski(F_78, G_79))=k2_enumset1(A_76, B_77, F_78, G_79))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_134])).
% 1.76/1.06  tff(c_150, plain, (![A_12, F_78, G_79]: (k2_xboole_0(k1_tarski(A_12), k2_tarski(F_78, G_79))=k2_enumset1(A_12, A_12, F_78, G_79))), inference(superposition, [status(thm), theory('equality')], [c_8, c_141])).
% 1.76/1.06  tff(c_156, plain, (![A_12, F_78, G_79]: (k2_xboole_0(k1_tarski(A_12), k2_tarski(F_78, G_79))=k1_enumset1(A_12, F_78, G_79))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_150])).
% 1.76/1.06  tff(c_20, plain, (k2_xboole_0(k1_tarski('#skF_1'), k2_tarski('#skF_1', '#skF_2'))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.76/1.06  tff(c_157, plain, (k1_enumset1('#skF_1', '#skF_1', '#skF_2')!=k2_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_156, c_20])).
% 1.76/1.06  tff(c_160, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_157])).
% 1.76/1.06  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.76/1.06  
% 1.76/1.06  Inference rules
% 1.76/1.06  ----------------------
% 1.76/1.06  #Ref     : 0
% 1.76/1.06  #Sup     : 32
% 1.76/1.06  #Fact    : 0
% 1.76/1.06  #Define  : 0
% 1.76/1.06  #Split   : 0
% 1.76/1.06  #Chain   : 0
% 1.76/1.06  #Close   : 0
% 1.76/1.06  
% 1.76/1.06  Ordering : KBO
% 1.76/1.06  
% 1.76/1.06  Simplification rules
% 1.76/1.06  ----------------------
% 1.76/1.06  #Subsume      : 0
% 1.76/1.06  #Demod        : 6
% 1.76/1.06  #Tautology    : 24
% 1.76/1.06  #SimpNegUnit  : 0
% 1.76/1.06  #BackRed      : 1
% 1.76/1.06  
% 1.76/1.06  #Partial instantiations: 0
% 1.76/1.06  #Strategies tried      : 1
% 1.76/1.06  
% 1.76/1.06  Timing (in seconds)
% 1.76/1.06  ----------------------
% 1.76/1.06  Preprocessing        : 0.25
% 1.76/1.06  Parsing              : 0.13
% 1.76/1.06  CNF conversion       : 0.02
% 1.76/1.06  Main loop            : 0.12
% 1.76/1.06  Inferencing          : 0.06
% 1.76/1.06  Reduction            : 0.04
% 1.76/1.06  Demodulation         : 0.03
% 1.76/1.06  BG Simplification    : 0.01
% 1.76/1.06  Subsumption          : 0.01
% 1.76/1.06  Abstraction          : 0.01
% 1.76/1.06  MUC search           : 0.00
% 1.76/1.06  Cooper               : 0.00
% 1.76/1.06  Total                : 0.40
% 1.76/1.06  Index Insertion      : 0.00
% 1.76/1.06  Index Deletion       : 0.00
% 1.76/1.06  Index Matching       : 0.00
% 1.76/1.06  BG Taut test         : 0.00
%------------------------------------------------------------------------------
