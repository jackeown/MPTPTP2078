%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:11 EST 2020

% Result     : Theorem 2.52s
% Output     : CNFRefutation 2.52s
% Verified   : 
% Statistics : Number of formulae       :   45 (  58 expanded)
%              Number of leaves         :   25 (  31 expanded)
%              Depth                    :    9
%              Number of atoms          :   28 (  41 expanded)
%              Number of equality atoms :   27 (  40 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

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

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_33,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_43,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_45,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_tarski(A,B),k1_enumset1(C,D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_tarski(A),k3_enumset1(B,C,D,E,F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_enumset1(A,B,C),k1_enumset1(D,E,F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l62_enumset1)).

tff(f_48,negated_conjecture,(
    ~ ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(c_8,plain,(
    ! [A_11,B_12,C_13] : k2_xboole_0(k1_tarski(A_11),k2_tarski(B_12,C_13)) = k1_enumset1(A_11,B_12,C_13) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_18,plain,(
    ! [A_36] : k2_tarski(A_36,A_36) = k1_tarski(A_36) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_20,plain,(
    ! [A_37,B_38] : k1_enumset1(A_37,A_37,B_38) = k2_tarski(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_237,plain,(
    ! [D_66,B_67,E_65,A_63,C_64] : k2_xboole_0(k2_tarski(A_63,B_67),k1_enumset1(C_64,D_66,E_65)) = k3_enumset1(A_63,B_67,C_64,D_66,E_65) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_693,plain,(
    ! [A_113,B_114,A_115,B_116] : k3_enumset1(A_113,B_114,A_115,A_115,B_116) = k2_xboole_0(k2_tarski(A_113,B_114),k2_tarski(A_115,B_116)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_237])).

tff(c_747,plain,(
    ! [A_36,A_115,B_116] : k3_enumset1(A_36,A_36,A_115,A_115,B_116) = k2_xboole_0(k1_tarski(A_36),k2_tarski(A_115,B_116)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_693])).

tff(c_765,plain,(
    ! [A_36,A_115,B_116] : k3_enumset1(A_36,A_36,A_115,A_115,B_116) = k1_enumset1(A_36,A_115,B_116) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_747])).

tff(c_10,plain,(
    ! [A_14,B_15,C_16,D_17] : k2_xboole_0(k1_tarski(A_14),k1_enumset1(B_15,C_16,D_17)) = k2_enumset1(A_14,B_15,C_16,D_17) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_767,plain,(
    ! [A_117,A_118,B_119] : k3_enumset1(A_117,A_117,A_118,A_118,B_119) = k1_enumset1(A_117,A_118,B_119) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_747])).

tff(c_14,plain,(
    ! [A_23,B_24,F_28,D_26,C_25,E_27] : k2_xboole_0(k1_tarski(A_23),k3_enumset1(B_24,C_25,D_26,E_27,F_28)) = k4_enumset1(A_23,B_24,C_25,D_26,E_27,F_28) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_784,plain,(
    ! [A_23,A_117,A_118,B_119] : k4_enumset1(A_23,A_117,A_117,A_118,A_118,B_119) = k2_xboole_0(k1_tarski(A_23),k1_enumset1(A_117,A_118,B_119)) ),
    inference(superposition,[status(thm),theory(equality)],[c_767,c_14])).

tff(c_825,plain,(
    ! [A_120,A_121,A_122,B_123] : k4_enumset1(A_120,A_121,A_121,A_122,A_122,B_123) = k2_enumset1(A_120,A_121,A_122,B_123) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_784])).

tff(c_12,plain,(
    ! [E_22,D_21,A_18,C_20,B_19] : k2_xboole_0(k2_tarski(A_18,B_19),k1_enumset1(C_20,D_21,E_22)) = k3_enumset1(A_18,B_19,C_20,D_21,E_22) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_458,plain,(
    ! [C_89,B_88,E_91,D_86,F_87,A_90] : k2_xboole_0(k1_enumset1(A_90,B_88,C_89),k1_enumset1(D_86,E_91,F_87)) = k4_enumset1(A_90,B_88,C_89,D_86,E_91,F_87) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_479,plain,(
    ! [B_38,E_91,A_37,D_86,F_87] : k4_enumset1(A_37,A_37,B_38,D_86,E_91,F_87) = k2_xboole_0(k2_tarski(A_37,B_38),k1_enumset1(D_86,E_91,F_87)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_458])).

tff(c_486,plain,(
    ! [B_38,E_91,A_37,D_86,F_87] : k4_enumset1(A_37,A_37,B_38,D_86,E_91,F_87) = k3_enumset1(A_37,B_38,D_86,E_91,F_87) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_479])).

tff(c_832,plain,(
    ! [A_121,A_122,B_123] : k3_enumset1(A_121,A_121,A_122,A_122,B_123) = k2_enumset1(A_121,A_121,A_122,B_123) ),
    inference(superposition,[status(thm),theory(equality)],[c_825,c_486])).

tff(c_873,plain,(
    ! [A_121,A_122,B_123] : k2_enumset1(A_121,A_121,A_122,B_123) = k1_enumset1(A_121,A_122,B_123) ),
    inference(demodulation,[status(thm),theory(equality)],[c_765,c_832])).

tff(c_22,plain,(
    k2_enumset1('#skF_1','#skF_1','#skF_2','#skF_3') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_884,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_873,c_22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:09:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.52/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.52/1.33  
% 2.52/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.52/1.33  %$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 2.52/1.33  
% 2.52/1.33  %Foreground sorts:
% 2.52/1.33  
% 2.52/1.33  
% 2.52/1.33  %Background operators:
% 2.52/1.33  
% 2.52/1.33  
% 2.52/1.33  %Foreground operators:
% 2.52/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.52/1.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.52/1.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.52/1.33  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.52/1.33  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.52/1.33  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.52/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.52/1.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.52/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.52/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.52/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.52/1.33  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.52/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.52/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.52/1.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.52/1.33  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.52/1.33  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.52/1.33  
% 2.52/1.34  tff(f_33, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_enumset1)).
% 2.52/1.34  tff(f_43, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.52/1.34  tff(f_45, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.52/1.34  tff(f_37, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_tarski(A, B), k1_enumset1(C, D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_enumset1)).
% 2.52/1.34  tff(f_35, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_enumset1)).
% 2.52/1.34  tff(f_39, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_tarski(A), k3_enumset1(B, C, D, E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_enumset1)).
% 2.52/1.34  tff(f_31, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_enumset1(A, B, C), k1_enumset1(D, E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l62_enumset1)).
% 2.52/1.34  tff(f_48, negated_conjecture, ~(![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.52/1.34  tff(c_8, plain, (![A_11, B_12, C_13]: (k2_xboole_0(k1_tarski(A_11), k2_tarski(B_12, C_13))=k1_enumset1(A_11, B_12, C_13))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.52/1.34  tff(c_18, plain, (![A_36]: (k2_tarski(A_36, A_36)=k1_tarski(A_36))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.52/1.34  tff(c_20, plain, (![A_37, B_38]: (k1_enumset1(A_37, A_37, B_38)=k2_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.52/1.34  tff(c_237, plain, (![D_66, B_67, E_65, A_63, C_64]: (k2_xboole_0(k2_tarski(A_63, B_67), k1_enumset1(C_64, D_66, E_65))=k3_enumset1(A_63, B_67, C_64, D_66, E_65))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.52/1.34  tff(c_693, plain, (![A_113, B_114, A_115, B_116]: (k3_enumset1(A_113, B_114, A_115, A_115, B_116)=k2_xboole_0(k2_tarski(A_113, B_114), k2_tarski(A_115, B_116)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_237])).
% 2.52/1.34  tff(c_747, plain, (![A_36, A_115, B_116]: (k3_enumset1(A_36, A_36, A_115, A_115, B_116)=k2_xboole_0(k1_tarski(A_36), k2_tarski(A_115, B_116)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_693])).
% 2.52/1.34  tff(c_765, plain, (![A_36, A_115, B_116]: (k3_enumset1(A_36, A_36, A_115, A_115, B_116)=k1_enumset1(A_36, A_115, B_116))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_747])).
% 2.52/1.34  tff(c_10, plain, (![A_14, B_15, C_16, D_17]: (k2_xboole_0(k1_tarski(A_14), k1_enumset1(B_15, C_16, D_17))=k2_enumset1(A_14, B_15, C_16, D_17))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.52/1.34  tff(c_767, plain, (![A_117, A_118, B_119]: (k3_enumset1(A_117, A_117, A_118, A_118, B_119)=k1_enumset1(A_117, A_118, B_119))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_747])).
% 2.52/1.34  tff(c_14, plain, (![A_23, B_24, F_28, D_26, C_25, E_27]: (k2_xboole_0(k1_tarski(A_23), k3_enumset1(B_24, C_25, D_26, E_27, F_28))=k4_enumset1(A_23, B_24, C_25, D_26, E_27, F_28))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.52/1.34  tff(c_784, plain, (![A_23, A_117, A_118, B_119]: (k4_enumset1(A_23, A_117, A_117, A_118, A_118, B_119)=k2_xboole_0(k1_tarski(A_23), k1_enumset1(A_117, A_118, B_119)))), inference(superposition, [status(thm), theory('equality')], [c_767, c_14])).
% 2.52/1.34  tff(c_825, plain, (![A_120, A_121, A_122, B_123]: (k4_enumset1(A_120, A_121, A_121, A_122, A_122, B_123)=k2_enumset1(A_120, A_121, A_122, B_123))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_784])).
% 2.52/1.34  tff(c_12, plain, (![E_22, D_21, A_18, C_20, B_19]: (k2_xboole_0(k2_tarski(A_18, B_19), k1_enumset1(C_20, D_21, E_22))=k3_enumset1(A_18, B_19, C_20, D_21, E_22))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.52/1.34  tff(c_458, plain, (![C_89, B_88, E_91, D_86, F_87, A_90]: (k2_xboole_0(k1_enumset1(A_90, B_88, C_89), k1_enumset1(D_86, E_91, F_87))=k4_enumset1(A_90, B_88, C_89, D_86, E_91, F_87))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.52/1.34  tff(c_479, plain, (![B_38, E_91, A_37, D_86, F_87]: (k4_enumset1(A_37, A_37, B_38, D_86, E_91, F_87)=k2_xboole_0(k2_tarski(A_37, B_38), k1_enumset1(D_86, E_91, F_87)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_458])).
% 2.52/1.34  tff(c_486, plain, (![B_38, E_91, A_37, D_86, F_87]: (k4_enumset1(A_37, A_37, B_38, D_86, E_91, F_87)=k3_enumset1(A_37, B_38, D_86, E_91, F_87))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_479])).
% 2.52/1.34  tff(c_832, plain, (![A_121, A_122, B_123]: (k3_enumset1(A_121, A_121, A_122, A_122, B_123)=k2_enumset1(A_121, A_121, A_122, B_123))), inference(superposition, [status(thm), theory('equality')], [c_825, c_486])).
% 2.52/1.34  tff(c_873, plain, (![A_121, A_122, B_123]: (k2_enumset1(A_121, A_121, A_122, B_123)=k1_enumset1(A_121, A_122, B_123))), inference(demodulation, [status(thm), theory('equality')], [c_765, c_832])).
% 2.52/1.34  tff(c_22, plain, (k2_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.52/1.34  tff(c_884, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_873, c_22])).
% 2.52/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.52/1.34  
% 2.52/1.34  Inference rules
% 2.52/1.34  ----------------------
% 2.52/1.34  #Ref     : 0
% 2.52/1.34  #Sup     : 202
% 2.52/1.34  #Fact    : 0
% 2.52/1.34  #Define  : 0
% 2.52/1.34  #Split   : 0
% 2.52/1.34  #Chain   : 0
% 2.52/1.34  #Close   : 0
% 2.52/1.34  
% 2.52/1.34  Ordering : KBO
% 2.52/1.34  
% 2.52/1.34  Simplification rules
% 2.52/1.34  ----------------------
% 2.52/1.34  #Subsume      : 21
% 2.52/1.34  #Demod        : 144
% 2.52/1.34  #Tautology    : 142
% 2.52/1.34  #SimpNegUnit  : 0
% 2.52/1.34  #BackRed      : 1
% 2.52/1.34  
% 2.52/1.34  #Partial instantiations: 0
% 2.52/1.34  #Strategies tried      : 1
% 2.52/1.34  
% 2.52/1.34  Timing (in seconds)
% 2.52/1.34  ----------------------
% 2.52/1.34  Preprocessing        : 0.29
% 2.52/1.34  Parsing              : 0.15
% 2.52/1.34  CNF conversion       : 0.02
% 2.52/1.34  Main loop            : 0.30
% 2.52/1.34  Inferencing          : 0.13
% 2.52/1.34  Reduction            : 0.11
% 2.52/1.34  Demodulation         : 0.09
% 2.52/1.34  BG Simplification    : 0.02
% 2.52/1.34  Subsumption          : 0.03
% 2.52/1.34  Abstraction          : 0.02
% 2.52/1.34  MUC search           : 0.00
% 2.52/1.34  Cooper               : 0.00
% 2.52/1.34  Total                : 0.61
% 2.52/1.34  Index Insertion      : 0.00
% 2.52/1.34  Index Deletion       : 0.00
% 2.52/1.34  Index Matching       : 0.00
% 2.52/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
