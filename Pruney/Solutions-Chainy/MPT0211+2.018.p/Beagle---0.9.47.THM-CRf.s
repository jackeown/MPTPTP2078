%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:17 EST 2020

% Result     : Theorem 6.15s
% Output     : CNFRefutation 6.15s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 208 expanded)
%              Number of leaves         :   27 (  84 expanded)
%              Depth                    :   11
%              Number of atoms          :   41 ( 191 expanded)
%              Number of equality atoms :   40 ( 190 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k7_enumset1 > k6_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

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

tff(k7_enumset1,type,(
    k7_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_53,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,C,D,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_enumset1)).

tff(f_55,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_51,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_enumset1(A,B,C),k2_tarski(D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l57_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(D,C,B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_49,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,D,C,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_enumset1)).

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(B,A),k2_tarski(C,A)) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_enumset1)).

tff(c_28,plain,(
    ! [A_52,B_53,C_54] : k2_enumset1(A_52,A_52,B_53,C_54) = k1_enumset1(A_52,B_53,C_54) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_12,plain,(
    ! [A_20,C_22,D_23,B_21] : k2_enumset1(A_20,C_22,D_23,B_21) = k2_enumset1(A_20,B_21,C_22,D_23) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_30,plain,(
    ! [A_55,B_56,C_57,D_58] : k3_enumset1(A_55,A_55,B_56,C_57,D_58) = k2_enumset1(A_55,B_56,C_57,D_58) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_26,plain,(
    ! [A_50,B_51] : k1_enumset1(A_50,A_50,B_51) = k2_tarski(A_50,B_51) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1853,plain,(
    ! [E_138,C_136,D_134,A_137,B_135] : k2_xboole_0(k1_enumset1(A_137,B_135,C_136),k2_tarski(D_134,E_138)) = k3_enumset1(A_137,B_135,C_136,D_134,E_138) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1877,plain,(
    ! [A_50,B_51,D_134,E_138] : k3_enumset1(A_50,A_50,B_51,D_134,E_138) = k2_xboole_0(k2_tarski(A_50,B_51),k2_tarski(D_134,E_138)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_1853])).

tff(c_1883,plain,(
    ! [A_50,B_51,D_134,E_138] : k2_xboole_0(k2_tarski(A_50,B_51),k2_tarski(D_134,E_138)) = k2_enumset1(A_50,B_51,D_134,E_138) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1877])).

tff(c_627,plain,(
    ! [D_100,C_101,B_102,A_103] : k2_enumset1(D_100,C_101,B_102,A_103) = k2_enumset1(A_103,B_102,C_101,D_100) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_699,plain,(
    ! [D_100,C_101,B_102] : k2_enumset1(D_100,C_101,B_102,B_102) = k1_enumset1(B_102,C_101,D_100) ),
    inference(superposition,[status(thm),theory(equality)],[c_627,c_28])).

tff(c_22,plain,(
    ! [A_45,B_46,C_47,D_48] : k2_xboole_0(k1_enumset1(A_45,B_46,C_47),k1_tarski(D_48)) = k2_enumset1(A_45,B_46,C_47,D_48) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_24,plain,(
    ! [A_49] : k2_tarski(A_49,A_49) = k1_tarski(A_49) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1880,plain,(
    ! [A_137,B_135,C_136,A_49] : k3_enumset1(A_137,B_135,C_136,A_49,A_49) = k2_xboole_0(k1_enumset1(A_137,B_135,C_136),k1_tarski(A_49)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1853])).

tff(c_5772,plain,(
    ! [A_196,B_197,C_198,A_199] : k3_enumset1(A_196,B_197,C_198,A_199,A_199) = k2_enumset1(A_196,B_197,C_198,A_199) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1880])).

tff(c_5782,plain,(
    ! [B_197,C_198,A_199] : k2_enumset1(B_197,C_198,A_199,A_199) = k2_enumset1(B_197,B_197,C_198,A_199) ),
    inference(superposition,[status(thm),theory(equality)],[c_5772,c_30])).

tff(c_5795,plain,(
    ! [B_200,C_201,A_202] : k1_enumset1(B_200,C_201,A_202) = k1_enumset1(A_202,C_201,B_200) ),
    inference(demodulation,[status(thm),theory(equality)],[c_699,c_28,c_5782])).

tff(c_291,plain,(
    ! [B_85,D_86,C_87,A_88] : k2_enumset1(B_85,D_86,C_87,A_88) = k2_enumset1(A_88,B_85,C_87,D_86) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_522,plain,(
    ! [A_95,D_96,C_97] : k2_enumset1(A_95,D_96,C_97,D_96) = k1_enumset1(D_96,C_97,A_95) ),
    inference(superposition,[status(thm),theory(equality)],[c_291,c_28])).

tff(c_145,plain,(
    ! [A_73,C_74,D_75,B_76] : k2_enumset1(A_73,C_74,D_75,B_76) = k2_enumset1(A_73,B_76,C_74,D_75) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_180,plain,(
    ! [A_52,C_54,B_53] : k2_enumset1(A_52,C_54,A_52,B_53) = k1_enumset1(A_52,B_53,C_54) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_145])).

tff(c_539,plain,(
    ! [D_96,C_97] : k1_enumset1(D_96,C_97,C_97) = k1_enumset1(C_97,D_96,D_96) ),
    inference(superposition,[status(thm),theory(equality)],[c_522,c_180])).

tff(c_5823,plain,(
    ! [B_200,A_202] : k1_enumset1(B_200,B_200,A_202) = k1_enumset1(B_200,A_202,A_202) ),
    inference(superposition,[status(thm),theory(equality)],[c_5795,c_539])).

tff(c_5902,plain,(
    ! [B_200,A_202] : k1_enumset1(B_200,A_202,A_202) = k2_tarski(B_200,A_202) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_5823])).

tff(c_5914,plain,(
    ! [D_96,C_97] : k2_tarski(D_96,C_97) = k2_tarski(C_97,D_96) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5902,c_5902,c_539])).

tff(c_387,plain,(
    ! [B_89,D_90,C_91] : k2_enumset1(B_89,D_90,C_91,B_89) = k1_enumset1(B_89,C_91,D_90) ),
    inference(superposition,[status(thm),theory(equality)],[c_291,c_28])).

tff(c_161,plain,(
    ! [B_76,C_74,D_75] : k2_enumset1(B_76,C_74,D_75,B_76) = k1_enumset1(B_76,C_74,D_75) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_28])).

tff(c_403,plain,(
    ! [B_89,D_90,C_91] : k1_enumset1(B_89,D_90,C_91) = k1_enumset1(B_89,C_91,D_90) ),
    inference(superposition,[status(thm),theory(equality)],[c_387,c_161])).

tff(c_32,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_452,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_403,c_32])).

tff(c_5965,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),k2_tarski('#skF_1','#skF_3')) != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5914,c_5914,c_452])).

tff(c_6075,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_1','#skF_3') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1883,c_5965])).

tff(c_6078,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_12,c_12,c_6075])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:29:09 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.15/2.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.15/2.21  
% 6.15/2.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.15/2.22  %$ k7_enumset1 > k6_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 6.15/2.22  
% 6.15/2.22  %Foreground sorts:
% 6.15/2.22  
% 6.15/2.22  
% 6.15/2.22  %Background operators:
% 6.15/2.22  
% 6.15/2.22  
% 6.15/2.22  %Foreground operators:
% 6.15/2.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.15/2.22  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.15/2.22  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.15/2.22  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.15/2.22  tff(k7_enumset1, type, k7_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.15/2.22  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.15/2.22  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.15/2.22  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.15/2.22  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.15/2.22  tff('#skF_2', type, '#skF_2': $i).
% 6.15/2.22  tff('#skF_3', type, '#skF_3': $i).
% 6.15/2.22  tff('#skF_1', type, '#skF_1': $i).
% 6.15/2.22  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.15/2.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.15/2.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.15/2.22  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.15/2.22  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.15/2.22  
% 6.15/2.23  tff(f_53, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 6.15/2.23  tff(f_37, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, C, D, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t105_enumset1)).
% 6.15/2.23  tff(f_55, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 6.15/2.23  tff(f_51, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 6.15/2.23  tff(f_33, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_enumset1(A, B, C), k2_tarski(D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l57_enumset1)).
% 6.15/2.23  tff(f_43, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(D, C, B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_enumset1)).
% 6.15/2.23  tff(f_47, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 6.15/2.23  tff(f_49, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 6.15/2.23  tff(f_41, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, D, C, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_enumset1)).
% 6.15/2.23  tff(f_58, negated_conjecture, ~(![A, B, C]: (k2_xboole_0(k2_tarski(B, A), k2_tarski(C, A)) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t137_enumset1)).
% 6.15/2.23  tff(c_28, plain, (![A_52, B_53, C_54]: (k2_enumset1(A_52, A_52, B_53, C_54)=k1_enumset1(A_52, B_53, C_54))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.15/2.23  tff(c_12, plain, (![A_20, C_22, D_23, B_21]: (k2_enumset1(A_20, C_22, D_23, B_21)=k2_enumset1(A_20, B_21, C_22, D_23))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.15/2.23  tff(c_30, plain, (![A_55, B_56, C_57, D_58]: (k3_enumset1(A_55, A_55, B_56, C_57, D_58)=k2_enumset1(A_55, B_56, C_57, D_58))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.15/2.23  tff(c_26, plain, (![A_50, B_51]: (k1_enumset1(A_50, A_50, B_51)=k2_tarski(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.15/2.23  tff(c_1853, plain, (![E_138, C_136, D_134, A_137, B_135]: (k2_xboole_0(k1_enumset1(A_137, B_135, C_136), k2_tarski(D_134, E_138))=k3_enumset1(A_137, B_135, C_136, D_134, E_138))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.15/2.23  tff(c_1877, plain, (![A_50, B_51, D_134, E_138]: (k3_enumset1(A_50, A_50, B_51, D_134, E_138)=k2_xboole_0(k2_tarski(A_50, B_51), k2_tarski(D_134, E_138)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_1853])).
% 6.15/2.23  tff(c_1883, plain, (![A_50, B_51, D_134, E_138]: (k2_xboole_0(k2_tarski(A_50, B_51), k2_tarski(D_134, E_138))=k2_enumset1(A_50, B_51, D_134, E_138))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1877])).
% 6.15/2.23  tff(c_627, plain, (![D_100, C_101, B_102, A_103]: (k2_enumset1(D_100, C_101, B_102, A_103)=k2_enumset1(A_103, B_102, C_101, D_100))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.15/2.23  tff(c_699, plain, (![D_100, C_101, B_102]: (k2_enumset1(D_100, C_101, B_102, B_102)=k1_enumset1(B_102, C_101, D_100))), inference(superposition, [status(thm), theory('equality')], [c_627, c_28])).
% 6.15/2.23  tff(c_22, plain, (![A_45, B_46, C_47, D_48]: (k2_xboole_0(k1_enumset1(A_45, B_46, C_47), k1_tarski(D_48))=k2_enumset1(A_45, B_46, C_47, D_48))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.15/2.23  tff(c_24, plain, (![A_49]: (k2_tarski(A_49, A_49)=k1_tarski(A_49))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.15/2.23  tff(c_1880, plain, (![A_137, B_135, C_136, A_49]: (k3_enumset1(A_137, B_135, C_136, A_49, A_49)=k2_xboole_0(k1_enumset1(A_137, B_135, C_136), k1_tarski(A_49)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_1853])).
% 6.15/2.23  tff(c_5772, plain, (![A_196, B_197, C_198, A_199]: (k3_enumset1(A_196, B_197, C_198, A_199, A_199)=k2_enumset1(A_196, B_197, C_198, A_199))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_1880])).
% 6.15/2.23  tff(c_5782, plain, (![B_197, C_198, A_199]: (k2_enumset1(B_197, C_198, A_199, A_199)=k2_enumset1(B_197, B_197, C_198, A_199))), inference(superposition, [status(thm), theory('equality')], [c_5772, c_30])).
% 6.15/2.23  tff(c_5795, plain, (![B_200, C_201, A_202]: (k1_enumset1(B_200, C_201, A_202)=k1_enumset1(A_202, C_201, B_200))), inference(demodulation, [status(thm), theory('equality')], [c_699, c_28, c_5782])).
% 6.15/2.23  tff(c_291, plain, (![B_85, D_86, C_87, A_88]: (k2_enumset1(B_85, D_86, C_87, A_88)=k2_enumset1(A_88, B_85, C_87, D_86))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.15/2.23  tff(c_522, plain, (![A_95, D_96, C_97]: (k2_enumset1(A_95, D_96, C_97, D_96)=k1_enumset1(D_96, C_97, A_95))), inference(superposition, [status(thm), theory('equality')], [c_291, c_28])).
% 6.15/2.23  tff(c_145, plain, (![A_73, C_74, D_75, B_76]: (k2_enumset1(A_73, C_74, D_75, B_76)=k2_enumset1(A_73, B_76, C_74, D_75))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.15/2.23  tff(c_180, plain, (![A_52, C_54, B_53]: (k2_enumset1(A_52, C_54, A_52, B_53)=k1_enumset1(A_52, B_53, C_54))), inference(superposition, [status(thm), theory('equality')], [c_28, c_145])).
% 6.15/2.23  tff(c_539, plain, (![D_96, C_97]: (k1_enumset1(D_96, C_97, C_97)=k1_enumset1(C_97, D_96, D_96))), inference(superposition, [status(thm), theory('equality')], [c_522, c_180])).
% 6.15/2.23  tff(c_5823, plain, (![B_200, A_202]: (k1_enumset1(B_200, B_200, A_202)=k1_enumset1(B_200, A_202, A_202))), inference(superposition, [status(thm), theory('equality')], [c_5795, c_539])).
% 6.15/2.23  tff(c_5902, plain, (![B_200, A_202]: (k1_enumset1(B_200, A_202, A_202)=k2_tarski(B_200, A_202))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_5823])).
% 6.15/2.23  tff(c_5914, plain, (![D_96, C_97]: (k2_tarski(D_96, C_97)=k2_tarski(C_97, D_96))), inference(demodulation, [status(thm), theory('equality')], [c_5902, c_5902, c_539])).
% 6.15/2.23  tff(c_387, plain, (![B_89, D_90, C_91]: (k2_enumset1(B_89, D_90, C_91, B_89)=k1_enumset1(B_89, C_91, D_90))), inference(superposition, [status(thm), theory('equality')], [c_291, c_28])).
% 6.15/2.23  tff(c_161, plain, (![B_76, C_74, D_75]: (k2_enumset1(B_76, C_74, D_75, B_76)=k1_enumset1(B_76, C_74, D_75))), inference(superposition, [status(thm), theory('equality')], [c_145, c_28])).
% 6.15/2.23  tff(c_403, plain, (![B_89, D_90, C_91]: (k1_enumset1(B_89, D_90, C_91)=k1_enumset1(B_89, C_91, D_90))), inference(superposition, [status(thm), theory('equality')], [c_387, c_161])).
% 6.15/2.23  tff(c_32, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.15/2.23  tff(c_452, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_403, c_32])).
% 6.15/2.23  tff(c_5965, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), k2_tarski('#skF_1', '#skF_3'))!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5914, c_5914, c_452])).
% 6.15/2.23  tff(c_6075, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_1', '#skF_3')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1883, c_5965])).
% 6.15/2.23  tff(c_6078, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_12, c_12, c_6075])).
% 6.15/2.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.15/2.23  
% 6.15/2.23  Inference rules
% 6.15/2.23  ----------------------
% 6.15/2.23  #Ref     : 0
% 6.15/2.23  #Sup     : 1580
% 6.15/2.23  #Fact    : 0
% 6.15/2.23  #Define  : 0
% 6.15/2.23  #Split   : 0
% 6.15/2.23  #Chain   : 0
% 6.15/2.23  #Close   : 0
% 6.15/2.23  
% 6.15/2.23  Ordering : KBO
% 6.15/2.23  
% 6.15/2.23  Simplification rules
% 6.15/2.23  ----------------------
% 6.15/2.23  #Subsume      : 375
% 6.15/2.23  #Demod        : 789
% 6.15/2.23  #Tautology    : 815
% 6.15/2.23  #SimpNegUnit  : 0
% 6.15/2.23  #BackRed      : 4
% 6.15/2.23  
% 6.15/2.23  #Partial instantiations: 0
% 6.15/2.23  #Strategies tried      : 1
% 6.15/2.23  
% 6.15/2.23  Timing (in seconds)
% 6.15/2.23  ----------------------
% 6.15/2.23  Preprocessing        : 0.31
% 6.15/2.23  Parsing              : 0.16
% 6.15/2.23  CNF conversion       : 0.02
% 6.15/2.23  Main loop            : 1.15
% 6.15/2.23  Inferencing          : 0.33
% 6.15/2.23  Reduction            : 0.61
% 6.15/2.23  Demodulation         : 0.55
% 6.15/2.23  BG Simplification    : 0.04
% 6.15/2.23  Subsumption          : 0.13
% 6.15/2.23  Abstraction          : 0.06
% 6.15/2.23  MUC search           : 0.00
% 6.15/2.23  Cooper               : 0.00
% 6.15/2.23  Total                : 1.49
% 6.15/2.23  Index Insertion      : 0.00
% 6.15/2.24  Index Deletion       : 0.00
% 6.15/2.24  Index Matching       : 0.00
% 6.15/2.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
