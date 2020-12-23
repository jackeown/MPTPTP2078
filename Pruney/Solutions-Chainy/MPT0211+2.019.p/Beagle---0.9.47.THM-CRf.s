%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:17 EST 2020

% Result     : Theorem 5.46s
% Output     : CNFRefutation 5.84s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 206 expanded)
%              Number of leaves         :   28 (  84 expanded)
%              Depth                    :   11
%              Number of atoms          :   40 ( 188 expanded)
%              Number of equality atoms :   39 ( 187 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_35,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,C,B,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,D,C,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_enumset1)).

tff(f_51,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_53,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_49,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_enumset1(A,B,C),k2_tarski(D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l57_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(D,C,B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_47,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(B,A),k2_tarski(C,A)) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_enumset1)).

tff(c_10,plain,(
    ! [A_12,C_14,B_13,D_15] : k2_enumset1(A_12,C_14,B_13,D_15) = k2_enumset1(A_12,B_13,C_14,D_15) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_530,plain,(
    ! [A_95,D_96,C_97,B_98] : k2_enumset1(A_95,D_96,C_97,B_98) = k2_enumset1(A_95,B_98,C_97,D_96) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_26,plain,(
    ! [A_43,B_44,C_45] : k2_enumset1(A_43,A_43,B_44,C_45) = k1_enumset1(A_43,B_44,C_45) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_678,plain,(
    ! [B_99,D_100,C_101] : k2_enumset1(B_99,D_100,C_101,B_99) = k1_enumset1(B_99,C_101,D_100) ),
    inference(superposition,[status(thm),theory(equality)],[c_530,c_26])).

tff(c_951,plain,(
    ! [D_120,B_121,C_122] : k2_enumset1(D_120,B_121,C_122,D_120) = k1_enumset1(D_120,B_121,C_122) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_678])).

tff(c_598,plain,(
    ! [B_98,D_96,C_97] : k2_enumset1(B_98,D_96,C_97,B_98) = k1_enumset1(B_98,C_97,D_96) ),
    inference(superposition,[status(thm),theory(equality)],[c_530,c_26])).

tff(c_961,plain,(
    ! [D_120,C_122,B_121] : k1_enumset1(D_120,C_122,B_121) = k1_enumset1(D_120,B_121,C_122) ),
    inference(superposition,[status(thm),theory(equality)],[c_951,c_598])).

tff(c_28,plain,(
    ! [A_46,B_47,C_48,D_49] : k3_enumset1(A_46,A_46,B_47,C_48,D_49) = k2_enumset1(A_46,B_47,C_48,D_49) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_24,plain,(
    ! [A_41,B_42] : k1_enumset1(A_41,A_41,B_42) = k2_tarski(A_41,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1070,plain,(
    ! [E_127,C_125,D_123,A_126,B_124] : k2_xboole_0(k1_enumset1(A_126,B_124,C_125),k2_tarski(D_123,E_127)) = k3_enumset1(A_126,B_124,C_125,D_123,E_127) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1088,plain,(
    ! [A_41,B_42,D_123,E_127] : k3_enumset1(A_41,A_41,B_42,D_123,E_127) = k2_xboole_0(k2_tarski(A_41,B_42),k2_tarski(D_123,E_127)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1070])).

tff(c_1094,plain,(
    ! [A_41,B_42,D_123,E_127] : k2_xboole_0(k2_tarski(A_41,B_42),k2_tarski(D_123,E_127)) = k2_enumset1(A_41,B_42,D_123,E_127) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1088])).

tff(c_234,plain,(
    ! [D_82,C_83,B_84,A_85] : k2_enumset1(D_82,C_83,B_84,A_85) = k2_enumset1(A_85,B_84,C_83,D_82) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_270,plain,(
    ! [D_82,C_83,B_84] : k2_enumset1(D_82,C_83,B_84,B_84) = k1_enumset1(B_84,C_83,D_82) ),
    inference(superposition,[status(thm),theory(equality)],[c_234,c_26])).

tff(c_18,plain,(
    ! [A_28,B_29,C_30,D_31] : k2_xboole_0(k1_enumset1(A_28,B_29,C_30),k1_tarski(D_31)) = k2_enumset1(A_28,B_29,C_30,D_31) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_22,plain,(
    ! [A_40] : k2_tarski(A_40,A_40) = k1_tarski(A_40) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1091,plain,(
    ! [A_126,B_124,C_125,A_40] : k3_enumset1(A_126,B_124,C_125,A_40,A_40) = k2_xboole_0(k1_enumset1(A_126,B_124,C_125),k1_tarski(A_40)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_1070])).

tff(c_4988,plain,(
    ! [A_196,B_197,C_198,A_199] : k3_enumset1(A_196,B_197,C_198,A_199,A_199) = k2_enumset1(A_196,B_197,C_198,A_199) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1091])).

tff(c_4995,plain,(
    ! [B_197,C_198,A_199] : k2_enumset1(B_197,C_198,A_199,A_199) = k2_enumset1(B_197,B_197,C_198,A_199) ),
    inference(superposition,[status(thm),theory(equality)],[c_4988,c_28])).

tff(c_5007,plain,(
    ! [B_200,C_201,A_202] : k1_enumset1(B_200,C_201,A_202) = k1_enumset1(A_202,C_201,B_200) ),
    inference(demodulation,[status(thm),theory(equality)],[c_270,c_26,c_4995])).

tff(c_424,plain,(
    ! [D_90,C_91,B_92] : k2_enumset1(D_90,C_91,B_92,B_92) = k1_enumset1(B_92,C_91,D_90) ),
    inference(superposition,[status(thm),theory(equality)],[c_234,c_26])).

tff(c_453,plain,(
    ! [C_91,B_92] : k1_enumset1(C_91,B_92,B_92) = k1_enumset1(B_92,C_91,C_91) ),
    inference(superposition,[status(thm),theory(equality)],[c_424,c_26])).

tff(c_5047,plain,(
    ! [B_200,A_202] : k1_enumset1(B_200,B_200,A_202) = k1_enumset1(B_200,A_202,A_202) ),
    inference(superposition,[status(thm),theory(equality)],[c_5007,c_453])).

tff(c_5114,plain,(
    ! [B_200,A_202] : k1_enumset1(B_200,A_202,A_202) = k2_tarski(B_200,A_202) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_5047])).

tff(c_5126,plain,(
    ! [C_91,B_92] : k2_tarski(C_91,B_92) = k2_tarski(B_92,C_91) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5114,c_5114,c_453])).

tff(c_34,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1096,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_961,c_34])).

tff(c_5177,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),k2_tarski('#skF_1','#skF_3')) != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5126,c_5126,c_1096])).

tff(c_5293,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_1','#skF_3') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1094,c_5177])).

tff(c_5296,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_961,c_26,c_10,c_5293])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:33:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.46/2.06  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.46/2.07  
% 5.46/2.07  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.46/2.07  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 5.46/2.07  
% 5.46/2.07  %Foreground sorts:
% 5.46/2.07  
% 5.46/2.07  
% 5.46/2.07  %Background operators:
% 5.46/2.07  
% 5.46/2.07  
% 5.46/2.07  %Foreground operators:
% 5.46/2.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.46/2.07  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.46/2.07  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.46/2.07  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.46/2.07  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.46/2.07  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.46/2.07  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.46/2.07  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.46/2.07  tff('#skF_2', type, '#skF_2': $i).
% 5.46/2.07  tff('#skF_3', type, '#skF_3': $i).
% 5.46/2.07  tff('#skF_1', type, '#skF_1': $i).
% 5.46/2.07  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.46/2.07  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.46/2.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.46/2.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.46/2.07  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.46/2.07  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.46/2.07  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.46/2.07  
% 5.84/2.08  tff(f_35, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, C, B, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t104_enumset1)).
% 5.84/2.08  tff(f_37, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, D, C, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t107_enumset1)).
% 5.84/2.08  tff(f_51, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 5.84/2.08  tff(f_53, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 5.84/2.08  tff(f_49, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 5.84/2.08  tff(f_33, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_enumset1(A, B, C), k2_tarski(D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l57_enumset1)).
% 5.84/2.08  tff(f_41, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(D, C, B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_enumset1)).
% 5.84/2.08  tff(f_43, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_enumset1)).
% 5.84/2.08  tff(f_47, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 5.84/2.08  tff(f_60, negated_conjecture, ~(![A, B, C]: (k2_xboole_0(k2_tarski(B, A), k2_tarski(C, A)) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t137_enumset1)).
% 5.84/2.08  tff(c_10, plain, (![A_12, C_14, B_13, D_15]: (k2_enumset1(A_12, C_14, B_13, D_15)=k2_enumset1(A_12, B_13, C_14, D_15))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.84/2.08  tff(c_530, plain, (![A_95, D_96, C_97, B_98]: (k2_enumset1(A_95, D_96, C_97, B_98)=k2_enumset1(A_95, B_98, C_97, D_96))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.84/2.08  tff(c_26, plain, (![A_43, B_44, C_45]: (k2_enumset1(A_43, A_43, B_44, C_45)=k1_enumset1(A_43, B_44, C_45))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.84/2.08  tff(c_678, plain, (![B_99, D_100, C_101]: (k2_enumset1(B_99, D_100, C_101, B_99)=k1_enumset1(B_99, C_101, D_100))), inference(superposition, [status(thm), theory('equality')], [c_530, c_26])).
% 5.84/2.08  tff(c_951, plain, (![D_120, B_121, C_122]: (k2_enumset1(D_120, B_121, C_122, D_120)=k1_enumset1(D_120, B_121, C_122))), inference(superposition, [status(thm), theory('equality')], [c_10, c_678])).
% 5.84/2.08  tff(c_598, plain, (![B_98, D_96, C_97]: (k2_enumset1(B_98, D_96, C_97, B_98)=k1_enumset1(B_98, C_97, D_96))), inference(superposition, [status(thm), theory('equality')], [c_530, c_26])).
% 5.84/2.08  tff(c_961, plain, (![D_120, C_122, B_121]: (k1_enumset1(D_120, C_122, B_121)=k1_enumset1(D_120, B_121, C_122))), inference(superposition, [status(thm), theory('equality')], [c_951, c_598])).
% 5.84/2.08  tff(c_28, plain, (![A_46, B_47, C_48, D_49]: (k3_enumset1(A_46, A_46, B_47, C_48, D_49)=k2_enumset1(A_46, B_47, C_48, D_49))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.84/2.08  tff(c_24, plain, (![A_41, B_42]: (k1_enumset1(A_41, A_41, B_42)=k2_tarski(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.84/2.08  tff(c_1070, plain, (![E_127, C_125, D_123, A_126, B_124]: (k2_xboole_0(k1_enumset1(A_126, B_124, C_125), k2_tarski(D_123, E_127))=k3_enumset1(A_126, B_124, C_125, D_123, E_127))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.84/2.08  tff(c_1088, plain, (![A_41, B_42, D_123, E_127]: (k3_enumset1(A_41, A_41, B_42, D_123, E_127)=k2_xboole_0(k2_tarski(A_41, B_42), k2_tarski(D_123, E_127)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_1070])).
% 5.84/2.08  tff(c_1094, plain, (![A_41, B_42, D_123, E_127]: (k2_xboole_0(k2_tarski(A_41, B_42), k2_tarski(D_123, E_127))=k2_enumset1(A_41, B_42, D_123, E_127))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1088])).
% 5.84/2.08  tff(c_234, plain, (![D_82, C_83, B_84, A_85]: (k2_enumset1(D_82, C_83, B_84, A_85)=k2_enumset1(A_85, B_84, C_83, D_82))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.84/2.08  tff(c_270, plain, (![D_82, C_83, B_84]: (k2_enumset1(D_82, C_83, B_84, B_84)=k1_enumset1(B_84, C_83, D_82))), inference(superposition, [status(thm), theory('equality')], [c_234, c_26])).
% 5.84/2.08  tff(c_18, plain, (![A_28, B_29, C_30, D_31]: (k2_xboole_0(k1_enumset1(A_28, B_29, C_30), k1_tarski(D_31))=k2_enumset1(A_28, B_29, C_30, D_31))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.84/2.08  tff(c_22, plain, (![A_40]: (k2_tarski(A_40, A_40)=k1_tarski(A_40))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.84/2.08  tff(c_1091, plain, (![A_126, B_124, C_125, A_40]: (k3_enumset1(A_126, B_124, C_125, A_40, A_40)=k2_xboole_0(k1_enumset1(A_126, B_124, C_125), k1_tarski(A_40)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_1070])).
% 5.84/2.08  tff(c_4988, plain, (![A_196, B_197, C_198, A_199]: (k3_enumset1(A_196, B_197, C_198, A_199, A_199)=k2_enumset1(A_196, B_197, C_198, A_199))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1091])).
% 5.84/2.08  tff(c_4995, plain, (![B_197, C_198, A_199]: (k2_enumset1(B_197, C_198, A_199, A_199)=k2_enumset1(B_197, B_197, C_198, A_199))), inference(superposition, [status(thm), theory('equality')], [c_4988, c_28])).
% 5.84/2.08  tff(c_5007, plain, (![B_200, C_201, A_202]: (k1_enumset1(B_200, C_201, A_202)=k1_enumset1(A_202, C_201, B_200))), inference(demodulation, [status(thm), theory('equality')], [c_270, c_26, c_4995])).
% 5.84/2.08  tff(c_424, plain, (![D_90, C_91, B_92]: (k2_enumset1(D_90, C_91, B_92, B_92)=k1_enumset1(B_92, C_91, D_90))), inference(superposition, [status(thm), theory('equality')], [c_234, c_26])).
% 5.84/2.08  tff(c_453, plain, (![C_91, B_92]: (k1_enumset1(C_91, B_92, B_92)=k1_enumset1(B_92, C_91, C_91))), inference(superposition, [status(thm), theory('equality')], [c_424, c_26])).
% 5.84/2.08  tff(c_5047, plain, (![B_200, A_202]: (k1_enumset1(B_200, B_200, A_202)=k1_enumset1(B_200, A_202, A_202))), inference(superposition, [status(thm), theory('equality')], [c_5007, c_453])).
% 5.84/2.08  tff(c_5114, plain, (![B_200, A_202]: (k1_enumset1(B_200, A_202, A_202)=k2_tarski(B_200, A_202))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_5047])).
% 5.84/2.08  tff(c_5126, plain, (![C_91, B_92]: (k2_tarski(C_91, B_92)=k2_tarski(B_92, C_91))), inference(demodulation, [status(thm), theory('equality')], [c_5114, c_5114, c_453])).
% 5.84/2.08  tff(c_34, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.84/2.08  tff(c_1096, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_961, c_34])).
% 5.84/2.08  tff(c_5177, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), k2_tarski('#skF_1', '#skF_3'))!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5126, c_5126, c_1096])).
% 5.84/2.08  tff(c_5293, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_1', '#skF_3')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1094, c_5177])).
% 5.84/2.08  tff(c_5296, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_961, c_26, c_10, c_5293])).
% 5.84/2.08  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.84/2.08  
% 5.84/2.08  Inference rules
% 5.84/2.08  ----------------------
% 5.84/2.08  #Ref     : 0
% 5.84/2.08  #Sup     : 1340
% 5.84/2.08  #Fact    : 0
% 5.84/2.08  #Define  : 0
% 5.84/2.08  #Split   : 0
% 5.84/2.08  #Chain   : 0
% 5.84/2.08  #Close   : 0
% 5.84/2.08  
% 5.84/2.08  Ordering : KBO
% 5.84/2.08  
% 5.84/2.08  Simplification rules
% 5.84/2.08  ----------------------
% 5.84/2.08  #Subsume      : 303
% 5.84/2.08  #Demod        : 737
% 5.84/2.08  #Tautology    : 773
% 5.84/2.08  #SimpNegUnit  : 0
% 5.84/2.08  #BackRed      : 4
% 5.84/2.08  
% 5.84/2.08  #Partial instantiations: 0
% 5.84/2.08  #Strategies tried      : 1
% 5.84/2.08  
% 5.84/2.08  Timing (in seconds)
% 5.84/2.08  ----------------------
% 5.84/2.09  Preprocessing        : 0.33
% 5.84/2.09  Parsing              : 0.17
% 5.84/2.09  CNF conversion       : 0.02
% 5.84/2.09  Main loop            : 1.01
% 5.84/2.09  Inferencing          : 0.29
% 5.84/2.09  Reduction            : 0.52
% 5.84/2.09  Demodulation         : 0.47
% 5.84/2.09  BG Simplification    : 0.04
% 5.84/2.09  Subsumption          : 0.12
% 5.84/2.09  Abstraction          : 0.05
% 5.84/2.09  MUC search           : 0.00
% 5.84/2.09  Cooper               : 0.00
% 5.84/2.09  Total                : 1.36
% 5.84/2.09  Index Insertion      : 0.00
% 5.84/2.09  Index Deletion       : 0.00
% 5.84/2.09  Index Matching       : 0.00
% 5.84/2.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
