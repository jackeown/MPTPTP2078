%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:21 EST 2020

% Result     : Theorem 7.90s
% Output     : CNFRefutation 7.90s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 157 expanded)
%              Number of leaves         :   31 (  66 expanded)
%              Depth                    :   10
%              Number of atoms          :   49 ( 140 expanded)
%              Number of equality atoms :   48 ( 139 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k7_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

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

tff(f_43,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,D,C,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_enumset1)).

tff(f_55,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,C,D,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_enumset1)).

tff(f_57,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_53,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_enumset1(A,B,C),k2_tarski(D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l57_enumset1)).

tff(f_51,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(B,A),k2_tarski(C,A)) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_enumset1)).

tff(c_375,plain,(
    ! [B_90,D_91,C_92,A_93] : k2_enumset1(B_90,D_91,C_92,A_93) = k2_enumset1(A_93,B_90,C_92,D_91) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_30,plain,(
    ! [A_49,B_50,C_51] : k2_enumset1(A_49,A_49,B_50,C_51) = k1_enumset1(A_49,B_50,C_51) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_593,plain,(
    ! [B_98,D_99,C_100] : k2_enumset1(B_98,D_99,C_100,B_98) = k1_enumset1(B_98,C_100,D_99) ),
    inference(superposition,[status(thm),theory(equality)],[c_375,c_30])).

tff(c_174,plain,(
    ! [A_76,C_77,D_78,B_79] : k2_enumset1(A_76,C_77,D_78,B_79) = k2_enumset1(A_76,B_79,C_77,D_78) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_190,plain,(
    ! [B_79,C_77,D_78] : k2_enumset1(B_79,C_77,D_78,B_79) = k1_enumset1(B_79,C_77,D_78) ),
    inference(superposition,[status(thm),theory(equality)],[c_174,c_30])).

tff(c_615,plain,(
    ! [B_98,D_99,C_100] : k1_enumset1(B_98,D_99,C_100) = k1_enumset1(B_98,C_100,D_99) ),
    inference(superposition,[status(thm),theory(equality)],[c_593,c_190])).

tff(c_14,plain,(
    ! [A_17,C_19,D_20,B_18] : k2_enumset1(A_17,C_19,D_20,B_18) = k2_enumset1(A_17,B_18,C_19,D_20) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_32,plain,(
    ! [A_52,B_53,C_54,D_55] : k3_enumset1(A_52,A_52,B_53,C_54,D_55) = k2_enumset1(A_52,B_53,C_54,D_55) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_28,plain,(
    ! [A_47,B_48] : k1_enumset1(A_47,A_47,B_48) = k2_tarski(A_47,B_48) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1772,plain,(
    ! [E_143,D_144,A_142,C_145,B_141] : k2_xboole_0(k1_enumset1(A_142,B_141,C_145),k2_tarski(D_144,E_143)) = k3_enumset1(A_142,B_141,C_145,D_144,E_143) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1796,plain,(
    ! [A_47,B_48,D_144,E_143] : k3_enumset1(A_47,A_47,B_48,D_144,E_143) = k2_xboole_0(k2_tarski(A_47,B_48),k2_tarski(D_144,E_143)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1772])).

tff(c_1802,plain,(
    ! [A_47,B_48,D_144,E_143] : k2_xboole_0(k2_tarski(A_47,B_48),k2_tarski(D_144,E_143)) = k2_enumset1(A_47,B_48,D_144,E_143) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1796])).

tff(c_26,plain,(
    ! [A_46] : k2_tarski(A_46,A_46) = k1_tarski(A_46) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1300,plain,(
    ! [A_123,B_124,C_125,D_126] : k2_xboole_0(k1_enumset1(A_123,B_124,C_125),k1_tarski(D_126)) = k2_enumset1(A_123,B_124,C_125,D_126) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1324,plain,(
    ! [A_47,B_48,D_126] : k2_xboole_0(k2_tarski(A_47,B_48),k1_tarski(D_126)) = k2_enumset1(A_47,A_47,B_48,D_126) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1300])).

tff(c_5972,plain,(
    ! [A_204,B_205,D_206] : k2_xboole_0(k2_tarski(A_204,B_205),k1_tarski(D_206)) = k1_enumset1(A_204,B_205,D_206) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1324])).

tff(c_5993,plain,(
    ! [A_46,D_206] : k2_xboole_0(k1_tarski(A_46),k1_tarski(D_206)) = k1_enumset1(A_46,A_46,D_206) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_5972])).

tff(c_5997,plain,(
    ! [A_207,D_208] : k2_xboole_0(k1_tarski(A_207),k1_tarski(D_208)) = k2_tarski(A_207,D_208) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_5993])).

tff(c_10,plain,(
    ! [A_10,B_11] : k5_xboole_0(A_10,k4_xboole_0(B_11,A_10)) = k2_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_321,plain,(
    ! [A_88,B_89] : k5_xboole_0(k5_xboole_0(A_88,B_89),k3_xboole_0(A_88,B_89)) = k2_xboole_0(A_88,B_89) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_3263,plain,(
    ! [B_173,A_174] : k5_xboole_0(k5_xboole_0(B_173,A_174),k3_xboole_0(A_174,B_173)) = k2_xboole_0(A_174,B_173) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_321])).

tff(c_6,plain,(
    ! [A_5,B_6,C_7] : k5_xboole_0(k5_xboole_0(A_5,B_6),C_7) = k5_xboole_0(A_5,k5_xboole_0(B_6,C_7)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3282,plain,(
    ! [B_173,A_174] : k5_xboole_0(B_173,k5_xboole_0(A_174,k3_xboole_0(A_174,B_173))) = k2_xboole_0(A_174,B_173) ),
    inference(superposition,[status(thm),theory(equality)],[c_3263,c_6])).

tff(c_3329,plain,(
    ! [B_173,A_174] : k2_xboole_0(B_173,A_174) = k2_xboole_0(A_174,B_173) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_4,c_3282])).

tff(c_6018,plain,(
    ! [D_209,A_210] : k2_xboole_0(k1_tarski(D_209),k1_tarski(A_210)) = k2_tarski(A_210,D_209) ),
    inference(superposition,[status(thm),theory(equality)],[c_5997,c_3329])).

tff(c_5996,plain,(
    ! [A_46,D_206] : k2_xboole_0(k1_tarski(A_46),k1_tarski(D_206)) = k2_tarski(A_46,D_206) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_5993])).

tff(c_6024,plain,(
    ! [D_209,A_210] : k2_tarski(D_209,A_210) = k2_tarski(A_210,D_209) ),
    inference(superposition,[status(thm),theory(equality)],[c_6018,c_5996])).

tff(c_36,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_676,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_615,c_36])).

tff(c_3335,plain,(
    k2_xboole_0(k2_tarski('#skF_3','#skF_1'),k2_tarski('#skF_2','#skF_1')) != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3329,c_676])).

tff(c_6049,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_3'),k2_tarski('#skF_1','#skF_2')) != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6024,c_6024,c_3335])).

tff(c_7899,plain,(
    k2_enumset1('#skF_1','#skF_3','#skF_1','#skF_2') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1802,c_6049])).

tff(c_7902,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_615,c_30,c_14,c_7899])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:36:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.90/2.65  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.90/2.66  
% 7.90/2.66  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.90/2.66  %$ k7_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 7.90/2.66  
% 7.90/2.66  %Foreground sorts:
% 7.90/2.66  
% 7.90/2.66  
% 7.90/2.66  %Background operators:
% 7.90/2.66  
% 7.90/2.66  
% 7.90/2.66  %Foreground operators:
% 7.90/2.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.90/2.66  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.90/2.66  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.90/2.66  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 7.90/2.66  tff(k7_enumset1, type, k7_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 7.90/2.66  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.90/2.66  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.90/2.66  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.90/2.66  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.90/2.66  tff('#skF_2', type, '#skF_2': $i).
% 7.90/2.66  tff('#skF_3', type, '#skF_3': $i).
% 7.90/2.66  tff('#skF_1', type, '#skF_1': $i).
% 7.90/2.66  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.90/2.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.90/2.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.90/2.66  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.90/2.66  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.90/2.66  
% 7.90/2.67  tff(f_43, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, D, C, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_enumset1)).
% 7.90/2.67  tff(f_55, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 7.90/2.67  tff(f_39, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, C, D, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t105_enumset1)).
% 7.90/2.67  tff(f_57, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 7.90/2.67  tff(f_53, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 7.90/2.67  tff(f_37, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_enumset1(A, B, C), k2_tarski(D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l57_enumset1)).
% 7.90/2.67  tff(f_51, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 7.90/2.67  tff(f_49, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 7.90/2.67  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 7.90/2.67  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 7.90/2.67  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 7.90/2.67  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 7.90/2.67  tff(f_31, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 7.90/2.67  tff(f_62, negated_conjecture, ~(![A, B, C]: (k2_xboole_0(k2_tarski(B, A), k2_tarski(C, A)) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t137_enumset1)).
% 7.90/2.67  tff(c_375, plain, (![B_90, D_91, C_92, A_93]: (k2_enumset1(B_90, D_91, C_92, A_93)=k2_enumset1(A_93, B_90, C_92, D_91))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.90/2.67  tff(c_30, plain, (![A_49, B_50, C_51]: (k2_enumset1(A_49, A_49, B_50, C_51)=k1_enumset1(A_49, B_50, C_51))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.90/2.67  tff(c_593, plain, (![B_98, D_99, C_100]: (k2_enumset1(B_98, D_99, C_100, B_98)=k1_enumset1(B_98, C_100, D_99))), inference(superposition, [status(thm), theory('equality')], [c_375, c_30])).
% 7.90/2.67  tff(c_174, plain, (![A_76, C_77, D_78, B_79]: (k2_enumset1(A_76, C_77, D_78, B_79)=k2_enumset1(A_76, B_79, C_77, D_78))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.90/2.67  tff(c_190, plain, (![B_79, C_77, D_78]: (k2_enumset1(B_79, C_77, D_78, B_79)=k1_enumset1(B_79, C_77, D_78))), inference(superposition, [status(thm), theory('equality')], [c_174, c_30])).
% 7.90/2.67  tff(c_615, plain, (![B_98, D_99, C_100]: (k1_enumset1(B_98, D_99, C_100)=k1_enumset1(B_98, C_100, D_99))), inference(superposition, [status(thm), theory('equality')], [c_593, c_190])).
% 7.90/2.67  tff(c_14, plain, (![A_17, C_19, D_20, B_18]: (k2_enumset1(A_17, C_19, D_20, B_18)=k2_enumset1(A_17, B_18, C_19, D_20))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.90/2.67  tff(c_32, plain, (![A_52, B_53, C_54, D_55]: (k3_enumset1(A_52, A_52, B_53, C_54, D_55)=k2_enumset1(A_52, B_53, C_54, D_55))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.90/2.67  tff(c_28, plain, (![A_47, B_48]: (k1_enumset1(A_47, A_47, B_48)=k2_tarski(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.90/2.67  tff(c_1772, plain, (![E_143, D_144, A_142, C_145, B_141]: (k2_xboole_0(k1_enumset1(A_142, B_141, C_145), k2_tarski(D_144, E_143))=k3_enumset1(A_142, B_141, C_145, D_144, E_143))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.90/2.67  tff(c_1796, plain, (![A_47, B_48, D_144, E_143]: (k3_enumset1(A_47, A_47, B_48, D_144, E_143)=k2_xboole_0(k2_tarski(A_47, B_48), k2_tarski(D_144, E_143)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_1772])).
% 7.90/2.67  tff(c_1802, plain, (![A_47, B_48, D_144, E_143]: (k2_xboole_0(k2_tarski(A_47, B_48), k2_tarski(D_144, E_143))=k2_enumset1(A_47, B_48, D_144, E_143))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1796])).
% 7.90/2.67  tff(c_26, plain, (![A_46]: (k2_tarski(A_46, A_46)=k1_tarski(A_46))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.90/2.67  tff(c_1300, plain, (![A_123, B_124, C_125, D_126]: (k2_xboole_0(k1_enumset1(A_123, B_124, C_125), k1_tarski(D_126))=k2_enumset1(A_123, B_124, C_125, D_126))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.90/2.67  tff(c_1324, plain, (![A_47, B_48, D_126]: (k2_xboole_0(k2_tarski(A_47, B_48), k1_tarski(D_126))=k2_enumset1(A_47, A_47, B_48, D_126))), inference(superposition, [status(thm), theory('equality')], [c_28, c_1300])).
% 7.90/2.67  tff(c_5972, plain, (![A_204, B_205, D_206]: (k2_xboole_0(k2_tarski(A_204, B_205), k1_tarski(D_206))=k1_enumset1(A_204, B_205, D_206))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1324])).
% 7.90/2.67  tff(c_5993, plain, (![A_46, D_206]: (k2_xboole_0(k1_tarski(A_46), k1_tarski(D_206))=k1_enumset1(A_46, A_46, D_206))), inference(superposition, [status(thm), theory('equality')], [c_26, c_5972])).
% 7.90/2.67  tff(c_5997, plain, (![A_207, D_208]: (k2_xboole_0(k1_tarski(A_207), k1_tarski(D_208))=k2_tarski(A_207, D_208))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_5993])).
% 7.90/2.67  tff(c_10, plain, (![A_10, B_11]: (k5_xboole_0(A_10, k4_xboole_0(B_11, A_10))=k2_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.90/2.67  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.90/2.67  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.90/2.67  tff(c_321, plain, (![A_88, B_89]: (k5_xboole_0(k5_xboole_0(A_88, B_89), k3_xboole_0(A_88, B_89))=k2_xboole_0(A_88, B_89))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.90/2.67  tff(c_3263, plain, (![B_173, A_174]: (k5_xboole_0(k5_xboole_0(B_173, A_174), k3_xboole_0(A_174, B_173))=k2_xboole_0(A_174, B_173))), inference(superposition, [status(thm), theory('equality')], [c_2, c_321])).
% 7.90/2.67  tff(c_6, plain, (![A_5, B_6, C_7]: (k5_xboole_0(k5_xboole_0(A_5, B_6), C_7)=k5_xboole_0(A_5, k5_xboole_0(B_6, C_7)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.90/2.67  tff(c_3282, plain, (![B_173, A_174]: (k5_xboole_0(B_173, k5_xboole_0(A_174, k3_xboole_0(A_174, B_173)))=k2_xboole_0(A_174, B_173))), inference(superposition, [status(thm), theory('equality')], [c_3263, c_6])).
% 7.90/2.67  tff(c_3329, plain, (![B_173, A_174]: (k2_xboole_0(B_173, A_174)=k2_xboole_0(A_174, B_173))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_4, c_3282])).
% 7.90/2.67  tff(c_6018, plain, (![D_209, A_210]: (k2_xboole_0(k1_tarski(D_209), k1_tarski(A_210))=k2_tarski(A_210, D_209))), inference(superposition, [status(thm), theory('equality')], [c_5997, c_3329])).
% 7.90/2.67  tff(c_5996, plain, (![A_46, D_206]: (k2_xboole_0(k1_tarski(A_46), k1_tarski(D_206))=k2_tarski(A_46, D_206))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_5993])).
% 7.90/2.67  tff(c_6024, plain, (![D_209, A_210]: (k2_tarski(D_209, A_210)=k2_tarski(A_210, D_209))), inference(superposition, [status(thm), theory('equality')], [c_6018, c_5996])).
% 7.90/2.67  tff(c_36, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.90/2.67  tff(c_676, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_615, c_36])).
% 7.90/2.67  tff(c_3335, plain, (k2_xboole_0(k2_tarski('#skF_3', '#skF_1'), k2_tarski('#skF_2', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3329, c_676])).
% 7.90/2.67  tff(c_6049, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_3'), k2_tarski('#skF_1', '#skF_2'))!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6024, c_6024, c_3335])).
% 7.90/2.67  tff(c_7899, plain, (k2_enumset1('#skF_1', '#skF_3', '#skF_1', '#skF_2')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1802, c_6049])).
% 7.90/2.67  tff(c_7902, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_615, c_30, c_14, c_7899])).
% 7.90/2.67  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.90/2.67  
% 7.90/2.67  Inference rules
% 7.90/2.67  ----------------------
% 7.90/2.67  #Ref     : 0
% 7.90/2.67  #Sup     : 2065
% 7.90/2.67  #Fact    : 0
% 7.90/2.67  #Define  : 0
% 7.90/2.67  #Split   : 0
% 7.90/2.67  #Chain   : 0
% 7.90/2.67  #Close   : 0
% 7.90/2.67  
% 7.90/2.67  Ordering : KBO
% 7.90/2.67  
% 7.90/2.67  Simplification rules
% 7.90/2.67  ----------------------
% 7.90/2.67  #Subsume      : 562
% 7.90/2.67  #Demod        : 1028
% 7.90/2.67  #Tautology    : 1005
% 7.90/2.67  #SimpNegUnit  : 0
% 7.90/2.67  #BackRed      : 5
% 7.90/2.67  
% 7.90/2.67  #Partial instantiations: 0
% 7.90/2.67  #Strategies tried      : 1
% 7.90/2.67  
% 7.90/2.67  Timing (in seconds)
% 7.90/2.67  ----------------------
% 7.90/2.68  Preprocessing        : 0.33
% 7.90/2.68  Parsing              : 0.17
% 7.90/2.68  CNF conversion       : 0.02
% 7.90/2.68  Main loop            : 1.58
% 7.90/2.68  Inferencing          : 0.44
% 7.90/2.68  Reduction            : 0.87
% 7.90/2.68  Demodulation         : 0.78
% 7.90/2.68  BG Simplification    : 0.05
% 7.90/2.68  Subsumption          : 0.17
% 7.90/2.68  Abstraction          : 0.08
% 7.90/2.68  MUC search           : 0.00
% 7.90/2.68  Cooper               : 0.00
% 7.90/2.68  Total                : 1.94
% 7.90/2.68  Index Insertion      : 0.00
% 7.90/2.68  Index Deletion       : 0.00
% 7.90/2.68  Index Matching       : 0.00
% 7.90/2.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
