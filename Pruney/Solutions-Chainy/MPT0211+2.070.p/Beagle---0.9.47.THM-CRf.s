%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:24 EST 2020

% Result     : Theorem 3.60s
% Output     : CNFRefutation 3.60s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 320 expanded)
%              Number of leaves         :   23 ( 120 expanded)
%              Depth                    :   13
%              Number of atoms          :   49 ( 306 expanded)
%              Number of equality atoms :   48 ( 305 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_41,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,C,D,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,D,C,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_37,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_enumset1(A,B,C),k2_tarski(D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l57_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_39,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_46,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(B,A),k2_tarski(C,A)) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_enumset1)).

tff(c_16,plain,(
    ! [A_23,B_24,C_25] : k2_enumset1(A_23,A_23,B_24,C_25) = k1_enumset1(A_23,B_24,C_25) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_104,plain,(
    ! [B_42,C_43,D_44,A_45] : k2_enumset1(B_42,C_43,D_44,A_45) = k2_enumset1(A_45,B_42,C_43,D_44) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_345,plain,(
    ! [A_60,B_61,C_62] : k2_enumset1(A_60,B_61,C_62,A_60) = k1_enumset1(A_60,B_61,C_62) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_104])).

tff(c_57,plain,(
    ! [A_38,D_39,C_40,B_41] : k2_enumset1(A_38,D_39,C_40,B_41) = k2_enumset1(A_38,B_41,C_40,D_39) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_73,plain,(
    ! [B_41,D_39,C_40] : k2_enumset1(B_41,D_39,C_40,B_41) = k1_enumset1(B_41,C_40,D_39) ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_16])).

tff(c_355,plain,(
    ! [A_60,C_62,B_61] : k1_enumset1(A_60,C_62,B_61) = k1_enumset1(A_60,B_61,C_62) ),
    inference(superposition,[status(thm),theory(equality)],[c_345,c_73])).

tff(c_8,plain,(
    ! [B_13,C_14,D_15,A_12] : k2_enumset1(B_13,C_14,D_15,A_12) = k2_enumset1(A_12,B_13,C_14,D_15) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_361,plain,(
    ! [B_61,C_62,A_60] : k2_enumset1(B_61,C_62,A_60,A_60) = k1_enumset1(A_60,B_61,C_62) ),
    inference(superposition,[status(thm),theory(equality)],[c_345,c_8])).

tff(c_10,plain,(
    ! [A_16,B_17,C_18,D_19] : k2_xboole_0(k1_enumset1(A_16,B_17,C_18),k1_tarski(D_19)) = k2_enumset1(A_16,B_17,C_18,D_19) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_20] : k2_tarski(A_20,A_20) = k1_tarski(A_20) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_675,plain,(
    ! [D_77,C_79,E_76,A_78,B_80] : k2_xboole_0(k1_enumset1(A_78,B_80,C_79),k2_tarski(D_77,E_76)) = k3_enumset1(A_78,B_80,C_79,D_77,E_76) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_702,plain,(
    ! [A_78,B_80,C_79,A_20] : k3_enumset1(A_78,B_80,C_79,A_20,A_20) = k2_xboole_0(k1_enumset1(A_78,B_80,C_79),k1_tarski(A_20)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_675])).

tff(c_1995,plain,(
    ! [A_108,B_109,C_110,A_111] : k3_enumset1(A_108,B_109,C_110,A_111,A_111) = k2_enumset1(A_108,B_109,C_110,A_111) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_702])).

tff(c_18,plain,(
    ! [A_26,B_27,C_28,D_29] : k3_enumset1(A_26,A_26,B_27,C_28,D_29) = k2_enumset1(A_26,B_27,C_28,D_29) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2002,plain,(
    ! [B_109,C_110,A_111] : k2_enumset1(B_109,C_110,A_111,A_111) = k2_enumset1(B_109,B_109,C_110,A_111) ),
    inference(superposition,[status(thm),theory(equality)],[c_1995,c_18])).

tff(c_2011,plain,(
    ! [B_109,C_110,A_111] : k1_enumset1(B_109,C_110,A_111) = k1_enumset1(A_111,B_109,C_110) ),
    inference(demodulation,[status(thm),theory(equality)],[c_361,c_16,c_2002])).

tff(c_14,plain,(
    ! [A_21,B_22] : k1_enumset1(A_21,A_21,B_22) = k2_tarski(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_408,plain,(
    ! [A_63,B_64,C_65,D_66] : k2_xboole_0(k1_enumset1(A_63,B_64,C_65),k1_tarski(D_66)) = k2_enumset1(A_63,B_64,C_65,D_66) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_426,plain,(
    ! [A_21,B_22,D_66] : k2_xboole_0(k2_tarski(A_21,B_22),k1_tarski(D_66)) = k2_enumset1(A_21,A_21,B_22,D_66) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_408])).

tff(c_431,plain,(
    ! [A_21,B_22,D_66] : k2_xboole_0(k2_tarski(A_21,B_22),k1_tarski(D_66)) = k1_enumset1(A_21,B_22,D_66) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_426])).

tff(c_2014,plain,(
    ! [B_112,C_113,A_114] : k1_enumset1(B_112,C_113,A_114) = k1_enumset1(A_114,B_112,C_113) ),
    inference(demodulation,[status(thm),theory(equality)],[c_361,c_16,c_2002])).

tff(c_223,plain,(
    ! [A_49,C_50,D_51] : k2_enumset1(A_49,C_50,C_50,D_51) = k1_enumset1(C_50,D_51,A_49) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_16])).

tff(c_253,plain,(
    ! [C_40,B_41] : k1_enumset1(C_40,B_41,B_41) = k1_enumset1(B_41,C_40,C_40) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_223])).

tff(c_2054,plain,(
    ! [C_113,A_114] : k1_enumset1(C_113,C_113,A_114) = k1_enumset1(C_113,A_114,A_114) ),
    inference(superposition,[status(thm),theory(equality)],[c_2014,c_253])).

tff(c_2148,plain,(
    ! [C_115,A_116] : k1_enumset1(C_115,A_116,A_116) = k2_tarski(C_115,A_116) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_2054])).

tff(c_2345,plain,(
    ! [A_125,C_126] : k1_enumset1(A_125,C_126,A_125) = k2_tarski(C_126,A_125) ),
    inference(superposition,[status(thm),theory(equality)],[c_2148,c_2011])).

tff(c_2374,plain,(
    ! [C_126,A_125,D_19] : k2_xboole_0(k2_tarski(C_126,A_125),k1_tarski(D_19)) = k2_enumset1(A_125,C_126,A_125,D_19) ),
    inference(superposition,[status(thm),theory(equality)],[c_2345,c_10])).

tff(c_2421,plain,(
    ! [A_125,C_126,D_19] : k2_enumset1(A_125,C_126,A_125,D_19) = k1_enumset1(C_126,A_125,D_19) ),
    inference(demodulation,[status(thm),theory(equality)],[c_431,c_2374])).

tff(c_6,plain,(
    ! [A_8,D_11,C_10,B_9] : k2_enumset1(A_8,D_11,C_10,B_9) = k2_enumset1(A_8,B_9,C_10,D_11) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_699,plain,(
    ! [A_21,B_22,D_77,E_76] : k3_enumset1(A_21,A_21,B_22,D_77,E_76) = k2_xboole_0(k2_tarski(A_21,B_22),k2_tarski(D_77,E_76)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_675])).

tff(c_705,plain,(
    ! [A_21,B_22,D_77,E_76] : k2_xboole_0(k2_tarski(A_21,B_22),k2_tarski(D_77,E_76)) = k2_enumset1(A_21,B_22,D_77,E_76) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_699])).

tff(c_2133,plain,(
    ! [C_113,A_114] : k1_enumset1(C_113,A_114,A_114) = k2_tarski(C_113,A_114) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_2054])).

tff(c_2147,plain,(
    ! [C_40,B_41] : k2_tarski(C_40,B_41) = k2_tarski(B_41,C_40) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2133,c_2133,c_253])).

tff(c_20,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_432,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_355,c_20])).

tff(c_2198,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),k2_tarski('#skF_1','#skF_3')) != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2147,c_2147,c_432])).

tff(c_2308,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_1','#skF_3') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_705,c_2198])).

tff(c_2309,plain,(
    k2_enumset1('#skF_1','#skF_3','#skF_1','#skF_2') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_2308])).

tff(c_2889,plain,(
    k1_enumset1('#skF_3','#skF_1','#skF_2') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2421,c_2309])).

tff(c_2892,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_355,c_2011,c_2889])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:17:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.60/1.62  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.60/1.63  
% 3.60/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.60/1.63  %$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 3.60/1.63  
% 3.60/1.63  %Foreground sorts:
% 3.60/1.63  
% 3.60/1.63  
% 3.60/1.63  %Background operators:
% 3.60/1.63  
% 3.60/1.63  
% 3.60/1.63  %Foreground operators:
% 3.60/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.60/1.63  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.60/1.63  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.60/1.63  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.60/1.63  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.60/1.63  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.60/1.63  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.60/1.63  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.60/1.63  tff('#skF_2', type, '#skF_2': $i).
% 3.60/1.63  tff('#skF_3', type, '#skF_3': $i).
% 3.60/1.63  tff('#skF_1', type, '#skF_1': $i).
% 3.60/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.60/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.60/1.63  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.60/1.63  
% 3.60/1.64  tff(f_41, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 3.60/1.64  tff(f_33, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, C, D, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t111_enumset1)).
% 3.60/1.64  tff(f_31, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, D, C, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t107_enumset1)).
% 3.60/1.64  tff(f_35, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 3.60/1.64  tff(f_37, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.60/1.64  tff(f_29, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_enumset1(A, B, C), k2_tarski(D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l57_enumset1)).
% 3.60/1.64  tff(f_43, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 3.60/1.64  tff(f_39, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.60/1.64  tff(f_46, negated_conjecture, ~(![A, B, C]: (k2_xboole_0(k2_tarski(B, A), k2_tarski(C, A)) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t137_enumset1)).
% 3.60/1.64  tff(c_16, plain, (![A_23, B_24, C_25]: (k2_enumset1(A_23, A_23, B_24, C_25)=k1_enumset1(A_23, B_24, C_25))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.60/1.64  tff(c_104, plain, (![B_42, C_43, D_44, A_45]: (k2_enumset1(B_42, C_43, D_44, A_45)=k2_enumset1(A_45, B_42, C_43, D_44))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.60/1.64  tff(c_345, plain, (![A_60, B_61, C_62]: (k2_enumset1(A_60, B_61, C_62, A_60)=k1_enumset1(A_60, B_61, C_62))), inference(superposition, [status(thm), theory('equality')], [c_16, c_104])).
% 3.60/1.64  tff(c_57, plain, (![A_38, D_39, C_40, B_41]: (k2_enumset1(A_38, D_39, C_40, B_41)=k2_enumset1(A_38, B_41, C_40, D_39))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.60/1.64  tff(c_73, plain, (![B_41, D_39, C_40]: (k2_enumset1(B_41, D_39, C_40, B_41)=k1_enumset1(B_41, C_40, D_39))), inference(superposition, [status(thm), theory('equality')], [c_57, c_16])).
% 3.60/1.64  tff(c_355, plain, (![A_60, C_62, B_61]: (k1_enumset1(A_60, C_62, B_61)=k1_enumset1(A_60, B_61, C_62))), inference(superposition, [status(thm), theory('equality')], [c_345, c_73])).
% 3.60/1.64  tff(c_8, plain, (![B_13, C_14, D_15, A_12]: (k2_enumset1(B_13, C_14, D_15, A_12)=k2_enumset1(A_12, B_13, C_14, D_15))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.60/1.64  tff(c_361, plain, (![B_61, C_62, A_60]: (k2_enumset1(B_61, C_62, A_60, A_60)=k1_enumset1(A_60, B_61, C_62))), inference(superposition, [status(thm), theory('equality')], [c_345, c_8])).
% 3.60/1.64  tff(c_10, plain, (![A_16, B_17, C_18, D_19]: (k2_xboole_0(k1_enumset1(A_16, B_17, C_18), k1_tarski(D_19))=k2_enumset1(A_16, B_17, C_18, D_19))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.60/1.64  tff(c_12, plain, (![A_20]: (k2_tarski(A_20, A_20)=k1_tarski(A_20))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.60/1.64  tff(c_675, plain, (![D_77, C_79, E_76, A_78, B_80]: (k2_xboole_0(k1_enumset1(A_78, B_80, C_79), k2_tarski(D_77, E_76))=k3_enumset1(A_78, B_80, C_79, D_77, E_76))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.60/1.64  tff(c_702, plain, (![A_78, B_80, C_79, A_20]: (k3_enumset1(A_78, B_80, C_79, A_20, A_20)=k2_xboole_0(k1_enumset1(A_78, B_80, C_79), k1_tarski(A_20)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_675])).
% 3.60/1.64  tff(c_1995, plain, (![A_108, B_109, C_110, A_111]: (k3_enumset1(A_108, B_109, C_110, A_111, A_111)=k2_enumset1(A_108, B_109, C_110, A_111))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_702])).
% 3.60/1.64  tff(c_18, plain, (![A_26, B_27, C_28, D_29]: (k3_enumset1(A_26, A_26, B_27, C_28, D_29)=k2_enumset1(A_26, B_27, C_28, D_29))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.60/1.64  tff(c_2002, plain, (![B_109, C_110, A_111]: (k2_enumset1(B_109, C_110, A_111, A_111)=k2_enumset1(B_109, B_109, C_110, A_111))), inference(superposition, [status(thm), theory('equality')], [c_1995, c_18])).
% 3.60/1.64  tff(c_2011, plain, (![B_109, C_110, A_111]: (k1_enumset1(B_109, C_110, A_111)=k1_enumset1(A_111, B_109, C_110))), inference(demodulation, [status(thm), theory('equality')], [c_361, c_16, c_2002])).
% 3.60/1.64  tff(c_14, plain, (![A_21, B_22]: (k1_enumset1(A_21, A_21, B_22)=k2_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.60/1.64  tff(c_408, plain, (![A_63, B_64, C_65, D_66]: (k2_xboole_0(k1_enumset1(A_63, B_64, C_65), k1_tarski(D_66))=k2_enumset1(A_63, B_64, C_65, D_66))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.60/1.64  tff(c_426, plain, (![A_21, B_22, D_66]: (k2_xboole_0(k2_tarski(A_21, B_22), k1_tarski(D_66))=k2_enumset1(A_21, A_21, B_22, D_66))), inference(superposition, [status(thm), theory('equality')], [c_14, c_408])).
% 3.60/1.64  tff(c_431, plain, (![A_21, B_22, D_66]: (k2_xboole_0(k2_tarski(A_21, B_22), k1_tarski(D_66))=k1_enumset1(A_21, B_22, D_66))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_426])).
% 3.60/1.64  tff(c_2014, plain, (![B_112, C_113, A_114]: (k1_enumset1(B_112, C_113, A_114)=k1_enumset1(A_114, B_112, C_113))), inference(demodulation, [status(thm), theory('equality')], [c_361, c_16, c_2002])).
% 3.60/1.64  tff(c_223, plain, (![A_49, C_50, D_51]: (k2_enumset1(A_49, C_50, C_50, D_51)=k1_enumset1(C_50, D_51, A_49))), inference(superposition, [status(thm), theory('equality')], [c_104, c_16])).
% 3.60/1.64  tff(c_253, plain, (![C_40, B_41]: (k1_enumset1(C_40, B_41, B_41)=k1_enumset1(B_41, C_40, C_40))), inference(superposition, [status(thm), theory('equality')], [c_73, c_223])).
% 3.60/1.64  tff(c_2054, plain, (![C_113, A_114]: (k1_enumset1(C_113, C_113, A_114)=k1_enumset1(C_113, A_114, A_114))), inference(superposition, [status(thm), theory('equality')], [c_2014, c_253])).
% 3.60/1.64  tff(c_2148, plain, (![C_115, A_116]: (k1_enumset1(C_115, A_116, A_116)=k2_tarski(C_115, A_116))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_2054])).
% 3.60/1.64  tff(c_2345, plain, (![A_125, C_126]: (k1_enumset1(A_125, C_126, A_125)=k2_tarski(C_126, A_125))), inference(superposition, [status(thm), theory('equality')], [c_2148, c_2011])).
% 3.60/1.64  tff(c_2374, plain, (![C_126, A_125, D_19]: (k2_xboole_0(k2_tarski(C_126, A_125), k1_tarski(D_19))=k2_enumset1(A_125, C_126, A_125, D_19))), inference(superposition, [status(thm), theory('equality')], [c_2345, c_10])).
% 3.60/1.64  tff(c_2421, plain, (![A_125, C_126, D_19]: (k2_enumset1(A_125, C_126, A_125, D_19)=k1_enumset1(C_126, A_125, D_19))), inference(demodulation, [status(thm), theory('equality')], [c_431, c_2374])).
% 3.60/1.64  tff(c_6, plain, (![A_8, D_11, C_10, B_9]: (k2_enumset1(A_8, D_11, C_10, B_9)=k2_enumset1(A_8, B_9, C_10, D_11))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.60/1.64  tff(c_699, plain, (![A_21, B_22, D_77, E_76]: (k3_enumset1(A_21, A_21, B_22, D_77, E_76)=k2_xboole_0(k2_tarski(A_21, B_22), k2_tarski(D_77, E_76)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_675])).
% 3.60/1.64  tff(c_705, plain, (![A_21, B_22, D_77, E_76]: (k2_xboole_0(k2_tarski(A_21, B_22), k2_tarski(D_77, E_76))=k2_enumset1(A_21, B_22, D_77, E_76))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_699])).
% 3.60/1.64  tff(c_2133, plain, (![C_113, A_114]: (k1_enumset1(C_113, A_114, A_114)=k2_tarski(C_113, A_114))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_2054])).
% 3.60/1.64  tff(c_2147, plain, (![C_40, B_41]: (k2_tarski(C_40, B_41)=k2_tarski(B_41, C_40))), inference(demodulation, [status(thm), theory('equality')], [c_2133, c_2133, c_253])).
% 3.60/1.64  tff(c_20, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.60/1.64  tff(c_432, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_355, c_20])).
% 3.60/1.64  tff(c_2198, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), k2_tarski('#skF_1', '#skF_3'))!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2147, c_2147, c_432])).
% 3.60/1.64  tff(c_2308, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_1', '#skF_3')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_705, c_2198])).
% 3.60/1.64  tff(c_2309, plain, (k2_enumset1('#skF_1', '#skF_3', '#skF_1', '#skF_2')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_2308])).
% 3.60/1.64  tff(c_2889, plain, (k1_enumset1('#skF_3', '#skF_1', '#skF_2')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2421, c_2309])).
% 3.60/1.64  tff(c_2892, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_355, c_2011, c_2889])).
% 3.60/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.60/1.64  
% 3.60/1.64  Inference rules
% 3.60/1.64  ----------------------
% 3.60/1.64  #Ref     : 0
% 3.60/1.64  #Sup     : 714
% 3.60/1.64  #Fact    : 0
% 3.60/1.64  #Define  : 0
% 3.60/1.64  #Split   : 0
% 3.60/1.64  #Chain   : 0
% 3.60/1.64  #Close   : 0
% 3.60/1.64  
% 3.60/1.64  Ordering : KBO
% 3.60/1.64  
% 3.60/1.64  Simplification rules
% 3.60/1.64  ----------------------
% 3.60/1.64  #Subsume      : 192
% 3.60/1.64  #Demod        : 409
% 3.60/1.64  #Tautology    : 450
% 3.60/1.64  #SimpNegUnit  : 0
% 3.60/1.64  #BackRed      : 5
% 3.60/1.64  
% 3.60/1.64  #Partial instantiations: 0
% 3.60/1.64  #Strategies tried      : 1
% 3.60/1.64  
% 3.60/1.64  Timing (in seconds)
% 3.60/1.64  ----------------------
% 3.60/1.64  Preprocessing        : 0.27
% 3.60/1.64  Parsing              : 0.14
% 3.60/1.64  CNF conversion       : 0.01
% 3.60/1.64  Main loop            : 0.60
% 3.60/1.64  Inferencing          : 0.21
% 3.60/1.64  Reduction            : 0.27
% 3.60/1.64  Demodulation         : 0.24
% 3.60/1.64  BG Simplification    : 0.02
% 3.60/1.64  Subsumption          : 0.07
% 3.60/1.65  Abstraction          : 0.04
% 3.60/1.65  MUC search           : 0.00
% 3.60/1.65  Cooper               : 0.00
% 3.60/1.65  Total                : 0.89
% 3.60/1.65  Index Insertion      : 0.00
% 3.60/1.65  Index Deletion       : 0.00
% 3.60/1.65  Index Matching       : 0.00
% 3.60/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
