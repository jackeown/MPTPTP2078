%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:04 EST 2020

% Result     : Theorem 4.88s
% Output     : CNFRefutation 4.88s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 430 expanded)
%              Number of leaves         :   25 ( 153 expanded)
%              Depth                    :   21
%              Number of atoms          :   57 ( 417 expanded)
%              Number of equality atoms :   56 ( 416 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_47,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_33,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_52,negated_conjecture,(
    ~ ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(c_22,plain,(
    ! [A_22,B_23,C_24] : k2_xboole_0(k1_tarski(A_22),k2_tarski(B_23,C_24)) = k1_enumset1(A_22,B_23,C_24) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_8,plain,(
    ! [A_7] : k2_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_8,B_9] : k2_xboole_0(A_8,k3_xboole_0(A_8,B_9)) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_93,plain,(
    ! [B_32,A_33] : k2_xboole_0(B_32,A_33) = k2_xboole_0(A_33,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_140,plain,(
    ! [A_34] : k2_xboole_0(k1_xboole_0,A_34) = A_34 ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_8])).

tff(c_172,plain,(
    ! [B_9] : k3_xboole_0(k1_xboole_0,B_9) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_140])).

tff(c_349,plain,(
    ! [A_45,B_46] : k5_xboole_0(A_45,k3_xboole_0(A_45,B_46)) = k4_xboole_0(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_370,plain,(
    ! [B_47] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,B_47) ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_349])).

tff(c_14,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k4_xboole_0(A_13,B_14)) = k3_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_383,plain,(
    ! [B_14] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k3_xboole_0(k1_xboole_0,B_14) ),
    inference(superposition,[status(thm),theory(equality)],[c_370,c_14])).

tff(c_394,plain,(
    k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_383])).

tff(c_361,plain,(
    ! [B_9] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,B_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_349])).

tff(c_439,plain,(
    ! [B_51] : k4_xboole_0(k1_xboole_0,B_51) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_394,c_361])).

tff(c_18,plain,(
    ! [A_18,B_19] : k5_xboole_0(A_18,k4_xboole_0(B_19,A_18)) = k2_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_447,plain,(
    ! [B_51] : k5_xboole_0(B_51,k1_xboole_0) = k2_xboole_0(B_51,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_439,c_18])).

tff(c_463,plain,(
    ! [B_51] : k5_xboole_0(B_51,k1_xboole_0) = B_51 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_447])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_20,plain,(
    ! [A_20,B_21] : k2_xboole_0(k1_tarski(A_20),k1_tarski(B_21)) = k2_tarski(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_397,plain,(
    ! [B_9] : k4_xboole_0(k1_xboole_0,B_9) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_394,c_361])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_203,plain,(
    ! [B_37] : k3_xboole_0(k1_xboole_0,B_37) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_140])).

tff(c_224,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_203])).

tff(c_358,plain,(
    ! [A_3] : k5_xboole_0(A_3,k1_xboole_0) = k4_xboole_0(A_3,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_224,c_349])).

tff(c_505,plain,(
    ! [A_56] : k4_xboole_0(A_56,k1_xboole_0) = A_56 ),
    inference(demodulation,[status(thm),theory(equality)],[c_463,c_358])).

tff(c_525,plain,(
    ! [A_56] : k4_xboole_0(A_56,A_56) = k3_xboole_0(A_56,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_505,c_14])).

tff(c_585,plain,(
    ! [A_58] : k4_xboole_0(A_58,A_58) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_224,c_525])).

tff(c_12,plain,(
    ! [A_10,B_11,C_12] : k4_xboole_0(k4_xboole_0(A_10,B_11),C_12) = k4_xboole_0(A_10,k2_xboole_0(B_11,C_12)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_597,plain,(
    ! [A_58,C_12] : k4_xboole_0(A_58,k2_xboole_0(A_58,C_12)) = k4_xboole_0(k1_xboole_0,C_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_585,c_12])).

tff(c_889,plain,(
    ! [A_69,C_70] : k4_xboole_0(A_69,k2_xboole_0(A_69,C_70)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_397,c_597])).

tff(c_931,plain,(
    ! [A_20,B_21] : k4_xboole_0(k1_tarski(A_20),k2_tarski(A_20,B_21)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_889])).

tff(c_542,plain,(
    ! [A_56] : k4_xboole_0(A_56,A_56) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_224,c_525])).

tff(c_504,plain,(
    ! [A_3] : k4_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(demodulation,[status(thm),theory(equality)],[c_463,c_358])).

tff(c_607,plain,(
    ! [A_58] : k4_xboole_0(A_58,k1_xboole_0) = k3_xboole_0(A_58,A_58) ),
    inference(superposition,[status(thm),theory(equality)],[c_585,c_14])).

tff(c_669,plain,(
    ! [A_60] : k3_xboole_0(A_60,A_60) = A_60 ),
    inference(demodulation,[status(thm),theory(equality)],[c_504,c_607])).

tff(c_6,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_675,plain,(
    ! [A_60] : k5_xboole_0(A_60,A_60) = k4_xboole_0(A_60,A_60) ),
    inference(superposition,[status(thm),theory(equality)],[c_669,c_6])).

tff(c_702,plain,(
    ! [A_60] : k5_xboole_0(A_60,A_60) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_542,c_675])).

tff(c_710,plain,(
    ! [A_61,B_62,C_63] : k5_xboole_0(k5_xboole_0(A_61,B_62),C_63) = k5_xboole_0(A_61,k5_xboole_0(B_62,C_63)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_5287,plain,(
    ! [A_161,B_162,C_163] : k5_xboole_0(A_161,k5_xboole_0(k4_xboole_0(B_162,A_161),C_163)) = k5_xboole_0(k2_xboole_0(A_161,B_162),C_163) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_710])).

tff(c_5403,plain,(
    ! [A_161,B_162] : k5_xboole_0(k2_xboole_0(A_161,B_162),k4_xboole_0(B_162,A_161)) = k5_xboole_0(A_161,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_702,c_5287])).

tff(c_5467,plain,(
    ! [A_164,B_165] : k5_xboole_0(k2_xboole_0(A_164,B_165),k4_xboole_0(B_165,A_164)) = A_164 ),
    inference(demodulation,[status(thm),theory(equality)],[c_463,c_5403])).

tff(c_5539,plain,(
    ! [A_20,B_21] : k5_xboole_0(k2_xboole_0(k2_tarski(A_20,B_21),k1_tarski(A_20)),k1_xboole_0) = k2_tarski(A_20,B_21) ),
    inference(superposition,[status(thm),theory(equality)],[c_931,c_5467])).

tff(c_5615,plain,(
    ! [A_20,B_21] : k1_enumset1(A_20,A_20,B_21) = k2_tarski(A_20,B_21) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_463,c_2,c_5539])).

tff(c_26,plain,(
    k1_enumset1('#skF_1','#skF_1','#skF_2') != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_5632,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5615,c_26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:27:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.88/1.98  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.88/1.99  
% 4.88/1.99  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.88/1.99  %$ k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 4.88/1.99  
% 4.88/1.99  %Foreground sorts:
% 4.88/1.99  
% 4.88/1.99  
% 4.88/1.99  %Background operators:
% 4.88/1.99  
% 4.88/1.99  
% 4.88/1.99  %Foreground operators:
% 4.88/1.99  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.88/1.99  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.88/1.99  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.88/1.99  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.88/1.99  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.88/1.99  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.88/1.99  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.88/1.99  tff('#skF_2', type, '#skF_2': $i).
% 4.88/1.99  tff('#skF_1', type, '#skF_1': $i).
% 4.88/1.99  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.88/1.99  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.88/1.99  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.88/1.99  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.88/1.99  
% 4.88/2.01  tff(f_47, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_enumset1)).
% 4.88/2.01  tff(f_33, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 4.88/2.01  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 4.88/2.01  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 4.88/2.01  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.88/2.01  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.88/2.01  tff(f_43, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 4.88/2.01  tff(f_45, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 4.88/2.01  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.88/2.01  tff(f_37, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 4.88/2.01  tff(f_41, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 4.88/2.01  tff(f_52, negated_conjecture, ~(![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 4.88/2.01  tff(c_22, plain, (![A_22, B_23, C_24]: (k2_xboole_0(k1_tarski(A_22), k2_tarski(B_23, C_24))=k1_enumset1(A_22, B_23, C_24))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.88/2.01  tff(c_8, plain, (![A_7]: (k2_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.88/2.01  tff(c_10, plain, (![A_8, B_9]: (k2_xboole_0(A_8, k3_xboole_0(A_8, B_9))=A_8)), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.88/2.01  tff(c_93, plain, (![B_32, A_33]: (k2_xboole_0(B_32, A_33)=k2_xboole_0(A_33, B_32))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.88/2.01  tff(c_140, plain, (![A_34]: (k2_xboole_0(k1_xboole_0, A_34)=A_34)), inference(superposition, [status(thm), theory('equality')], [c_93, c_8])).
% 4.88/2.01  tff(c_172, plain, (![B_9]: (k3_xboole_0(k1_xboole_0, B_9)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10, c_140])).
% 4.88/2.01  tff(c_349, plain, (![A_45, B_46]: (k5_xboole_0(A_45, k3_xboole_0(A_45, B_46))=k4_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.88/2.01  tff(c_370, plain, (![B_47]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, B_47))), inference(superposition, [status(thm), theory('equality')], [c_172, c_349])).
% 4.88/2.01  tff(c_14, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k4_xboole_0(A_13, B_14))=k3_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.88/2.01  tff(c_383, plain, (![B_14]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k3_xboole_0(k1_xboole_0, B_14))), inference(superposition, [status(thm), theory('equality')], [c_370, c_14])).
% 4.88/2.01  tff(c_394, plain, (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_172, c_383])).
% 4.88/2.01  tff(c_361, plain, (![B_9]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, B_9))), inference(superposition, [status(thm), theory('equality')], [c_172, c_349])).
% 4.88/2.01  tff(c_439, plain, (![B_51]: (k4_xboole_0(k1_xboole_0, B_51)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_394, c_361])).
% 4.88/2.01  tff(c_18, plain, (![A_18, B_19]: (k5_xboole_0(A_18, k4_xboole_0(B_19, A_18))=k2_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.88/2.01  tff(c_447, plain, (![B_51]: (k5_xboole_0(B_51, k1_xboole_0)=k2_xboole_0(B_51, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_439, c_18])).
% 4.88/2.01  tff(c_463, plain, (![B_51]: (k5_xboole_0(B_51, k1_xboole_0)=B_51)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_447])).
% 4.88/2.01  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.88/2.01  tff(c_20, plain, (![A_20, B_21]: (k2_xboole_0(k1_tarski(A_20), k1_tarski(B_21))=k2_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.88/2.01  tff(c_397, plain, (![B_9]: (k4_xboole_0(k1_xboole_0, B_9)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_394, c_361])).
% 4.88/2.01  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.88/2.01  tff(c_203, plain, (![B_37]: (k3_xboole_0(k1_xboole_0, B_37)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10, c_140])).
% 4.88/2.01  tff(c_224, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4, c_203])).
% 4.88/2.01  tff(c_358, plain, (![A_3]: (k5_xboole_0(A_3, k1_xboole_0)=k4_xboole_0(A_3, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_224, c_349])).
% 4.88/2.01  tff(c_505, plain, (![A_56]: (k4_xboole_0(A_56, k1_xboole_0)=A_56)), inference(demodulation, [status(thm), theory('equality')], [c_463, c_358])).
% 4.88/2.01  tff(c_525, plain, (![A_56]: (k4_xboole_0(A_56, A_56)=k3_xboole_0(A_56, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_505, c_14])).
% 4.88/2.01  tff(c_585, plain, (![A_58]: (k4_xboole_0(A_58, A_58)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_224, c_525])).
% 4.88/2.01  tff(c_12, plain, (![A_10, B_11, C_12]: (k4_xboole_0(k4_xboole_0(A_10, B_11), C_12)=k4_xboole_0(A_10, k2_xboole_0(B_11, C_12)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.88/2.01  tff(c_597, plain, (![A_58, C_12]: (k4_xboole_0(A_58, k2_xboole_0(A_58, C_12))=k4_xboole_0(k1_xboole_0, C_12))), inference(superposition, [status(thm), theory('equality')], [c_585, c_12])).
% 4.88/2.01  tff(c_889, plain, (![A_69, C_70]: (k4_xboole_0(A_69, k2_xboole_0(A_69, C_70))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_397, c_597])).
% 4.88/2.01  tff(c_931, plain, (![A_20, B_21]: (k4_xboole_0(k1_tarski(A_20), k2_tarski(A_20, B_21))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_20, c_889])).
% 4.88/2.01  tff(c_542, plain, (![A_56]: (k4_xboole_0(A_56, A_56)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_224, c_525])).
% 4.88/2.01  tff(c_504, plain, (![A_3]: (k4_xboole_0(A_3, k1_xboole_0)=A_3)), inference(demodulation, [status(thm), theory('equality')], [c_463, c_358])).
% 4.88/2.01  tff(c_607, plain, (![A_58]: (k4_xboole_0(A_58, k1_xboole_0)=k3_xboole_0(A_58, A_58))), inference(superposition, [status(thm), theory('equality')], [c_585, c_14])).
% 4.88/2.01  tff(c_669, plain, (![A_60]: (k3_xboole_0(A_60, A_60)=A_60)), inference(demodulation, [status(thm), theory('equality')], [c_504, c_607])).
% 4.88/2.01  tff(c_6, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.88/2.01  tff(c_675, plain, (![A_60]: (k5_xboole_0(A_60, A_60)=k4_xboole_0(A_60, A_60))), inference(superposition, [status(thm), theory('equality')], [c_669, c_6])).
% 4.88/2.01  tff(c_702, plain, (![A_60]: (k5_xboole_0(A_60, A_60)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_542, c_675])).
% 4.88/2.01  tff(c_710, plain, (![A_61, B_62, C_63]: (k5_xboole_0(k5_xboole_0(A_61, B_62), C_63)=k5_xboole_0(A_61, k5_xboole_0(B_62, C_63)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.88/2.01  tff(c_5287, plain, (![A_161, B_162, C_163]: (k5_xboole_0(A_161, k5_xboole_0(k4_xboole_0(B_162, A_161), C_163))=k5_xboole_0(k2_xboole_0(A_161, B_162), C_163))), inference(superposition, [status(thm), theory('equality')], [c_18, c_710])).
% 4.88/2.01  tff(c_5403, plain, (![A_161, B_162]: (k5_xboole_0(k2_xboole_0(A_161, B_162), k4_xboole_0(B_162, A_161))=k5_xboole_0(A_161, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_702, c_5287])).
% 4.88/2.01  tff(c_5467, plain, (![A_164, B_165]: (k5_xboole_0(k2_xboole_0(A_164, B_165), k4_xboole_0(B_165, A_164))=A_164)), inference(demodulation, [status(thm), theory('equality')], [c_463, c_5403])).
% 4.88/2.01  tff(c_5539, plain, (![A_20, B_21]: (k5_xboole_0(k2_xboole_0(k2_tarski(A_20, B_21), k1_tarski(A_20)), k1_xboole_0)=k2_tarski(A_20, B_21))), inference(superposition, [status(thm), theory('equality')], [c_931, c_5467])).
% 4.88/2.01  tff(c_5615, plain, (![A_20, B_21]: (k1_enumset1(A_20, A_20, B_21)=k2_tarski(A_20, B_21))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_463, c_2, c_5539])).
% 4.88/2.01  tff(c_26, plain, (k1_enumset1('#skF_1', '#skF_1', '#skF_2')!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.88/2.01  tff(c_5632, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5615, c_26])).
% 4.88/2.01  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.88/2.01  
% 4.88/2.01  Inference rules
% 4.88/2.01  ----------------------
% 4.88/2.01  #Ref     : 0
% 4.88/2.01  #Sup     : 1389
% 4.88/2.01  #Fact    : 0
% 4.88/2.01  #Define  : 0
% 4.88/2.01  #Split   : 0
% 4.88/2.01  #Chain   : 0
% 4.88/2.01  #Close   : 0
% 4.88/2.01  
% 4.88/2.01  Ordering : KBO
% 4.88/2.01  
% 4.88/2.01  Simplification rules
% 4.88/2.01  ----------------------
% 4.88/2.01  #Subsume      : 13
% 4.88/2.01  #Demod        : 1131
% 4.88/2.01  #Tautology    : 961
% 4.88/2.01  #SimpNegUnit  : 0
% 4.88/2.01  #BackRed      : 3
% 4.88/2.01  
% 4.88/2.01  #Partial instantiations: 0
% 4.88/2.01  #Strategies tried      : 1
% 4.88/2.01  
% 4.88/2.01  Timing (in seconds)
% 4.88/2.01  ----------------------
% 4.88/2.01  Preprocessing        : 0.30
% 4.88/2.01  Parsing              : 0.16
% 4.88/2.01  CNF conversion       : 0.02
% 4.88/2.01  Main loop            : 0.95
% 4.88/2.01  Inferencing          : 0.31
% 4.88/2.01  Reduction            : 0.43
% 4.88/2.01  Demodulation         : 0.37
% 4.88/2.01  BG Simplification    : 0.03
% 4.88/2.01  Subsumption          : 0.12
% 4.88/2.01  Abstraction          : 0.05
% 4.88/2.01  MUC search           : 0.00
% 4.88/2.01  Cooper               : 0.00
% 4.88/2.01  Total                : 1.28
% 4.88/2.01  Index Insertion      : 0.00
% 4.88/2.01  Index Deletion       : 0.00
% 4.88/2.01  Index Matching       : 0.00
% 4.88/2.01  BG Taut test         : 0.00
%------------------------------------------------------------------------------
