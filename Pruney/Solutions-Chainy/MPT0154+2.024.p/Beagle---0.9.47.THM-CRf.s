%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:07 EST 2020

% Result     : Theorem 7.74s
% Output     : CNFRefutation 7.78s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 197 expanded)
%              Number of leaves         :   23 (  75 expanded)
%              Depth                    :   14
%              Number of atoms          :   48 ( 184 expanded)
%              Number of equality atoms :   47 ( 183 expanded)
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

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_43,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_50,negated_conjecture,(
    ~ ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_52,plain,(
    ! [A_26,B_27] : k2_xboole_0(A_26,k3_xboole_0(A_26,B_27)) = A_26 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_61,plain,(
    ! [A_3] : k2_xboole_0(A_3,A_3) = A_3 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_52])).

tff(c_10,plain,(
    ! [A_8,B_9] : k2_xboole_0(A_8,k3_xboole_0(A_8,B_9)) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_83,plain,(
    ! [A_29,B_30] : k4_xboole_0(A_29,k2_xboole_0(A_29,B_30)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_93,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_83])).

tff(c_183,plain,(
    ! [A_36,B_37] : k5_xboole_0(A_36,k4_xboole_0(B_37,A_36)) = k2_xboole_0(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_192,plain,(
    ! [A_8] : k5_xboole_0(A_8,k1_xboole_0) = k2_xboole_0(A_8,A_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_183])).

tff(c_198,plain,(
    ! [A_8] : k5_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_192])).

tff(c_20,plain,(
    ! [A_19,B_20,C_21] : k2_xboole_0(k1_tarski(A_19),k2_tarski(B_20,C_21)) = k1_enumset1(A_19,B_20,C_21) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_244,plain,(
    ! [A_42,B_43] : k2_xboole_0(k1_tarski(A_42),k1_tarski(B_43)) = k2_tarski(A_42,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_12,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k2_xboole_0(A_10,B_11)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_250,plain,(
    ! [A_42,B_43] : k4_xboole_0(k1_tarski(A_42),k2_tarski(A_42,B_43)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_244,c_12])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_208,plain,(
    ! [A_39,B_40] : k5_xboole_0(A_39,k3_xboole_0(A_39,B_40)) = k4_xboole_0(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_217,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_208])).

tff(c_223,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k4_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_208])).

tff(c_226,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_223])).

tff(c_6,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_370,plain,(
    ! [A_58,B_59,C_60] : k5_xboole_0(k5_xboole_0(A_58,B_59),C_60) = k5_xboole_0(A_58,k5_xboole_0(B_59,C_60)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1492,plain,(
    ! [A_85,B_86,C_87] : k5_xboole_0(A_85,k5_xboole_0(k3_xboole_0(A_85,B_86),C_87)) = k5_xboole_0(k4_xboole_0(A_85,B_86),C_87) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_370])).

tff(c_1569,plain,(
    ! [A_85,B_86] : k5_xboole_0(k4_xboole_0(A_85,B_86),k3_xboole_0(A_85,B_86)) = k5_xboole_0(A_85,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_226,c_1492])).

tff(c_2236,plain,(
    ! [A_99,B_100] : k5_xboole_0(k4_xboole_0(A_99,B_100),k3_xboole_0(A_99,B_100)) = A_99 ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_1569])).

tff(c_560,plain,(
    ! [A_64,C_65] : k5_xboole_0(A_64,k5_xboole_0(A_64,C_65)) = k5_xboole_0(k1_xboole_0,C_65) ),
    inference(superposition,[status(thm),theory(equality)],[c_226,c_370])).

tff(c_625,plain,(
    ! [A_3] : k5_xboole_0(k1_xboole_0,A_3) = k5_xboole_0(A_3,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_226,c_560])).

tff(c_649,plain,(
    ! [A_3] : k5_xboole_0(k1_xboole_0,A_3) = A_3 ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_625])).

tff(c_412,plain,(
    ! [A_3,C_60] : k5_xboole_0(A_3,k5_xboole_0(A_3,C_60)) = k5_xboole_0(k1_xboole_0,C_60) ),
    inference(superposition,[status(thm),theory(equality)],[c_226,c_370])).

tff(c_652,plain,(
    ! [A_3,C_60] : k5_xboole_0(A_3,k5_xboole_0(A_3,C_60)) = C_60 ),
    inference(demodulation,[status(thm),theory(equality)],[c_649,c_412])).

tff(c_3727,plain,(
    ! [A_133,B_134] : k5_xboole_0(k4_xboole_0(A_133,B_134),A_133) = k3_xboole_0(A_133,B_134) ),
    inference(superposition,[status(thm),theory(equality)],[c_2236,c_652])).

tff(c_16,plain,(
    ! [A_15,B_16] : k5_xboole_0(A_15,k4_xboole_0(B_16,A_15)) = k2_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_433,plain,(
    ! [A_15,B_16,C_60] : k5_xboole_0(A_15,k5_xboole_0(k4_xboole_0(B_16,A_15),C_60)) = k5_xboole_0(k2_xboole_0(A_15,B_16),C_60) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_370])).

tff(c_3754,plain,(
    ! [B_134,A_133] : k5_xboole_0(k2_xboole_0(B_134,A_133),A_133) = k5_xboole_0(B_134,k3_xboole_0(A_133,B_134)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3727,c_433])).

tff(c_5521,plain,(
    ! [B_164,A_165] : k5_xboole_0(k2_xboole_0(B_164,A_165),A_165) = k4_xboole_0(B_164,A_165) ),
    inference(demodulation,[status(thm),theory(equality)],[c_217,c_3754])).

tff(c_7264,plain,(
    ! [B_187,A_188] : k5_xboole_0(k2_xboole_0(B_187,A_188),k4_xboole_0(B_187,A_188)) = A_188 ),
    inference(superposition,[status(thm),theory(equality)],[c_5521,c_652])).

tff(c_7359,plain,(
    ! [A_42,B_43] : k5_xboole_0(k2_xboole_0(k1_tarski(A_42),k2_tarski(A_42,B_43)),k1_xboole_0) = k2_tarski(A_42,B_43) ),
    inference(superposition,[status(thm),theory(equality)],[c_250,c_7264])).

tff(c_7403,plain,(
    ! [A_42,B_43] : k1_enumset1(A_42,A_42,B_43) = k2_tarski(A_42,B_43) ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_20,c_7359])).

tff(c_24,plain,(
    k1_enumset1('#skF_1','#skF_1','#skF_2') != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_7411,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7403,c_24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:59:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.74/3.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.74/3.32  
% 7.74/3.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.74/3.33  %$ k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 7.74/3.33  
% 7.74/3.33  %Foreground sorts:
% 7.74/3.33  
% 7.74/3.33  
% 7.74/3.33  %Background operators:
% 7.74/3.33  
% 7.74/3.33  
% 7.74/3.33  %Foreground operators:
% 7.74/3.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.74/3.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.74/3.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.74/3.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.74/3.33  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.74/3.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.74/3.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.74/3.33  tff('#skF_2', type, '#skF_2': $i).
% 7.74/3.33  tff('#skF_1', type, '#skF_1': $i).
% 7.74/3.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.74/3.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.74/3.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.74/3.33  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.74/3.33  
% 7.78/3.35  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 7.78/3.35  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 7.78/3.35  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 7.78/3.35  tff(f_41, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 7.78/3.35  tff(f_45, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_enumset1)).
% 7.78/3.35  tff(f_43, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 7.78/3.35  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 7.78/3.35  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 7.78/3.35  tff(f_39, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 7.78/3.35  tff(f_50, negated_conjecture, ~(![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 7.78/3.35  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.78/3.35  tff(c_52, plain, (![A_26, B_27]: (k2_xboole_0(A_26, k3_xboole_0(A_26, B_27))=A_26)), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.78/3.35  tff(c_61, plain, (![A_3]: (k2_xboole_0(A_3, A_3)=A_3)), inference(superposition, [status(thm), theory('equality')], [c_4, c_52])).
% 7.78/3.35  tff(c_10, plain, (![A_8, B_9]: (k2_xboole_0(A_8, k3_xboole_0(A_8, B_9))=A_8)), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.78/3.35  tff(c_83, plain, (![A_29, B_30]: (k4_xboole_0(A_29, k2_xboole_0(A_29, B_30))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.78/3.35  tff(c_93, plain, (![A_8]: (k4_xboole_0(A_8, A_8)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10, c_83])).
% 7.78/3.35  tff(c_183, plain, (![A_36, B_37]: (k5_xboole_0(A_36, k4_xboole_0(B_37, A_36))=k2_xboole_0(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.78/3.35  tff(c_192, plain, (![A_8]: (k5_xboole_0(A_8, k1_xboole_0)=k2_xboole_0(A_8, A_8))), inference(superposition, [status(thm), theory('equality')], [c_93, c_183])).
% 7.78/3.35  tff(c_198, plain, (![A_8]: (k5_xboole_0(A_8, k1_xboole_0)=A_8)), inference(demodulation, [status(thm), theory('equality')], [c_61, c_192])).
% 7.78/3.35  tff(c_20, plain, (![A_19, B_20, C_21]: (k2_xboole_0(k1_tarski(A_19), k2_tarski(B_20, C_21))=k1_enumset1(A_19, B_20, C_21))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.78/3.35  tff(c_244, plain, (![A_42, B_43]: (k2_xboole_0(k1_tarski(A_42), k1_tarski(B_43))=k2_tarski(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.78/3.35  tff(c_12, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k2_xboole_0(A_10, B_11))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.78/3.35  tff(c_250, plain, (![A_42, B_43]: (k4_xboole_0(k1_tarski(A_42), k2_tarski(A_42, B_43))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_244, c_12])).
% 7.78/3.35  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.78/3.35  tff(c_208, plain, (![A_39, B_40]: (k5_xboole_0(A_39, k3_xboole_0(A_39, B_40))=k4_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.78/3.35  tff(c_217, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_208])).
% 7.78/3.35  tff(c_223, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k4_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_208])).
% 7.78/3.35  tff(c_226, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_93, c_223])).
% 7.78/3.35  tff(c_6, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.78/3.35  tff(c_370, plain, (![A_58, B_59, C_60]: (k5_xboole_0(k5_xboole_0(A_58, B_59), C_60)=k5_xboole_0(A_58, k5_xboole_0(B_59, C_60)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.78/3.35  tff(c_1492, plain, (![A_85, B_86, C_87]: (k5_xboole_0(A_85, k5_xboole_0(k3_xboole_0(A_85, B_86), C_87))=k5_xboole_0(k4_xboole_0(A_85, B_86), C_87))), inference(superposition, [status(thm), theory('equality')], [c_6, c_370])).
% 7.78/3.35  tff(c_1569, plain, (![A_85, B_86]: (k5_xboole_0(k4_xboole_0(A_85, B_86), k3_xboole_0(A_85, B_86))=k5_xboole_0(A_85, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_226, c_1492])).
% 7.78/3.35  tff(c_2236, plain, (![A_99, B_100]: (k5_xboole_0(k4_xboole_0(A_99, B_100), k3_xboole_0(A_99, B_100))=A_99)), inference(demodulation, [status(thm), theory('equality')], [c_198, c_1569])).
% 7.78/3.35  tff(c_560, plain, (![A_64, C_65]: (k5_xboole_0(A_64, k5_xboole_0(A_64, C_65))=k5_xboole_0(k1_xboole_0, C_65))), inference(superposition, [status(thm), theory('equality')], [c_226, c_370])).
% 7.78/3.35  tff(c_625, plain, (![A_3]: (k5_xboole_0(k1_xboole_0, A_3)=k5_xboole_0(A_3, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_226, c_560])).
% 7.78/3.35  tff(c_649, plain, (![A_3]: (k5_xboole_0(k1_xboole_0, A_3)=A_3)), inference(demodulation, [status(thm), theory('equality')], [c_198, c_625])).
% 7.78/3.35  tff(c_412, plain, (![A_3, C_60]: (k5_xboole_0(A_3, k5_xboole_0(A_3, C_60))=k5_xboole_0(k1_xboole_0, C_60))), inference(superposition, [status(thm), theory('equality')], [c_226, c_370])).
% 7.78/3.35  tff(c_652, plain, (![A_3, C_60]: (k5_xboole_0(A_3, k5_xboole_0(A_3, C_60))=C_60)), inference(demodulation, [status(thm), theory('equality')], [c_649, c_412])).
% 7.78/3.35  tff(c_3727, plain, (![A_133, B_134]: (k5_xboole_0(k4_xboole_0(A_133, B_134), A_133)=k3_xboole_0(A_133, B_134))), inference(superposition, [status(thm), theory('equality')], [c_2236, c_652])).
% 7.78/3.35  tff(c_16, plain, (![A_15, B_16]: (k5_xboole_0(A_15, k4_xboole_0(B_16, A_15))=k2_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.78/3.35  tff(c_433, plain, (![A_15, B_16, C_60]: (k5_xboole_0(A_15, k5_xboole_0(k4_xboole_0(B_16, A_15), C_60))=k5_xboole_0(k2_xboole_0(A_15, B_16), C_60))), inference(superposition, [status(thm), theory('equality')], [c_16, c_370])).
% 7.78/3.35  tff(c_3754, plain, (![B_134, A_133]: (k5_xboole_0(k2_xboole_0(B_134, A_133), A_133)=k5_xboole_0(B_134, k3_xboole_0(A_133, B_134)))), inference(superposition, [status(thm), theory('equality')], [c_3727, c_433])).
% 7.78/3.35  tff(c_5521, plain, (![B_164, A_165]: (k5_xboole_0(k2_xboole_0(B_164, A_165), A_165)=k4_xboole_0(B_164, A_165))), inference(demodulation, [status(thm), theory('equality')], [c_217, c_3754])).
% 7.78/3.35  tff(c_7264, plain, (![B_187, A_188]: (k5_xboole_0(k2_xboole_0(B_187, A_188), k4_xboole_0(B_187, A_188))=A_188)), inference(superposition, [status(thm), theory('equality')], [c_5521, c_652])).
% 7.78/3.35  tff(c_7359, plain, (![A_42, B_43]: (k5_xboole_0(k2_xboole_0(k1_tarski(A_42), k2_tarski(A_42, B_43)), k1_xboole_0)=k2_tarski(A_42, B_43))), inference(superposition, [status(thm), theory('equality')], [c_250, c_7264])).
% 7.78/3.35  tff(c_7403, plain, (![A_42, B_43]: (k1_enumset1(A_42, A_42, B_43)=k2_tarski(A_42, B_43))), inference(demodulation, [status(thm), theory('equality')], [c_198, c_20, c_7359])).
% 7.78/3.35  tff(c_24, plain, (k1_enumset1('#skF_1', '#skF_1', '#skF_2')!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.78/3.35  tff(c_7411, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7403, c_24])).
% 7.78/3.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.78/3.35  
% 7.78/3.35  Inference rules
% 7.78/3.35  ----------------------
% 7.78/3.35  #Ref     : 0
% 7.78/3.35  #Sup     : 1818
% 7.78/3.35  #Fact    : 0
% 7.78/3.35  #Define  : 0
% 7.78/3.35  #Split   : 0
% 7.78/3.35  #Chain   : 0
% 7.78/3.35  #Close   : 0
% 7.78/3.35  
% 7.78/3.35  Ordering : KBO
% 7.78/3.35  
% 7.78/3.35  Simplification rules
% 7.78/3.35  ----------------------
% 7.78/3.35  #Subsume      : 18
% 7.78/3.35  #Demod        : 1981
% 7.78/3.35  #Tautology    : 1173
% 7.78/3.35  #SimpNegUnit  : 0
% 7.78/3.35  #BackRed      : 10
% 7.78/3.35  
% 7.78/3.35  #Partial instantiations: 0
% 7.78/3.35  #Strategies tried      : 1
% 7.78/3.35  
% 7.78/3.35  Timing (in seconds)
% 7.78/3.35  ----------------------
% 7.78/3.35  Preprocessing        : 0.45
% 7.78/3.35  Parsing              : 0.23
% 7.78/3.35  CNF conversion       : 0.03
% 7.78/3.35  Main loop            : 1.95
% 7.78/3.35  Inferencing          : 0.60
% 7.78/3.35  Reduction            : 0.94
% 7.78/3.35  Demodulation         : 0.81
% 7.78/3.35  BG Simplification    : 0.08
% 7.78/3.35  Subsumption          : 0.23
% 7.78/3.35  Abstraction          : 0.11
% 7.78/3.35  MUC search           : 0.00
% 7.78/3.35  Cooper               : 0.00
% 7.78/3.35  Total                : 2.45
% 7.78/3.35  Index Insertion      : 0.00
% 7.78/3.36  Index Deletion       : 0.00
% 7.78/3.36  Index Matching       : 0.00
% 7.78/3.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
