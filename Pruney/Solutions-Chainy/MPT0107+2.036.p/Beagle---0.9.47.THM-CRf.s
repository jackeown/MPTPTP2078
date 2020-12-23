%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:57 EST 2020

% Result     : Theorem 4.42s
% Output     : CNFRefutation 4.42s
% Verified   : 
% Statistics : Number of formulae       :   57 (  91 expanded)
%              Number of leaves         :   21 (  39 expanded)
%              Depth                    :   10
%              Number of atoms          :   47 (  81 expanded)
%              Number of equality atoms :   46 (  80 expanded)
%              Maximal formula depth    :    4 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(f_45,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_37,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_41,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_48,negated_conjecture,(
    ~ ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_155,plain,(
    ! [A_26,B_27] : k5_xboole_0(A_26,k4_xboole_0(B_27,A_26)) = k2_xboole_0(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_58,plain,(
    ! [B_23,A_24] : k5_xboole_0(B_23,A_24) = k5_xboole_0(A_24,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_11] : k5_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_74,plain,(
    ! [A_24] : k5_xboole_0(k1_xboole_0,A_24) = A_24 ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_12])).

tff(c_162,plain,(
    ! [B_27] : k4_xboole_0(B_27,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_74])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_16,plain,(
    ! [A_15] : k5_xboole_0(A_15,A_15) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_316,plain,(
    ! [A_39,B_40] : k5_xboole_0(k5_xboole_0(A_39,B_40),k3_xboole_0(A_39,B_40)) = k2_xboole_0(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_364,plain,(
    ! [A_5] : k5_xboole_0(k5_xboole_0(A_5,A_5),A_5) = k2_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_316])).

tff(c_372,plain,(
    ! [A_41] : k2_xboole_0(A_41,A_41) = A_41 ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_16,c_364])).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(k4_xboole_0(A_3,B_4),k4_xboole_0(B_4,A_3)) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_379,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k4_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_372,c_4])).

tff(c_392,plain,(
    ! [A_42] : k4_xboole_0(A_42,A_42) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_379])).

tff(c_10,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = k3_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_406,plain,(
    ! [A_42] : k4_xboole_0(A_42,k1_xboole_0) = k3_xboole_0(A_42,A_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_392,c_10])).

tff(c_424,plain,(
    ! [A_42] : k2_xboole_0(k1_xboole_0,A_42) = A_42 ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_6,c_406])).

tff(c_8,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_202,plain,(
    ! [A_31,B_32] : k4_xboole_0(A_31,k4_xboole_0(A_31,B_32)) = k3_xboole_0(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_220,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k4_xboole_0(A_7,B_8)) = k3_xboole_0(A_7,k3_xboole_0(A_7,B_8)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_202])).

tff(c_228,plain,(
    ! [A_7,B_8] : k3_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k3_xboole_0(A_7,B_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_220])).

tff(c_18,plain,(
    ! [A_16,B_17] : k5_xboole_0(k5_xboole_0(A_16,B_17),k3_xboole_0(A_16,B_17)) = k2_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_459,plain,(
    ! [A_44,B_45,C_46] : k5_xboole_0(k5_xboole_0(A_44,B_45),C_46) = k5_xboole_0(A_44,k5_xboole_0(B_45,C_46)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1585,plain,(
    ! [A_69,B_70] : k5_xboole_0(A_69,k5_xboole_0(B_70,k3_xboole_0(A_69,B_70))) = k2_xboole_0(A_69,B_70) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_459])).

tff(c_1657,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k5_xboole_0(k3_xboole_0(A_7,B_8),k3_xboole_0(A_7,B_8))) = k2_xboole_0(A_7,k3_xboole_0(A_7,B_8)) ),
    inference(superposition,[status(thm),theory(equality)],[c_228,c_1585])).

tff(c_1686,plain,(
    ! [A_71,B_72] : k2_xboole_0(A_71,k3_xboole_0(A_71,B_72)) = A_71 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_16,c_1657])).

tff(c_20,plain,(
    ! [A_18,B_19] : k5_xboole_0(A_18,k4_xboole_0(B_19,A_18)) = k2_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_536,plain,(
    ! [A_15,C_46] : k5_xboole_0(A_15,k5_xboole_0(A_15,C_46)) = k5_xboole_0(k1_xboole_0,C_46) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_459])).

tff(c_718,plain,(
    ! [A_52,C_53] : k5_xboole_0(A_52,k5_xboole_0(A_52,C_53)) = C_53 ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_536])).

tff(c_775,plain,(
    ! [A_18,B_19] : k5_xboole_0(A_18,k2_xboole_0(A_18,B_19)) = k4_xboole_0(B_19,A_18) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_718])).

tff(c_1692,plain,(
    ! [A_71,B_72] : k4_xboole_0(k3_xboole_0(A_71,B_72),A_71) = k5_xboole_0(A_71,A_71) ),
    inference(superposition,[status(thm),theory(equality)],[c_1686,c_775])).

tff(c_1771,plain,(
    ! [A_75,B_76] : k4_xboole_0(k3_xboole_0(A_75,B_76),A_75) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1692])).

tff(c_1783,plain,(
    ! [A_75,B_76] : k2_xboole_0(k1_xboole_0,k4_xboole_0(A_75,k3_xboole_0(A_75,B_76))) = k5_xboole_0(k3_xboole_0(A_75,B_76),A_75) ),
    inference(superposition,[status(thm),theory(equality)],[c_1771,c_4])).

tff(c_1820,plain,(
    ! [A_75,B_76] : k5_xboole_0(A_75,k3_xboole_0(A_75,B_76)) = k4_xboole_0(A_75,B_76) ),
    inference(demodulation,[status(thm),theory(equality)],[c_424,c_8,c_2,c_1783])).

tff(c_22,plain,(
    k5_xboole_0('#skF_1',k3_xboole_0('#skF_1','#skF_2')) != k4_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_5015,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1820,c_22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:32:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.42/1.85  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.42/1.85  
% 4.42/1.85  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.42/1.86  %$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 4.42/1.86  
% 4.42/1.86  %Foreground sorts:
% 4.42/1.86  
% 4.42/1.86  
% 4.42/1.86  %Background operators:
% 4.42/1.86  
% 4.42/1.86  
% 4.42/1.86  %Foreground operators:
% 4.42/1.86  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.42/1.86  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.42/1.86  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.42/1.86  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.42/1.86  tff('#skF_2', type, '#skF_2': $i).
% 4.42/1.86  tff('#skF_1', type, '#skF_1': $i).
% 4.42/1.86  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.42/1.86  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.42/1.86  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.42/1.86  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.42/1.86  
% 4.42/1.87  tff(f_45, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 4.42/1.87  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 4.42/1.87  tff(f_37, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 4.42/1.87  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 4.42/1.87  tff(f_41, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 4.42/1.87  tff(f_43, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 4.42/1.87  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_xboole_0)).
% 4.42/1.87  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.42/1.87  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 4.42/1.87  tff(f_39, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 4.42/1.87  tff(f_48, negated_conjecture, ~(![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.42/1.87  tff(c_155, plain, (![A_26, B_27]: (k5_xboole_0(A_26, k4_xboole_0(B_27, A_26))=k2_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.42/1.87  tff(c_58, plain, (![B_23, A_24]: (k5_xboole_0(B_23, A_24)=k5_xboole_0(A_24, B_23))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.42/1.87  tff(c_12, plain, (![A_11]: (k5_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.42/1.87  tff(c_74, plain, (![A_24]: (k5_xboole_0(k1_xboole_0, A_24)=A_24)), inference(superposition, [status(thm), theory('equality')], [c_58, c_12])).
% 4.42/1.87  tff(c_162, plain, (![B_27]: (k4_xboole_0(B_27, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_27))), inference(superposition, [status(thm), theory('equality')], [c_155, c_74])).
% 4.42/1.87  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.42/1.87  tff(c_16, plain, (![A_15]: (k5_xboole_0(A_15, A_15)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.42/1.87  tff(c_316, plain, (![A_39, B_40]: (k5_xboole_0(k5_xboole_0(A_39, B_40), k3_xboole_0(A_39, B_40))=k2_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.42/1.87  tff(c_364, plain, (![A_5]: (k5_xboole_0(k5_xboole_0(A_5, A_5), A_5)=k2_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_316])).
% 4.42/1.87  tff(c_372, plain, (![A_41]: (k2_xboole_0(A_41, A_41)=A_41)), inference(demodulation, [status(thm), theory('equality')], [c_74, c_16, c_364])).
% 4.42/1.87  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(k4_xboole_0(A_3, B_4), k4_xboole_0(B_4, A_3))=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.42/1.87  tff(c_379, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k4_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_372, c_4])).
% 4.42/1.87  tff(c_392, plain, (![A_42]: (k4_xboole_0(A_42, A_42)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_379])).
% 4.42/1.87  tff(c_10, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k4_xboole_0(A_9, B_10))=k3_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.42/1.87  tff(c_406, plain, (![A_42]: (k4_xboole_0(A_42, k1_xboole_0)=k3_xboole_0(A_42, A_42))), inference(superposition, [status(thm), theory('equality')], [c_392, c_10])).
% 4.42/1.87  tff(c_424, plain, (![A_42]: (k2_xboole_0(k1_xboole_0, A_42)=A_42)), inference(demodulation, [status(thm), theory('equality')], [c_162, c_6, c_406])).
% 4.42/1.87  tff(c_8, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.42/1.87  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.42/1.87  tff(c_202, plain, (![A_31, B_32]: (k4_xboole_0(A_31, k4_xboole_0(A_31, B_32))=k3_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.42/1.87  tff(c_220, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k4_xboole_0(A_7, B_8))=k3_xboole_0(A_7, k3_xboole_0(A_7, B_8)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_202])).
% 4.42/1.87  tff(c_228, plain, (![A_7, B_8]: (k3_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k3_xboole_0(A_7, B_8))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_220])).
% 4.42/1.87  tff(c_18, plain, (![A_16, B_17]: (k5_xboole_0(k5_xboole_0(A_16, B_17), k3_xboole_0(A_16, B_17))=k2_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.42/1.87  tff(c_459, plain, (![A_44, B_45, C_46]: (k5_xboole_0(k5_xboole_0(A_44, B_45), C_46)=k5_xboole_0(A_44, k5_xboole_0(B_45, C_46)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.42/1.87  tff(c_1585, plain, (![A_69, B_70]: (k5_xboole_0(A_69, k5_xboole_0(B_70, k3_xboole_0(A_69, B_70)))=k2_xboole_0(A_69, B_70))), inference(superposition, [status(thm), theory('equality')], [c_18, c_459])).
% 4.42/1.87  tff(c_1657, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k5_xboole_0(k3_xboole_0(A_7, B_8), k3_xboole_0(A_7, B_8)))=k2_xboole_0(A_7, k3_xboole_0(A_7, B_8)))), inference(superposition, [status(thm), theory('equality')], [c_228, c_1585])).
% 4.42/1.87  tff(c_1686, plain, (![A_71, B_72]: (k2_xboole_0(A_71, k3_xboole_0(A_71, B_72))=A_71)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_16, c_1657])).
% 4.42/1.87  tff(c_20, plain, (![A_18, B_19]: (k5_xboole_0(A_18, k4_xboole_0(B_19, A_18))=k2_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.42/1.87  tff(c_536, plain, (![A_15, C_46]: (k5_xboole_0(A_15, k5_xboole_0(A_15, C_46))=k5_xboole_0(k1_xboole_0, C_46))), inference(superposition, [status(thm), theory('equality')], [c_16, c_459])).
% 4.42/1.87  tff(c_718, plain, (![A_52, C_53]: (k5_xboole_0(A_52, k5_xboole_0(A_52, C_53))=C_53)), inference(demodulation, [status(thm), theory('equality')], [c_74, c_536])).
% 4.42/1.87  tff(c_775, plain, (![A_18, B_19]: (k5_xboole_0(A_18, k2_xboole_0(A_18, B_19))=k4_xboole_0(B_19, A_18))), inference(superposition, [status(thm), theory('equality')], [c_20, c_718])).
% 4.42/1.87  tff(c_1692, plain, (![A_71, B_72]: (k4_xboole_0(k3_xboole_0(A_71, B_72), A_71)=k5_xboole_0(A_71, A_71))), inference(superposition, [status(thm), theory('equality')], [c_1686, c_775])).
% 4.42/1.87  tff(c_1771, plain, (![A_75, B_76]: (k4_xboole_0(k3_xboole_0(A_75, B_76), A_75)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_1692])).
% 4.42/1.87  tff(c_1783, plain, (![A_75, B_76]: (k2_xboole_0(k1_xboole_0, k4_xboole_0(A_75, k3_xboole_0(A_75, B_76)))=k5_xboole_0(k3_xboole_0(A_75, B_76), A_75))), inference(superposition, [status(thm), theory('equality')], [c_1771, c_4])).
% 4.42/1.87  tff(c_1820, plain, (![A_75, B_76]: (k5_xboole_0(A_75, k3_xboole_0(A_75, B_76))=k4_xboole_0(A_75, B_76))), inference(demodulation, [status(thm), theory('equality')], [c_424, c_8, c_2, c_1783])).
% 4.42/1.87  tff(c_22, plain, (k5_xboole_0('#skF_1', k3_xboole_0('#skF_1', '#skF_2'))!=k4_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.42/1.87  tff(c_5015, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1820, c_22])).
% 4.42/1.87  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.42/1.87  
% 4.42/1.87  Inference rules
% 4.42/1.87  ----------------------
% 4.42/1.87  #Ref     : 0
% 4.42/1.87  #Sup     : 1259
% 4.42/1.87  #Fact    : 0
% 4.42/1.87  #Define  : 0
% 4.42/1.87  #Split   : 0
% 4.42/1.87  #Chain   : 0
% 4.42/1.87  #Close   : 0
% 4.42/1.87  
% 4.42/1.87  Ordering : KBO
% 4.42/1.87  
% 4.42/1.87  Simplification rules
% 4.42/1.87  ----------------------
% 4.42/1.87  #Subsume      : 33
% 4.42/1.87  #Demod        : 1243
% 4.42/1.87  #Tautology    : 757
% 4.42/1.87  #SimpNegUnit  : 0
% 4.42/1.87  #BackRed      : 6
% 4.42/1.87  
% 4.42/1.87  #Partial instantiations: 0
% 4.42/1.87  #Strategies tried      : 1
% 4.42/1.87  
% 4.42/1.87  Timing (in seconds)
% 4.42/1.87  ----------------------
% 4.42/1.87  Preprocessing        : 0.26
% 4.42/1.87  Parsing              : 0.14
% 4.42/1.87  CNF conversion       : 0.01
% 4.42/1.87  Main loop            : 0.84
% 4.42/1.87  Inferencing          : 0.25
% 4.42/1.87  Reduction            : 0.42
% 4.42/1.87  Demodulation         : 0.36
% 4.42/1.87  BG Simplification    : 0.03
% 4.42/1.87  Subsumption          : 0.10
% 4.42/1.87  Abstraction          : 0.05
% 4.42/1.87  MUC search           : 0.00
% 4.42/1.87  Cooper               : 0.00
% 4.42/1.87  Total                : 1.13
% 4.42/1.87  Index Insertion      : 0.00
% 4.42/1.87  Index Deletion       : 0.00
% 4.42/1.87  Index Matching       : 0.00
% 4.42/1.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
