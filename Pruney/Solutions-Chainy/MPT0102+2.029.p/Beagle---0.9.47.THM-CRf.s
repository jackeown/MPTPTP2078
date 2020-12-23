%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:44 EST 2020

% Result     : Theorem 5.01s
% Output     : CNFRefutation 5.01s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 159 expanded)
%              Number of leaves         :   21 (  62 expanded)
%              Depth                    :   16
%              Number of atoms          :   48 ( 149 expanded)
%              Number of equality atoms :   47 ( 148 expanded)
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

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_31,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_35,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_45,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_48,negated_conjecture,(
    ~ ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

tff(c_16,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k4_xboole_0(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_6,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_18,plain,(
    ! [A_16,B_17] : k2_xboole_0(k3_xboole_0(A_16,B_17),k4_xboole_0(A_16,B_17)) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_8,plain,(
    ! [A_6,B_7] : k2_xboole_0(A_6,k4_xboole_0(B_7,A_6)) = k2_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_14,plain,(
    ! [A_11,B_12,C_13] : k4_xboole_0(k4_xboole_0(A_11,B_12),C_13) = k4_xboole_0(A_11,k2_xboole_0(B_12,C_13)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_42,plain,(
    ! [B_23,A_24] : k2_xboole_0(B_23,A_24) = k2_xboole_0(A_24,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_58,plain,(
    ! [A_24] : k2_xboole_0(k1_xboole_0,A_24) = A_24 ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_6])).

tff(c_10,plain,(
    ! [A_8] : k4_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_316,plain,(
    ! [A_35,B_36] : k4_xboole_0(A_35,k4_xboole_0(A_35,B_36)) = k3_xboole_0(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_346,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = k3_xboole_0(A_8,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_316])).

tff(c_232,plain,(
    ! [A_32,B_33] : k4_xboole_0(k2_xboole_0(A_32,B_33),B_33) = k4_xboole_0(A_32,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_263,plain,(
    ! [A_24] : k4_xboole_0(k1_xboole_0,A_24) = k4_xboole_0(A_24,A_24) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_232])).

tff(c_350,plain,(
    ! [A_24] : k4_xboole_0(k1_xboole_0,A_24) = k3_xboole_0(A_24,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_346,c_263])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_241,plain,(
    ! [B_33,A_32] : k2_xboole_0(B_33,k4_xboole_0(A_32,B_33)) = k2_xboole_0(B_33,k2_xboole_0(A_32,B_33)) ),
    inference(superposition,[status(thm),theory(equality)],[c_232,c_8])).

tff(c_554,plain,(
    ! [B_45,A_46] : k2_xboole_0(B_45,k2_xboole_0(A_46,B_45)) = k2_xboole_0(B_45,A_46) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_241])).

tff(c_623,plain,(
    ! [B_47,A_48] : k2_xboole_0(B_47,k2_xboole_0(B_47,A_48)) = k2_xboole_0(B_47,A_48) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_554])).

tff(c_671,plain,(
    ! [A_16,B_17] : k2_xboole_0(k3_xboole_0(A_16,B_17),k4_xboole_0(A_16,B_17)) = k2_xboole_0(k3_xboole_0(A_16,B_17),A_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_623])).

tff(c_791,plain,(
    ! [A_52,B_53] : k2_xboole_0(A_52,k3_xboole_0(A_52,B_53)) = A_52 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_2,c_671])).

tff(c_829,plain,(
    ! [B_54] : k3_xboole_0(k1_xboole_0,B_54) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_791,c_58])).

tff(c_841,plain,(
    ! [B_54] : k2_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,B_54)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_829,c_18])).

tff(c_847,plain,(
    ! [B_54] : k3_xboole_0(B_54,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_350,c_841])).

tff(c_1029,plain,(
    ! [A_60] : k4_xboole_0(A_60,A_60) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_847,c_346])).

tff(c_1069,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k2_xboole_0(B_12,k4_xboole_0(A_11,B_12))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1029])).

tff(c_1389,plain,(
    ! [A_68,B_69] : k4_xboole_0(A_68,k2_xboole_0(B_69,A_68)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1069])).

tff(c_1934,plain,(
    ! [A_82,B_83] : k4_xboole_0(k4_xboole_0(A_82,B_83),A_82) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_1389])).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(k4_xboole_0(A_3,B_4),k4_xboole_0(B_4,A_3)) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1951,plain,(
    ! [A_82,B_83] : k2_xboole_0(k4_xboole_0(A_82,k4_xboole_0(A_82,B_83)),k1_xboole_0) = k5_xboole_0(A_82,k4_xboole_0(A_82,B_83)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1934,c_4])).

tff(c_2022,plain,(
    ! [A_82,B_83] : k5_xboole_0(A_82,k4_xboole_0(A_82,B_83)) = k3_xboole_0(A_82,B_83) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_6,c_1951])).

tff(c_12,plain,(
    ! [A_9,B_10] : k4_xboole_0(k2_xboole_0(A_9,B_10),B_10) = k4_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1400,plain,(
    ! [B_69,A_68] : k2_xboole_0(k1_xboole_0,k4_xboole_0(k2_xboole_0(B_69,A_68),A_68)) = k5_xboole_0(A_68,k2_xboole_0(B_69,A_68)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1389,c_4])).

tff(c_1471,plain,(
    ! [A_68,B_69] : k5_xboole_0(A_68,k2_xboole_0(B_69,A_68)) = k4_xboole_0(B_69,A_68) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_58,c_1400])).

tff(c_20,plain,(
    ! [A_18,B_19,C_20] : k5_xboole_0(k5_xboole_0(A_18,B_19),C_20) = k5_xboole_0(A_18,k5_xboole_0(B_19,C_20)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_22,plain,(
    k5_xboole_0(k5_xboole_0('#skF_1','#skF_2'),k2_xboole_0('#skF_1','#skF_2')) != k3_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_23,plain,(
    k5_xboole_0('#skF_1',k5_xboole_0('#skF_2',k2_xboole_0('#skF_1','#skF_2'))) != k3_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_22])).

tff(c_3134,plain,(
    k5_xboole_0('#skF_1',k4_xboole_0('#skF_1','#skF_2')) != k3_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1471,c_23])).

tff(c_7284,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2022,c_3134])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:08:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.01/1.96  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.01/1.96  
% 5.01/1.96  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.01/1.97  %$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 5.01/1.97  
% 5.01/1.97  %Foreground sorts:
% 5.01/1.97  
% 5.01/1.97  
% 5.01/1.97  %Background operators:
% 5.01/1.97  
% 5.01/1.97  
% 5.01/1.97  %Foreground operators:
% 5.01/1.97  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.01/1.97  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.01/1.97  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.01/1.97  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.01/1.97  tff('#skF_2', type, '#skF_2': $i).
% 5.01/1.97  tff('#skF_1', type, '#skF_1': $i).
% 5.01/1.97  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.01/1.97  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.01/1.97  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.01/1.97  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.01/1.97  
% 5.01/1.98  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.01/1.98  tff(f_31, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 5.01/1.98  tff(f_43, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 5.01/1.98  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 5.01/1.98  tff(f_39, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 5.01/1.98  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 5.01/1.98  tff(f_35, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 5.01/1.98  tff(f_37, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 5.01/1.98  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_xboole_0)).
% 5.01/1.98  tff(f_45, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 5.01/1.98  tff(f_48, negated_conjecture, ~(![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 5.01/1.98  tff(c_16, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k4_xboole_0(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.01/1.98  tff(c_6, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.01/1.98  tff(c_18, plain, (![A_16, B_17]: (k2_xboole_0(k3_xboole_0(A_16, B_17), k4_xboole_0(A_16, B_17))=A_16)), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.01/1.98  tff(c_8, plain, (![A_6, B_7]: (k2_xboole_0(A_6, k4_xboole_0(B_7, A_6))=k2_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.01/1.98  tff(c_14, plain, (![A_11, B_12, C_13]: (k4_xboole_0(k4_xboole_0(A_11, B_12), C_13)=k4_xboole_0(A_11, k2_xboole_0(B_12, C_13)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.01/1.98  tff(c_42, plain, (![B_23, A_24]: (k2_xboole_0(B_23, A_24)=k2_xboole_0(A_24, B_23))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.01/1.98  tff(c_58, plain, (![A_24]: (k2_xboole_0(k1_xboole_0, A_24)=A_24)), inference(superposition, [status(thm), theory('equality')], [c_42, c_6])).
% 5.01/1.98  tff(c_10, plain, (![A_8]: (k4_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.01/1.98  tff(c_316, plain, (![A_35, B_36]: (k4_xboole_0(A_35, k4_xboole_0(A_35, B_36))=k3_xboole_0(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.01/1.98  tff(c_346, plain, (![A_8]: (k4_xboole_0(A_8, A_8)=k3_xboole_0(A_8, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_316])).
% 5.01/1.98  tff(c_232, plain, (![A_32, B_33]: (k4_xboole_0(k2_xboole_0(A_32, B_33), B_33)=k4_xboole_0(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.01/1.98  tff(c_263, plain, (![A_24]: (k4_xboole_0(k1_xboole_0, A_24)=k4_xboole_0(A_24, A_24))), inference(superposition, [status(thm), theory('equality')], [c_58, c_232])).
% 5.01/1.98  tff(c_350, plain, (![A_24]: (k4_xboole_0(k1_xboole_0, A_24)=k3_xboole_0(A_24, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_346, c_263])).
% 5.01/1.98  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.01/1.98  tff(c_241, plain, (![B_33, A_32]: (k2_xboole_0(B_33, k4_xboole_0(A_32, B_33))=k2_xboole_0(B_33, k2_xboole_0(A_32, B_33)))), inference(superposition, [status(thm), theory('equality')], [c_232, c_8])).
% 5.01/1.98  tff(c_554, plain, (![B_45, A_46]: (k2_xboole_0(B_45, k2_xboole_0(A_46, B_45))=k2_xboole_0(B_45, A_46))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_241])).
% 5.01/1.98  tff(c_623, plain, (![B_47, A_48]: (k2_xboole_0(B_47, k2_xboole_0(B_47, A_48))=k2_xboole_0(B_47, A_48))), inference(superposition, [status(thm), theory('equality')], [c_2, c_554])).
% 5.01/1.98  tff(c_671, plain, (![A_16, B_17]: (k2_xboole_0(k3_xboole_0(A_16, B_17), k4_xboole_0(A_16, B_17))=k2_xboole_0(k3_xboole_0(A_16, B_17), A_16))), inference(superposition, [status(thm), theory('equality')], [c_18, c_623])).
% 5.01/1.98  tff(c_791, plain, (![A_52, B_53]: (k2_xboole_0(A_52, k3_xboole_0(A_52, B_53))=A_52)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_2, c_671])).
% 5.01/1.98  tff(c_829, plain, (![B_54]: (k3_xboole_0(k1_xboole_0, B_54)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_791, c_58])).
% 5.01/1.98  tff(c_841, plain, (![B_54]: (k2_xboole_0(k1_xboole_0, k4_xboole_0(k1_xboole_0, B_54))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_829, c_18])).
% 5.01/1.98  tff(c_847, plain, (![B_54]: (k3_xboole_0(B_54, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_58, c_350, c_841])).
% 5.01/1.98  tff(c_1029, plain, (![A_60]: (k4_xboole_0(A_60, A_60)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_847, c_346])).
% 5.01/1.98  tff(c_1069, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k2_xboole_0(B_12, k4_xboole_0(A_11, B_12)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14, c_1029])).
% 5.01/1.98  tff(c_1389, plain, (![A_68, B_69]: (k4_xboole_0(A_68, k2_xboole_0(B_69, A_68))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_1069])).
% 5.01/1.98  tff(c_1934, plain, (![A_82, B_83]: (k4_xboole_0(k4_xboole_0(A_82, B_83), A_82)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_18, c_1389])).
% 5.01/1.98  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(k4_xboole_0(A_3, B_4), k4_xboole_0(B_4, A_3))=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.01/1.98  tff(c_1951, plain, (![A_82, B_83]: (k2_xboole_0(k4_xboole_0(A_82, k4_xboole_0(A_82, B_83)), k1_xboole_0)=k5_xboole_0(A_82, k4_xboole_0(A_82, B_83)))), inference(superposition, [status(thm), theory('equality')], [c_1934, c_4])).
% 5.01/1.98  tff(c_2022, plain, (![A_82, B_83]: (k5_xboole_0(A_82, k4_xboole_0(A_82, B_83))=k3_xboole_0(A_82, B_83))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_6, c_1951])).
% 5.01/1.98  tff(c_12, plain, (![A_9, B_10]: (k4_xboole_0(k2_xboole_0(A_9, B_10), B_10)=k4_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.01/1.98  tff(c_1400, plain, (![B_69, A_68]: (k2_xboole_0(k1_xboole_0, k4_xboole_0(k2_xboole_0(B_69, A_68), A_68))=k5_xboole_0(A_68, k2_xboole_0(B_69, A_68)))), inference(superposition, [status(thm), theory('equality')], [c_1389, c_4])).
% 5.01/1.98  tff(c_1471, plain, (![A_68, B_69]: (k5_xboole_0(A_68, k2_xboole_0(B_69, A_68))=k4_xboole_0(B_69, A_68))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_58, c_1400])).
% 5.01/1.98  tff(c_20, plain, (![A_18, B_19, C_20]: (k5_xboole_0(k5_xboole_0(A_18, B_19), C_20)=k5_xboole_0(A_18, k5_xboole_0(B_19, C_20)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.01/1.98  tff(c_22, plain, (k5_xboole_0(k5_xboole_0('#skF_1', '#skF_2'), k2_xboole_0('#skF_1', '#skF_2'))!=k3_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.01/1.98  tff(c_23, plain, (k5_xboole_0('#skF_1', k5_xboole_0('#skF_2', k2_xboole_0('#skF_1', '#skF_2')))!=k3_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_22])).
% 5.01/1.98  tff(c_3134, plain, (k5_xboole_0('#skF_1', k4_xboole_0('#skF_1', '#skF_2'))!=k3_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1471, c_23])).
% 5.01/1.98  tff(c_7284, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2022, c_3134])).
% 5.01/1.98  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.01/1.98  
% 5.01/1.98  Inference rules
% 5.01/1.98  ----------------------
% 5.01/1.98  #Ref     : 0
% 5.01/1.98  #Sup     : 1826
% 5.01/1.98  #Fact    : 0
% 5.01/1.98  #Define  : 0
% 5.01/1.98  #Split   : 0
% 5.01/1.98  #Chain   : 0
% 5.01/1.98  #Close   : 0
% 5.01/1.98  
% 5.01/1.98  Ordering : KBO
% 5.01/1.98  
% 5.01/1.98  Simplification rules
% 5.01/1.98  ----------------------
% 5.01/1.98  #Subsume      : 9
% 5.01/1.98  #Demod        : 2154
% 5.01/1.98  #Tautology    : 1262
% 5.01/1.98  #SimpNegUnit  : 0
% 5.01/1.98  #BackRed      : 6
% 5.01/1.98  
% 5.01/1.98  #Partial instantiations: 0
% 5.01/1.98  #Strategies tried      : 1
% 5.01/1.98  
% 5.01/1.98  Timing (in seconds)
% 5.01/1.98  ----------------------
% 5.01/1.98  Preprocessing        : 0.26
% 5.01/1.98  Parsing              : 0.15
% 5.01/1.98  CNF conversion       : 0.01
% 5.01/1.98  Main loop            : 0.97
% 5.01/1.98  Inferencing          : 0.27
% 5.01/1.98  Reduction            : 0.49
% 5.01/1.98  Demodulation         : 0.41
% 5.01/1.98  BG Simplification    : 0.03
% 5.01/1.98  Subsumption          : 0.12
% 5.01/1.98  Abstraction          : 0.05
% 5.01/1.98  MUC search           : 0.00
% 5.01/1.98  Cooper               : 0.00
% 5.01/1.98  Total                : 1.26
% 5.01/1.98  Index Insertion      : 0.00
% 5.01/1.98  Index Deletion       : 0.00
% 5.01/1.98  Index Matching       : 0.00
% 5.01/1.98  BG Taut test         : 0.00
%------------------------------------------------------------------------------
