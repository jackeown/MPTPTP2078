%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:00 EST 2020

% Result     : Theorem 8.55s
% Output     : CNFRefutation 8.55s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 142 expanded)
%              Number of leaves         :   19 (  56 expanded)
%              Depth                    :   15
%              Number of atoms          :   47 ( 132 expanded)
%              Number of equality atoms :   46 ( 131 expanded)
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

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_29,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_31,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_39,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_44,negated_conjecture,(
    ~ ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_10,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k3_xboole_0(A_9,B_10)) = k4_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_87,plain,(
    ! [A_23,B_24] : k4_xboole_0(A_23,k4_xboole_0(A_23,B_24)) = k3_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_12,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k4_xboole_0(A_11,B_12)) = k3_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_90,plain,(
    ! [A_23,B_24] : k4_xboole_0(A_23,k3_xboole_0(A_23,B_24)) = k3_xboole_0(A_23,k4_xboole_0(A_23,B_24)) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_12])).

tff(c_1242,plain,(
    ! [A_23,B_24] : k3_xboole_0(A_23,k4_xboole_0(A_23,B_24)) = k4_xboole_0(A_23,B_24) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_90])).

tff(c_8,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k2_xboole_0(A_7,B_8)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4,plain,(
    ! [A_3] : k4_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_108,plain,(
    ! [A_3] : k4_xboole_0(A_3,A_3) = k3_xboole_0(A_3,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_87])).

tff(c_105,plain,(
    ! [A_7,B_8] : k3_xboole_0(A_7,k2_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_87])).

tff(c_111,plain,(
    ! [A_7,B_8] : k3_xboole_0(A_7,k2_xboole_0(A_7,B_8)) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_105])).

tff(c_162,plain,(
    ! [A_28,B_29] : k4_xboole_0(A_28,k3_xboole_0(A_28,B_29)) = k4_xboole_0(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_180,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k2_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_162])).

tff(c_185,plain,(
    ! [A_7] : k3_xboole_0(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_8,c_180])).

tff(c_186,plain,(
    ! [A_3] : k4_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_108])).

tff(c_224,plain,(
    ! [A_32,B_33,C_34] : k4_xboole_0(k4_xboole_0(A_32,B_33),C_34) = k4_xboole_0(A_32,k2_xboole_0(B_33,C_34)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_265,plain,(
    ! [A_3,C_34] : k4_xboole_0(A_3,k2_xboole_0(A_3,C_34)) = k4_xboole_0(k1_xboole_0,C_34) ),
    inference(superposition,[status(thm),theory(equality)],[c_186,c_224])).

tff(c_304,plain,(
    ! [C_34] : k4_xboole_0(k1_xboole_0,C_34) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_265])).

tff(c_14,plain,(
    ! [A_13] : k5_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_412,plain,(
    ! [A_38,B_39] : k2_xboole_0(k4_xboole_0(A_38,B_39),k4_xboole_0(B_39,A_38)) = k5_xboole_0(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_471,plain,(
    ! [A_3] : k2_xboole_0(A_3,k4_xboole_0(k1_xboole_0,A_3)) = k5_xboole_0(A_3,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_412])).

tff(c_485,plain,(
    ! [A_3] : k2_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(demodulation,[status(thm),theory(equality)],[c_304,c_14,c_471])).

tff(c_16,plain,(
    ! [A_14,B_15] : k5_xboole_0(A_14,k4_xboole_0(B_15,A_14)) = k2_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_199,plain,(
    ! [A_31] : k4_xboole_0(A_31,A_31) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_108])).

tff(c_207,plain,(
    ! [A_31] : k5_xboole_0(A_31,k1_xboole_0) = k2_xboole_0(A_31,A_31) ),
    inference(superposition,[status(thm),theory(equality)],[c_199,c_16])).

tff(c_220,plain,(
    ! [A_31] : k2_xboole_0(A_31,A_31) = A_31 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_207])).

tff(c_10343,plain,(
    ! [C_167,A_168,B_169] : k5_xboole_0(C_167,k4_xboole_0(A_168,k2_xboole_0(B_169,C_167))) = k2_xboole_0(C_167,k4_xboole_0(A_168,B_169)) ),
    inference(superposition,[status(thm),theory(equality)],[c_224,c_16])).

tff(c_10504,plain,(
    ! [A_31,A_168] : k5_xboole_0(A_31,k4_xboole_0(A_168,A_31)) = k2_xboole_0(A_31,k4_xboole_0(A_168,A_31)) ),
    inference(superposition,[status(thm),theory(equality)],[c_220,c_10343])).

tff(c_10555,plain,(
    ! [A_31,A_168] : k2_xboole_0(A_31,k4_xboole_0(A_168,A_31)) = k2_xboole_0(A_31,A_168) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_10504])).

tff(c_234,plain,(
    ! [A_32,B_33] : k4_xboole_0(A_32,k2_xboole_0(B_33,k4_xboole_0(A_32,B_33))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_224,c_186])).

tff(c_10911,plain,(
    ! [A_32,B_33] : k4_xboole_0(A_32,k2_xboole_0(B_33,A_32)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10555,c_234])).

tff(c_6,plain,(
    ! [A_4,B_5,C_6] : k4_xboole_0(k4_xboole_0(A_4,B_5),C_6) = k4_xboole_0(A_4,k2_xboole_0(B_5,C_6)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_459,plain,(
    ! [A_11,B_12] : k2_xboole_0(k3_xboole_0(A_11,B_12),k4_xboole_0(k4_xboole_0(A_11,B_12),A_11)) = k5_xboole_0(A_11,k4_xboole_0(A_11,B_12)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_412])).

tff(c_483,plain,(
    ! [A_11,B_12] : k2_xboole_0(k3_xboole_0(A_11,B_12),k4_xboole_0(A_11,k2_xboole_0(B_12,A_11))) = k5_xboole_0(A_11,k4_xboole_0(A_11,B_12)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_459])).

tff(c_21844,plain,(
    ! [A_250,B_251] : k5_xboole_0(A_250,k4_xboole_0(A_250,B_251)) = k3_xboole_0(A_250,B_251) ),
    inference(demodulation,[status(thm),theory(equality)],[c_485,c_10911,c_483])).

tff(c_22043,plain,(
    ! [A_11,B_12] : k5_xboole_0(A_11,k3_xboole_0(A_11,B_12)) = k3_xboole_0(A_11,k4_xboole_0(A_11,B_12)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_21844])).

tff(c_22112,plain,(
    ! [A_11,B_12] : k5_xboole_0(A_11,k3_xboole_0(A_11,B_12)) = k4_xboole_0(A_11,B_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1242,c_22043])).

tff(c_18,plain,(
    k5_xboole_0('#skF_1',k3_xboole_0('#skF_1','#skF_2')) != k4_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_22123,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22112,c_18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:15:36 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.55/3.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.55/3.44  
% 8.55/3.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.55/3.45  %$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 8.55/3.45  
% 8.55/3.45  %Foreground sorts:
% 8.55/3.45  
% 8.55/3.45  
% 8.55/3.45  %Background operators:
% 8.55/3.45  
% 8.55/3.45  
% 8.55/3.45  %Foreground operators:
% 8.55/3.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.55/3.45  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.55/3.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.55/3.45  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.55/3.45  tff('#skF_2', type, '#skF_2': $i).
% 8.55/3.45  tff('#skF_1', type, '#skF_1': $i).
% 8.55/3.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.55/3.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.55/3.45  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.55/3.45  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.55/3.45  
% 8.55/3.46  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 8.55/3.46  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 8.55/3.46  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 8.55/3.46  tff(f_29, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 8.55/3.46  tff(f_31, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 8.55/3.46  tff(f_39, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 8.55/3.46  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_xboole_0)).
% 8.55/3.46  tff(f_41, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 8.55/3.46  tff(f_44, negated_conjecture, ~(![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 8.55/3.46  tff(c_10, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k3_xboole_0(A_9, B_10))=k4_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.55/3.46  tff(c_87, plain, (![A_23, B_24]: (k4_xboole_0(A_23, k4_xboole_0(A_23, B_24))=k3_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.55/3.46  tff(c_12, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k4_xboole_0(A_11, B_12))=k3_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.55/3.46  tff(c_90, plain, (![A_23, B_24]: (k4_xboole_0(A_23, k3_xboole_0(A_23, B_24))=k3_xboole_0(A_23, k4_xboole_0(A_23, B_24)))), inference(superposition, [status(thm), theory('equality')], [c_87, c_12])).
% 8.55/3.46  tff(c_1242, plain, (![A_23, B_24]: (k3_xboole_0(A_23, k4_xboole_0(A_23, B_24))=k4_xboole_0(A_23, B_24))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_90])).
% 8.55/3.46  tff(c_8, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k2_xboole_0(A_7, B_8))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.55/3.46  tff(c_4, plain, (![A_3]: (k4_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.55/3.46  tff(c_108, plain, (![A_3]: (k4_xboole_0(A_3, A_3)=k3_xboole_0(A_3, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_87])).
% 8.55/3.46  tff(c_105, plain, (![A_7, B_8]: (k3_xboole_0(A_7, k2_xboole_0(A_7, B_8))=k4_xboole_0(A_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_87])).
% 8.55/3.46  tff(c_111, plain, (![A_7, B_8]: (k3_xboole_0(A_7, k2_xboole_0(A_7, B_8))=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_105])).
% 8.55/3.46  tff(c_162, plain, (![A_28, B_29]: (k4_xboole_0(A_28, k3_xboole_0(A_28, B_29))=k4_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.55/3.46  tff(c_180, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k2_xboole_0(A_7, B_8))=k4_xboole_0(A_7, A_7))), inference(superposition, [status(thm), theory('equality')], [c_111, c_162])).
% 8.55/3.46  tff(c_185, plain, (![A_7]: (k3_xboole_0(A_7, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_108, c_8, c_180])).
% 8.55/3.46  tff(c_186, plain, (![A_3]: (k4_xboole_0(A_3, A_3)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_185, c_108])).
% 8.55/3.46  tff(c_224, plain, (![A_32, B_33, C_34]: (k4_xboole_0(k4_xboole_0(A_32, B_33), C_34)=k4_xboole_0(A_32, k2_xboole_0(B_33, C_34)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.55/3.46  tff(c_265, plain, (![A_3, C_34]: (k4_xboole_0(A_3, k2_xboole_0(A_3, C_34))=k4_xboole_0(k1_xboole_0, C_34))), inference(superposition, [status(thm), theory('equality')], [c_186, c_224])).
% 8.55/3.46  tff(c_304, plain, (![C_34]: (k4_xboole_0(k1_xboole_0, C_34)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_265])).
% 8.55/3.46  tff(c_14, plain, (![A_13]: (k5_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.55/3.46  tff(c_412, plain, (![A_38, B_39]: (k2_xboole_0(k4_xboole_0(A_38, B_39), k4_xboole_0(B_39, A_38))=k5_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.55/3.46  tff(c_471, plain, (![A_3]: (k2_xboole_0(A_3, k4_xboole_0(k1_xboole_0, A_3))=k5_xboole_0(A_3, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_412])).
% 8.55/3.46  tff(c_485, plain, (![A_3]: (k2_xboole_0(A_3, k1_xboole_0)=A_3)), inference(demodulation, [status(thm), theory('equality')], [c_304, c_14, c_471])).
% 8.55/3.46  tff(c_16, plain, (![A_14, B_15]: (k5_xboole_0(A_14, k4_xboole_0(B_15, A_14))=k2_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.55/3.46  tff(c_199, plain, (![A_31]: (k4_xboole_0(A_31, A_31)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_185, c_108])).
% 8.55/3.46  tff(c_207, plain, (![A_31]: (k5_xboole_0(A_31, k1_xboole_0)=k2_xboole_0(A_31, A_31))), inference(superposition, [status(thm), theory('equality')], [c_199, c_16])).
% 8.55/3.46  tff(c_220, plain, (![A_31]: (k2_xboole_0(A_31, A_31)=A_31)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_207])).
% 8.55/3.46  tff(c_10343, plain, (![C_167, A_168, B_169]: (k5_xboole_0(C_167, k4_xboole_0(A_168, k2_xboole_0(B_169, C_167)))=k2_xboole_0(C_167, k4_xboole_0(A_168, B_169)))), inference(superposition, [status(thm), theory('equality')], [c_224, c_16])).
% 8.55/3.46  tff(c_10504, plain, (![A_31, A_168]: (k5_xboole_0(A_31, k4_xboole_0(A_168, A_31))=k2_xboole_0(A_31, k4_xboole_0(A_168, A_31)))), inference(superposition, [status(thm), theory('equality')], [c_220, c_10343])).
% 8.55/3.46  tff(c_10555, plain, (![A_31, A_168]: (k2_xboole_0(A_31, k4_xboole_0(A_168, A_31))=k2_xboole_0(A_31, A_168))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_10504])).
% 8.55/3.46  tff(c_234, plain, (![A_32, B_33]: (k4_xboole_0(A_32, k2_xboole_0(B_33, k4_xboole_0(A_32, B_33)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_224, c_186])).
% 8.55/3.46  tff(c_10911, plain, (![A_32, B_33]: (k4_xboole_0(A_32, k2_xboole_0(B_33, A_32))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10555, c_234])).
% 8.55/3.46  tff(c_6, plain, (![A_4, B_5, C_6]: (k4_xboole_0(k4_xboole_0(A_4, B_5), C_6)=k4_xboole_0(A_4, k2_xboole_0(B_5, C_6)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.55/3.46  tff(c_459, plain, (![A_11, B_12]: (k2_xboole_0(k3_xboole_0(A_11, B_12), k4_xboole_0(k4_xboole_0(A_11, B_12), A_11))=k5_xboole_0(A_11, k4_xboole_0(A_11, B_12)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_412])).
% 8.55/3.46  tff(c_483, plain, (![A_11, B_12]: (k2_xboole_0(k3_xboole_0(A_11, B_12), k4_xboole_0(A_11, k2_xboole_0(B_12, A_11)))=k5_xboole_0(A_11, k4_xboole_0(A_11, B_12)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_459])).
% 8.55/3.46  tff(c_21844, plain, (![A_250, B_251]: (k5_xboole_0(A_250, k4_xboole_0(A_250, B_251))=k3_xboole_0(A_250, B_251))), inference(demodulation, [status(thm), theory('equality')], [c_485, c_10911, c_483])).
% 8.55/3.46  tff(c_22043, plain, (![A_11, B_12]: (k5_xboole_0(A_11, k3_xboole_0(A_11, B_12))=k3_xboole_0(A_11, k4_xboole_0(A_11, B_12)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_21844])).
% 8.55/3.46  tff(c_22112, plain, (![A_11, B_12]: (k5_xboole_0(A_11, k3_xboole_0(A_11, B_12))=k4_xboole_0(A_11, B_12))), inference(demodulation, [status(thm), theory('equality')], [c_1242, c_22043])).
% 8.55/3.46  tff(c_18, plain, (k5_xboole_0('#skF_1', k3_xboole_0('#skF_1', '#skF_2'))!=k4_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_44])).
% 8.55/3.46  tff(c_22123, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22112, c_18])).
% 8.55/3.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.55/3.46  
% 8.55/3.46  Inference rules
% 8.55/3.46  ----------------------
% 8.55/3.46  #Ref     : 0
% 8.55/3.46  #Sup     : 5457
% 8.55/3.46  #Fact    : 0
% 8.55/3.46  #Define  : 0
% 8.55/3.46  #Split   : 0
% 8.55/3.46  #Chain   : 0
% 8.55/3.46  #Close   : 0
% 8.55/3.46  
% 8.55/3.46  Ordering : KBO
% 8.55/3.46  
% 8.55/3.46  Simplification rules
% 8.55/3.46  ----------------------
% 8.55/3.46  #Subsume      : 0
% 8.55/3.46  #Demod        : 7122
% 8.55/3.46  #Tautology    : 3921
% 8.55/3.46  #SimpNegUnit  : 0
% 8.55/3.46  #BackRed      : 9
% 8.55/3.46  
% 8.55/3.46  #Partial instantiations: 0
% 8.55/3.46  #Strategies tried      : 1
% 8.55/3.46  
% 8.55/3.46  Timing (in seconds)
% 8.55/3.46  ----------------------
% 8.55/3.47  Preprocessing        : 0.29
% 8.55/3.47  Parsing              : 0.16
% 8.55/3.47  CNF conversion       : 0.02
% 8.55/3.47  Main loop            : 2.38
% 8.55/3.47  Inferencing          : 0.59
% 8.55/3.47  Reduction            : 1.29
% 8.55/3.47  Demodulation         : 1.13
% 8.55/3.47  BG Simplification    : 0.06
% 8.55/3.47  Subsumption          : 0.33
% 8.55/3.47  Abstraction          : 0.14
% 8.55/3.47  MUC search           : 0.00
% 8.55/3.47  Cooper               : 0.00
% 8.55/3.47  Total                : 2.70
% 8.55/3.47  Index Insertion      : 0.00
% 8.55/3.47  Index Deletion       : 0.00
% 8.55/3.47  Index Matching       : 0.00
% 8.55/3.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
