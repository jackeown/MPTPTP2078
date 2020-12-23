%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:39 EST 2020

% Result     : Theorem 29.82s
% Output     : CNFRefutation 29.82s
% Verified   : 
% Statistics : Number of formulae       :   42 (  61 expanded)
%              Number of leaves         :   17 (  28 expanded)
%              Depth                    :    7
%              Number of atoms          :   33 (  52 expanded)
%              Number of equality atoms :   32 (  51 expanded)
%              Maximal formula depth    :    4 (   3 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : k2_xboole_0(A,k2_xboole_0(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_42,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_xboole_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_79,plain,(
    ! [A_23,B_24] : k2_xboole_0(A_23,k2_xboole_0(A_23,B_24)) = k2_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_97,plain,(
    ! [A_1,B_2] : k2_xboole_0(A_1,k2_xboole_0(B_2,A_1)) = k2_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_79])).

tff(c_6,plain,(
    ! [A_5,B_6] : k2_xboole_0(A_5,k4_xboole_0(B_6,A_5)) = k2_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_188,plain,(
    ! [A_30,B_31] : k2_xboole_0(k4_xboole_0(A_30,B_31),k4_xboole_0(B_31,A_30)) = k5_xboole_0(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_224,plain,(
    ! [B_31,A_30] : k2_xboole_0(k4_xboole_0(B_31,A_30),k4_xboole_0(A_30,B_31)) = k5_xboole_0(A_30,B_31) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_188])).

tff(c_12,plain,(
    ! [A_12,B_13,C_14] : k2_xboole_0(k2_xboole_0(A_12,B_13),C_14) = k2_xboole_0(A_12,k2_xboole_0(B_13,C_14)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_231,plain,(
    ! [A_32,B_33,C_34] : k2_xboole_0(k2_xboole_0(A_32,B_33),C_34) = k2_xboole_0(A_32,k2_xboole_0(B_33,C_34)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_287,plain,(
    ! [A_5,B_6,C_34] : k2_xboole_0(A_5,k2_xboole_0(k4_xboole_0(B_6,A_5),C_34)) = k2_xboole_0(k2_xboole_0(A_5,B_6),C_34) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_231])).

tff(c_2490,plain,(
    ! [A_66,B_67,C_68] : k2_xboole_0(A_66,k2_xboole_0(k4_xboole_0(B_67,A_66),C_68)) = k2_xboole_0(A_66,k2_xboole_0(B_67,C_68)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_287])).

tff(c_2616,plain,(
    ! [A_30,B_31] : k2_xboole_0(A_30,k2_xboole_0(B_31,k4_xboole_0(A_30,B_31))) = k2_xboole_0(A_30,k5_xboole_0(A_30,B_31)) ),
    inference(superposition,[status(thm),theory(equality)],[c_224,c_2490])).

tff(c_2703,plain,(
    ! [A_30,B_31] : k2_xboole_0(A_30,k5_xboole_0(A_30,B_31)) = k2_xboole_0(A_30,B_31) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_6,c_2616])).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(k4_xboole_0(A_3,B_4),k4_xboole_0(B_4,A_3)) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_14,plain,(
    ! [A_15,B_16] : k2_xboole_0(A_15,k2_xboole_0(A_15,B_16)) = k2_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_197,plain,(
    ! [A_30,B_31] : k2_xboole_0(k4_xboole_0(A_30,B_31),k5_xboole_0(A_30,B_31)) = k2_xboole_0(k4_xboole_0(A_30,B_31),k4_xboole_0(B_31,A_30)) ),
    inference(superposition,[status(thm),theory(equality)],[c_188,c_14])).

tff(c_227,plain,(
    ! [A_30,B_31] : k2_xboole_0(k4_xboole_0(A_30,B_31),k5_xboole_0(A_30,B_31)) = k5_xboole_0(A_30,B_31) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_197])).

tff(c_10,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k4_xboole_0(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_151,plain,(
    ! [A_27,B_28,C_29] : k4_xboole_0(k4_xboole_0(A_27,B_28),C_29) = k4_xboole_0(A_27,k2_xboole_0(B_28,C_29)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_3510,plain,(
    ! [A_78,B_79,C_80] : k4_xboole_0(A_78,k2_xboole_0(k4_xboole_0(A_78,B_79),C_80)) = k4_xboole_0(k3_xboole_0(A_78,B_79),C_80) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_151])).

tff(c_65324,plain,(
    ! [A_306,B_307] : k4_xboole_0(k3_xboole_0(A_306,B_307),k5_xboole_0(A_306,B_307)) = k4_xboole_0(A_306,k5_xboole_0(A_306,B_307)) ),
    inference(superposition,[status(thm),theory(equality)],[c_227,c_3510])).

tff(c_65432,plain,(
    ! [A_306,B_307] : k2_xboole_0(k5_xboole_0(A_306,B_307),k4_xboole_0(A_306,k5_xboole_0(A_306,B_307))) = k2_xboole_0(k5_xboole_0(A_306,B_307),k3_xboole_0(A_306,B_307)) ),
    inference(superposition,[status(thm),theory(equality)],[c_65324,c_6])).

tff(c_65487,plain,(
    ! [A_306,B_307] : k2_xboole_0(k3_xboole_0(A_306,B_307),k5_xboole_0(A_306,B_307)) = k2_xboole_0(A_306,B_307) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2703,c_2,c_6,c_2,c_65432])).

tff(c_16,plain,(
    k2_xboole_0(k5_xboole_0('#skF_1','#skF_2'),k3_xboole_0('#skF_1','#skF_2')) != k2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_17,plain,(
    k2_xboole_0(k3_xboole_0('#skF_1','#skF_2'),k5_xboole_0('#skF_1','#skF_2')) != k2_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_16])).

tff(c_65496,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_65487,c_17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:39:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 29.82/20.83  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 29.82/20.84  
% 29.82/20.84  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 29.82/20.84  %$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_1
% 29.82/20.84  
% 29.82/20.84  %Foreground sorts:
% 29.82/20.84  
% 29.82/20.84  
% 29.82/20.84  %Background operators:
% 29.82/20.84  
% 29.82/20.84  
% 29.82/20.84  %Foreground operators:
% 29.82/20.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 29.82/20.84  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 29.82/20.84  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 29.82/20.84  tff('#skF_2', type, '#skF_2': $i).
% 29.82/20.84  tff('#skF_1', type, '#skF_1': $i).
% 29.82/20.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 29.82/20.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 29.82/20.84  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 29.82/20.84  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 29.82/20.84  
% 29.82/20.85  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 29.82/20.85  tff(f_39, axiom, (![A, B]: (k2_xboole_0(A, k2_xboole_0(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_xboole_1)).
% 29.82/20.85  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 29.82/20.85  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_xboole_0)).
% 29.82/20.85  tff(f_37, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 29.82/20.85  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 29.82/20.85  tff(f_33, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 29.82/20.85  tff(f_42, negated_conjecture, ~(![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t93_xboole_1)).
% 29.82/20.85  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 29.82/20.85  tff(c_79, plain, (![A_23, B_24]: (k2_xboole_0(A_23, k2_xboole_0(A_23, B_24))=k2_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_39])).
% 29.82/20.85  tff(c_97, plain, (![A_1, B_2]: (k2_xboole_0(A_1, k2_xboole_0(B_2, A_1))=k2_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_79])).
% 29.82/20.85  tff(c_6, plain, (![A_5, B_6]: (k2_xboole_0(A_5, k4_xboole_0(B_6, A_5))=k2_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 29.82/20.85  tff(c_188, plain, (![A_30, B_31]: (k2_xboole_0(k4_xboole_0(A_30, B_31), k4_xboole_0(B_31, A_30))=k5_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_29])).
% 29.82/20.85  tff(c_224, plain, (![B_31, A_30]: (k2_xboole_0(k4_xboole_0(B_31, A_30), k4_xboole_0(A_30, B_31))=k5_xboole_0(A_30, B_31))), inference(superposition, [status(thm), theory('equality')], [c_2, c_188])).
% 29.82/20.85  tff(c_12, plain, (![A_12, B_13, C_14]: (k2_xboole_0(k2_xboole_0(A_12, B_13), C_14)=k2_xboole_0(A_12, k2_xboole_0(B_13, C_14)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 29.82/20.85  tff(c_231, plain, (![A_32, B_33, C_34]: (k2_xboole_0(k2_xboole_0(A_32, B_33), C_34)=k2_xboole_0(A_32, k2_xboole_0(B_33, C_34)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 29.82/20.85  tff(c_287, plain, (![A_5, B_6, C_34]: (k2_xboole_0(A_5, k2_xboole_0(k4_xboole_0(B_6, A_5), C_34))=k2_xboole_0(k2_xboole_0(A_5, B_6), C_34))), inference(superposition, [status(thm), theory('equality')], [c_6, c_231])).
% 29.82/20.85  tff(c_2490, plain, (![A_66, B_67, C_68]: (k2_xboole_0(A_66, k2_xboole_0(k4_xboole_0(B_67, A_66), C_68))=k2_xboole_0(A_66, k2_xboole_0(B_67, C_68)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_287])).
% 29.82/20.85  tff(c_2616, plain, (![A_30, B_31]: (k2_xboole_0(A_30, k2_xboole_0(B_31, k4_xboole_0(A_30, B_31)))=k2_xboole_0(A_30, k5_xboole_0(A_30, B_31)))), inference(superposition, [status(thm), theory('equality')], [c_224, c_2490])).
% 29.82/20.85  tff(c_2703, plain, (![A_30, B_31]: (k2_xboole_0(A_30, k5_xboole_0(A_30, B_31))=k2_xboole_0(A_30, B_31))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_6, c_2616])).
% 29.82/20.85  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(k4_xboole_0(A_3, B_4), k4_xboole_0(B_4, A_3))=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 29.82/20.85  tff(c_14, plain, (![A_15, B_16]: (k2_xboole_0(A_15, k2_xboole_0(A_15, B_16))=k2_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_39])).
% 29.82/20.85  tff(c_197, plain, (![A_30, B_31]: (k2_xboole_0(k4_xboole_0(A_30, B_31), k5_xboole_0(A_30, B_31))=k2_xboole_0(k4_xboole_0(A_30, B_31), k4_xboole_0(B_31, A_30)))), inference(superposition, [status(thm), theory('equality')], [c_188, c_14])).
% 29.82/20.85  tff(c_227, plain, (![A_30, B_31]: (k2_xboole_0(k4_xboole_0(A_30, B_31), k5_xboole_0(A_30, B_31))=k5_xboole_0(A_30, B_31))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_197])).
% 29.82/20.85  tff(c_10, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k4_xboole_0(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_35])).
% 29.82/20.85  tff(c_151, plain, (![A_27, B_28, C_29]: (k4_xboole_0(k4_xboole_0(A_27, B_28), C_29)=k4_xboole_0(A_27, k2_xboole_0(B_28, C_29)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 29.82/20.85  tff(c_3510, plain, (![A_78, B_79, C_80]: (k4_xboole_0(A_78, k2_xboole_0(k4_xboole_0(A_78, B_79), C_80))=k4_xboole_0(k3_xboole_0(A_78, B_79), C_80))), inference(superposition, [status(thm), theory('equality')], [c_10, c_151])).
% 29.82/20.85  tff(c_65324, plain, (![A_306, B_307]: (k4_xboole_0(k3_xboole_0(A_306, B_307), k5_xboole_0(A_306, B_307))=k4_xboole_0(A_306, k5_xboole_0(A_306, B_307)))), inference(superposition, [status(thm), theory('equality')], [c_227, c_3510])).
% 29.82/20.85  tff(c_65432, plain, (![A_306, B_307]: (k2_xboole_0(k5_xboole_0(A_306, B_307), k4_xboole_0(A_306, k5_xboole_0(A_306, B_307)))=k2_xboole_0(k5_xboole_0(A_306, B_307), k3_xboole_0(A_306, B_307)))), inference(superposition, [status(thm), theory('equality')], [c_65324, c_6])).
% 29.82/20.85  tff(c_65487, plain, (![A_306, B_307]: (k2_xboole_0(k3_xboole_0(A_306, B_307), k5_xboole_0(A_306, B_307))=k2_xboole_0(A_306, B_307))), inference(demodulation, [status(thm), theory('equality')], [c_2703, c_2, c_6, c_2, c_65432])).
% 29.82/20.85  tff(c_16, plain, (k2_xboole_0(k5_xboole_0('#skF_1', '#skF_2'), k3_xboole_0('#skF_1', '#skF_2'))!=k2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_42])).
% 29.82/20.85  tff(c_17, plain, (k2_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), k5_xboole_0('#skF_1', '#skF_2'))!=k2_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_16])).
% 29.82/20.85  tff(c_65496, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_65487, c_17])).
% 29.82/20.85  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 29.82/20.85  
% 29.82/20.85  Inference rules
% 29.82/20.85  ----------------------
% 29.82/20.85  #Ref     : 0
% 29.82/20.85  #Sup     : 16179
% 29.82/20.85  #Fact    : 0
% 29.82/20.85  #Define  : 0
% 29.82/20.85  #Split   : 0
% 29.82/20.85  #Chain   : 0
% 29.82/20.85  #Close   : 0
% 29.82/20.85  
% 29.82/20.85  Ordering : KBO
% 29.82/20.85  
% 29.82/20.85  Simplification rules
% 29.82/20.85  ----------------------
% 29.82/20.85  #Subsume      : 2403
% 29.82/20.85  #Demod        : 34971
% 29.82/20.85  #Tautology    : 4713
% 29.82/20.85  #SimpNegUnit  : 0
% 29.82/20.85  #BackRed      : 4
% 29.82/20.85  
% 29.82/20.85  #Partial instantiations: 0
% 29.82/20.85  #Strategies tried      : 1
% 29.82/20.85  
% 29.82/20.85  Timing (in seconds)
% 29.82/20.85  ----------------------
% 29.82/20.86  Preprocessing        : 0.27
% 29.82/20.86  Parsing              : 0.15
% 29.82/20.86  CNF conversion       : 0.01
% 29.82/20.86  Main loop            : 19.76
% 29.82/20.86  Inferencing          : 1.68
% 29.82/20.86  Reduction            : 15.86
% 29.82/20.86  Demodulation         : 15.37
% 29.82/20.86  BG Simplification    : 0.29
% 29.82/20.86  Subsumption          : 1.55
% 29.82/20.86  Abstraction          : 0.60
% 29.82/20.86  MUC search           : 0.00
% 29.82/20.86  Cooper               : 0.00
% 29.82/20.86  Total                : 20.06
% 29.82/20.86  Index Insertion      : 0.00
% 29.82/20.86  Index Deletion       : 0.00
% 29.82/20.86  Index Matching       : 0.00
% 29.82/20.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
