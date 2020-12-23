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
% DateTime   : Thu Dec  3 09:44:38 EST 2020

% Result     : Theorem 9.02s
% Output     : CNFRefutation 9.02s
% Verified   : 
% Statistics : Number of formulae       :   43 (  83 expanded)
%              Number of leaves         :   16 (  35 expanded)
%              Depth                    :    8
%              Number of atoms          :   34 (  74 expanded)
%              Number of equality atoms :   33 (  73 expanded)
%              Maximal formula depth    :    4 (   3 average)
%              Maximal term depth       :    4 (   2 average)

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

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_42,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_xboole_1)).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_93,plain,(
    ! [A_21,B_22] : k2_xboole_0(k3_xboole_0(A_21,B_22),k4_xboole_0(A_21,B_22)) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_102,plain,(
    ! [B_4,A_3] : k2_xboole_0(k3_xboole_0(B_4,A_3),k4_xboole_0(A_3,B_4)) = A_3 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_93])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_7] : k2_xboole_0(A_7,A_7) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_158,plain,(
    ! [A_27,B_28,C_29] : k2_xboole_0(k2_xboole_0(A_27,B_28),C_29) = k2_xboole_0(A_27,k2_xboole_0(B_28,C_29)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_260,plain,(
    ! [A_33,C_34] : k2_xboole_0(A_33,k2_xboole_0(A_33,C_34)) = k2_xboole_0(A_33,C_34) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_158])).

tff(c_292,plain,(
    ! [B_4,A_3] : k2_xboole_0(k3_xboole_0(B_4,A_3),k4_xboole_0(A_3,B_4)) = k2_xboole_0(k3_xboole_0(B_4,A_3),A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_260])).

tff(c_314,plain,(
    ! [A_3,B_4] : k2_xboole_0(A_3,k3_xboole_0(B_4,A_3)) = A_3 ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_2,c_292])).

tff(c_568,plain,(
    ! [A_47,A_45,B_46] : k2_xboole_0(A_47,k2_xboole_0(A_45,B_46)) = k2_xboole_0(A_45,k2_xboole_0(B_46,A_47)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_158])).

tff(c_827,plain,(
    ! [A_48,A_49] : k2_xboole_0(A_48,k2_xboole_0(A_48,A_49)) = k2_xboole_0(A_49,A_48) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_568])).

tff(c_920,plain,(
    ! [A_3,B_4] : k2_xboole_0(k4_xboole_0(A_3,B_4),k3_xboole_0(B_4,A_3)) = k2_xboole_0(k3_xboole_0(B_4,A_3),A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_827])).

tff(c_955,plain,(
    ! [A_3,B_4] : k2_xboole_0(k4_xboole_0(A_3,B_4),k3_xboole_0(B_4,A_3)) = A_3 ),
    inference(demodulation,[status(thm),theory(equality)],[c_314,c_2,c_920])).

tff(c_14,plain,(
    ! [A_14,B_15] : k2_xboole_0(k3_xboole_0(A_14,B_15),k4_xboole_0(A_14,B_15)) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_186,plain,(
    ! [A_14,B_15,C_29] : k2_xboole_0(k3_xboole_0(A_14,B_15),k2_xboole_0(k4_xboole_0(A_14,B_15),C_29)) = k2_xboole_0(A_14,C_29) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_158])).

tff(c_200,plain,(
    ! [A_27,B_28,A_1] : k2_xboole_0(A_27,k2_xboole_0(B_28,A_1)) = k2_xboole_0(A_1,k2_xboole_0(A_27,B_28)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_158])).

tff(c_3647,plain,(
    ! [A_87,B_88,C_89] : k2_xboole_0(k3_xboole_0(A_87,B_88),k2_xboole_0(k4_xboole_0(A_87,B_88),C_89)) = k2_xboole_0(A_87,C_89) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_158])).

tff(c_203,plain,(
    ! [A_7,C_29] : k2_xboole_0(A_7,k2_xboole_0(A_7,C_29)) = k2_xboole_0(A_7,C_29) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_158])).

tff(c_3706,plain,(
    ! [A_87,B_88,C_89] : k2_xboole_0(k3_xboole_0(A_87,B_88),k2_xboole_0(k4_xboole_0(A_87,B_88),C_89)) = k2_xboole_0(k3_xboole_0(A_87,B_88),k2_xboole_0(A_87,C_89)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3647,c_203])).

tff(c_7561,plain,(
    ! [A_156,C_157,B_158] : k2_xboole_0(A_156,k2_xboole_0(C_157,k3_xboole_0(A_156,B_158))) = k2_xboole_0(A_156,C_157) ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_200,c_3706])).

tff(c_7763,plain,(
    ! [B_4,A_3] : k2_xboole_0(B_4,k4_xboole_0(A_3,B_4)) = k2_xboole_0(B_4,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_955,c_7561])).

tff(c_6,plain,(
    ! [A_5,B_6] : k2_xboole_0(k4_xboole_0(A_5,B_6),k4_xboole_0(B_6,A_5)) = k5_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3805,plain,(
    ! [A_5,B_6] : k2_xboole_0(k3_xboole_0(A_5,B_6),k5_xboole_0(A_5,B_6)) = k2_xboole_0(A_5,k4_xboole_0(B_6,A_5)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_3647])).

tff(c_10256,plain,(
    ! [A_5,B_6] : k2_xboole_0(k3_xboole_0(A_5,B_6),k5_xboole_0(A_5,B_6)) = k2_xboole_0(A_5,B_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7763,c_3805])).

tff(c_16,plain,(
    k2_xboole_0(k5_xboole_0('#skF_1','#skF_2'),k3_xboole_0('#skF_1','#skF_2')) != k2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_17,plain,(
    k2_xboole_0(k3_xboole_0('#skF_1','#skF_2'),k5_xboole_0('#skF_1','#skF_2')) != k2_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_16])).

tff(c_10259,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10256,c_17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:00:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.02/3.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.02/3.34  
% 9.02/3.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.02/3.34  %$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_1
% 9.02/3.34  
% 9.02/3.34  %Foreground sorts:
% 9.02/3.34  
% 9.02/3.34  
% 9.02/3.34  %Background operators:
% 9.02/3.34  
% 9.02/3.34  
% 9.02/3.34  %Foreground operators:
% 9.02/3.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.02/3.34  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.02/3.34  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 9.02/3.34  tff('#skF_2', type, '#skF_2': $i).
% 9.02/3.34  tff('#skF_1', type, '#skF_1': $i).
% 9.02/3.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.02/3.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.02/3.34  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.02/3.34  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.02/3.34  
% 9.02/3.36  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 9.02/3.36  tff(f_39, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 9.02/3.36  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 9.02/3.36  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 9.02/3.36  tff(f_37, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 9.02/3.36  tff(f_31, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_xboole_0)).
% 9.02/3.36  tff(f_42, negated_conjecture, ~(![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t93_xboole_1)).
% 9.02/3.36  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 9.02/3.36  tff(c_93, plain, (![A_21, B_22]: (k2_xboole_0(k3_xboole_0(A_21, B_22), k4_xboole_0(A_21, B_22))=A_21)), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.02/3.36  tff(c_102, plain, (![B_4, A_3]: (k2_xboole_0(k3_xboole_0(B_4, A_3), k4_xboole_0(A_3, B_4))=A_3)), inference(superposition, [status(thm), theory('equality')], [c_4, c_93])).
% 9.02/3.36  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.02/3.36  tff(c_8, plain, (![A_7]: (k2_xboole_0(A_7, A_7)=A_7)), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.02/3.36  tff(c_158, plain, (![A_27, B_28, C_29]: (k2_xboole_0(k2_xboole_0(A_27, B_28), C_29)=k2_xboole_0(A_27, k2_xboole_0(B_28, C_29)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.02/3.36  tff(c_260, plain, (![A_33, C_34]: (k2_xboole_0(A_33, k2_xboole_0(A_33, C_34))=k2_xboole_0(A_33, C_34))), inference(superposition, [status(thm), theory('equality')], [c_8, c_158])).
% 9.02/3.36  tff(c_292, plain, (![B_4, A_3]: (k2_xboole_0(k3_xboole_0(B_4, A_3), k4_xboole_0(A_3, B_4))=k2_xboole_0(k3_xboole_0(B_4, A_3), A_3))), inference(superposition, [status(thm), theory('equality')], [c_102, c_260])).
% 9.02/3.36  tff(c_314, plain, (![A_3, B_4]: (k2_xboole_0(A_3, k3_xboole_0(B_4, A_3))=A_3)), inference(demodulation, [status(thm), theory('equality')], [c_102, c_2, c_292])).
% 9.02/3.36  tff(c_568, plain, (![A_47, A_45, B_46]: (k2_xboole_0(A_47, k2_xboole_0(A_45, B_46))=k2_xboole_0(A_45, k2_xboole_0(B_46, A_47)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_158])).
% 9.02/3.36  tff(c_827, plain, (![A_48, A_49]: (k2_xboole_0(A_48, k2_xboole_0(A_48, A_49))=k2_xboole_0(A_49, A_48))), inference(superposition, [status(thm), theory('equality')], [c_8, c_568])).
% 9.02/3.36  tff(c_920, plain, (![A_3, B_4]: (k2_xboole_0(k4_xboole_0(A_3, B_4), k3_xboole_0(B_4, A_3))=k2_xboole_0(k3_xboole_0(B_4, A_3), A_3))), inference(superposition, [status(thm), theory('equality')], [c_102, c_827])).
% 9.02/3.36  tff(c_955, plain, (![A_3, B_4]: (k2_xboole_0(k4_xboole_0(A_3, B_4), k3_xboole_0(B_4, A_3))=A_3)), inference(demodulation, [status(thm), theory('equality')], [c_314, c_2, c_920])).
% 9.02/3.36  tff(c_14, plain, (![A_14, B_15]: (k2_xboole_0(k3_xboole_0(A_14, B_15), k4_xboole_0(A_14, B_15))=A_14)), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.02/3.36  tff(c_186, plain, (![A_14, B_15, C_29]: (k2_xboole_0(k3_xboole_0(A_14, B_15), k2_xboole_0(k4_xboole_0(A_14, B_15), C_29))=k2_xboole_0(A_14, C_29))), inference(superposition, [status(thm), theory('equality')], [c_14, c_158])).
% 9.02/3.36  tff(c_200, plain, (![A_27, B_28, A_1]: (k2_xboole_0(A_27, k2_xboole_0(B_28, A_1))=k2_xboole_0(A_1, k2_xboole_0(A_27, B_28)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_158])).
% 9.02/3.36  tff(c_3647, plain, (![A_87, B_88, C_89]: (k2_xboole_0(k3_xboole_0(A_87, B_88), k2_xboole_0(k4_xboole_0(A_87, B_88), C_89))=k2_xboole_0(A_87, C_89))), inference(superposition, [status(thm), theory('equality')], [c_14, c_158])).
% 9.02/3.36  tff(c_203, plain, (![A_7, C_29]: (k2_xboole_0(A_7, k2_xboole_0(A_7, C_29))=k2_xboole_0(A_7, C_29))), inference(superposition, [status(thm), theory('equality')], [c_8, c_158])).
% 9.02/3.36  tff(c_3706, plain, (![A_87, B_88, C_89]: (k2_xboole_0(k3_xboole_0(A_87, B_88), k2_xboole_0(k4_xboole_0(A_87, B_88), C_89))=k2_xboole_0(k3_xboole_0(A_87, B_88), k2_xboole_0(A_87, C_89)))), inference(superposition, [status(thm), theory('equality')], [c_3647, c_203])).
% 9.02/3.36  tff(c_7561, plain, (![A_156, C_157, B_158]: (k2_xboole_0(A_156, k2_xboole_0(C_157, k3_xboole_0(A_156, B_158)))=k2_xboole_0(A_156, C_157))), inference(demodulation, [status(thm), theory('equality')], [c_186, c_200, c_3706])).
% 9.02/3.36  tff(c_7763, plain, (![B_4, A_3]: (k2_xboole_0(B_4, k4_xboole_0(A_3, B_4))=k2_xboole_0(B_4, A_3))), inference(superposition, [status(thm), theory('equality')], [c_955, c_7561])).
% 9.02/3.36  tff(c_6, plain, (![A_5, B_6]: (k2_xboole_0(k4_xboole_0(A_5, B_6), k4_xboole_0(B_6, A_5))=k5_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.02/3.36  tff(c_3805, plain, (![A_5, B_6]: (k2_xboole_0(k3_xboole_0(A_5, B_6), k5_xboole_0(A_5, B_6))=k2_xboole_0(A_5, k4_xboole_0(B_6, A_5)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_3647])).
% 9.02/3.36  tff(c_10256, plain, (![A_5, B_6]: (k2_xboole_0(k3_xboole_0(A_5, B_6), k5_xboole_0(A_5, B_6))=k2_xboole_0(A_5, B_6))), inference(demodulation, [status(thm), theory('equality')], [c_7763, c_3805])).
% 9.02/3.36  tff(c_16, plain, (k2_xboole_0(k5_xboole_0('#skF_1', '#skF_2'), k3_xboole_0('#skF_1', '#skF_2'))!=k2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_42])).
% 9.02/3.36  tff(c_17, plain, (k2_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), k5_xboole_0('#skF_1', '#skF_2'))!=k2_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_16])).
% 9.02/3.36  tff(c_10259, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10256, c_17])).
% 9.02/3.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.02/3.36  
% 9.02/3.36  Inference rules
% 9.02/3.36  ----------------------
% 9.02/3.36  #Ref     : 0
% 9.02/3.36  #Sup     : 2560
% 9.02/3.36  #Fact    : 0
% 9.02/3.36  #Define  : 0
% 9.02/3.36  #Split   : 0
% 9.02/3.36  #Chain   : 0
% 9.02/3.36  #Close   : 0
% 9.02/3.36  
% 9.02/3.36  Ordering : KBO
% 9.02/3.36  
% 9.02/3.36  Simplification rules
% 9.02/3.36  ----------------------
% 9.02/3.36  #Subsume      : 116
% 9.02/3.36  #Demod        : 1885
% 9.02/3.36  #Tautology    : 936
% 9.02/3.36  #SimpNegUnit  : 0
% 9.02/3.36  #BackRed      : 1
% 9.02/3.36  
% 9.02/3.36  #Partial instantiations: 0
% 9.02/3.36  #Strategies tried      : 1
% 9.02/3.36  
% 9.02/3.36  Timing (in seconds)
% 9.02/3.36  ----------------------
% 9.02/3.36  Preprocessing        : 0.32
% 9.02/3.36  Parsing              : 0.16
% 9.02/3.36  CNF conversion       : 0.02
% 9.02/3.36  Main loop            : 2.16
% 9.02/3.36  Inferencing          : 0.52
% 9.02/3.36  Reduction            : 1.25
% 9.02/3.36  Demodulation         : 1.14
% 9.02/3.36  BG Simplification    : 0.07
% 9.02/3.36  Subsumption          : 0.23
% 9.02/3.36  Abstraction          : 0.10
% 9.02/3.36  MUC search           : 0.00
% 9.02/3.36  Cooper               : 0.00
% 9.02/3.36  Total                : 2.50
% 9.02/3.36  Index Insertion      : 0.00
% 9.02/3.36  Index Deletion       : 0.00
% 9.02/3.36  Index Matching       : 0.00
% 9.02/3.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
