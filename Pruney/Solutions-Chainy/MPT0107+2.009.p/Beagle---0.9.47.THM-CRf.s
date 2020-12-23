%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:53 EST 2020

% Result     : Theorem 5.12s
% Output     : CNFRefutation 5.12s
% Verified   : 
% Statistics : Number of formulae       :   52 (  80 expanded)
%              Number of leaves         :   21 (  35 expanded)
%              Depth                    :    9
%              Number of atoms          :   42 (  70 expanded)
%              Number of equality atoms :   41 (  69 expanded)
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

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_51,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_55,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_53,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_62,negated_conjecture,(
    ~ ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_14,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k3_xboole_0(A_14,B_15)) = k4_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_16,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k4_xboole_0(A_16,B_17)) = k3_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_257,plain,(
    ! [A_51,B_52] : k4_xboole_0(A_51,k4_xboole_0(A_51,B_52)) = k3_xboole_0(A_51,B_52) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_269,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k3_xboole_0(A_16,B_17)) = k3_xboole_0(A_16,k4_xboole_0(A_16,B_17)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_257])).

tff(c_281,plain,(
    ! [A_16,B_17] : k3_xboole_0(A_16,k4_xboole_0(A_16,B_17)) = k4_xboole_0(A_16,B_17) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_269])).

tff(c_20,plain,(
    ! [A_21,B_22] : k2_xboole_0(k3_xboole_0(A_21,B_22),k4_xboole_0(A_21,B_22)) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_32,plain,(
    ! [A_33,B_34] : k5_xboole_0(A_33,k4_xboole_0(B_34,A_33)) = k2_xboole_0(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_10,plain,(
    ! [A_9,B_10] : k4_xboole_0(k2_xboole_0(A_9,B_10),B_10) = k4_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_284,plain,(
    ! [A_53,B_54] : k5_xboole_0(A_53,k4_xboole_0(B_54,A_53)) = k2_xboole_0(A_53,B_54) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_300,plain,(
    ! [B_10,A_9] : k5_xboole_0(B_10,k4_xboole_0(A_9,B_10)) = k2_xboole_0(B_10,k2_xboole_0(A_9,B_10)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_284])).

tff(c_542,plain,(
    ! [B_65,A_66] : k2_xboole_0(B_65,k2_xboole_0(A_66,B_65)) = k2_xboole_0(B_65,A_66) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_300])).

tff(c_669,plain,(
    ! [A_70,B_71] : k2_xboole_0(A_70,k2_xboole_0(A_70,B_71)) = k2_xboole_0(A_70,B_71) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_542])).

tff(c_704,plain,(
    ! [A_21,B_22] : k2_xboole_0(k3_xboole_0(A_21,B_22),k4_xboole_0(A_21,B_22)) = k2_xboole_0(k3_xboole_0(A_21,B_22),A_21) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_669])).

tff(c_727,plain,(
    ! [A_72,B_73] : k2_xboole_0(A_72,k3_xboole_0(A_72,B_73)) = A_72 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_2,c_704])).

tff(c_751,plain,(
    ! [A_16,B_17] : k2_xboole_0(A_16,k4_xboole_0(A_16,B_17)) = A_16 ),
    inference(superposition,[status(thm),theory(equality)],[c_281,c_727])).

tff(c_70,plain,(
    ! [B_38,A_39] : k5_xboole_0(B_38,A_39) = k5_xboole_0(A_39,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_24,plain,(
    ! [A_26] : k5_xboole_0(A_26,k1_xboole_0) = A_26 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_86,plain,(
    ! [A_39] : k5_xboole_0(k1_xboole_0,A_39) = A_39 ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_24])).

tff(c_28,plain,(
    ! [A_30] : k5_xboole_0(A_30,A_30) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_951,plain,(
    ! [A_81,B_82,C_83] : k5_xboole_0(k5_xboole_0(A_81,B_82),C_83) = k5_xboole_0(A_81,k5_xboole_0(B_82,C_83)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1028,plain,(
    ! [A_30,C_83] : k5_xboole_0(A_30,k5_xboole_0(A_30,C_83)) = k5_xboole_0(k1_xboole_0,C_83) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_951])).

tff(c_1042,plain,(
    ! [A_84,C_85] : k5_xboole_0(A_84,k5_xboole_0(A_84,C_85)) = C_85 ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_1028])).

tff(c_3623,plain,(
    ! [A_131,B_132] : k5_xboole_0(A_131,k2_xboole_0(A_131,B_132)) = k4_xboole_0(B_132,A_131) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_1042])).

tff(c_1091,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k5_xboole_0(B_4,A_3)) = B_4 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1042])).

tff(c_4465,plain,(
    ! [A_140,B_141] : k5_xboole_0(k2_xboole_0(A_140,B_141),k4_xboole_0(B_141,A_140)) = A_140 ),
    inference(superposition,[status(thm),theory(equality)],[c_3623,c_1091])).

tff(c_4561,plain,(
    ! [A_16,B_17] : k5_xboole_0(k2_xboole_0(k4_xboole_0(A_16,B_17),A_16),k3_xboole_0(A_16,B_17)) = k4_xboole_0(A_16,B_17) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_4465])).

tff(c_4601,plain,(
    ! [A_16,B_17] : k5_xboole_0(A_16,k3_xboole_0(A_16,B_17)) = k4_xboole_0(A_16,B_17) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_751,c_4,c_2,c_4561])).

tff(c_34,plain,(
    k5_xboole_0('#skF_1',k3_xboole_0('#skF_1','#skF_2')) != k4_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_6526,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4601,c_34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:23:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.12/2.00  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.12/2.00  
% 5.12/2.00  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.12/2.00  %$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 5.12/2.00  
% 5.12/2.00  %Foreground sorts:
% 5.12/2.00  
% 5.12/2.00  
% 5.12/2.00  %Background operators:
% 5.12/2.00  
% 5.12/2.00  
% 5.12/2.00  %Foreground operators:
% 5.12/2.00  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.12/2.00  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.12/2.00  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.12/2.00  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.12/2.00  tff('#skF_2', type, '#skF_2': $i).
% 5.12/2.00  tff('#skF_1', type, '#skF_1': $i).
% 5.12/2.00  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.12/2.00  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.12/2.00  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.12/2.00  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.12/2.00  
% 5.12/2.01  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 5.12/2.01  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 5.12/2.01  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.12/2.01  tff(f_47, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 5.12/2.01  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 5.12/2.01  tff(f_59, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 5.12/2.01  tff(f_37, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 5.12/2.01  tff(f_51, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 5.12/2.01  tff(f_55, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 5.12/2.01  tff(f_53, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 5.12/2.01  tff(f_62, negated_conjecture, ~(![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.12/2.01  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.12/2.01  tff(c_14, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k3_xboole_0(A_14, B_15))=k4_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.12/2.01  tff(c_16, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k4_xboole_0(A_16, B_17))=k3_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.12/2.01  tff(c_257, plain, (![A_51, B_52]: (k4_xboole_0(A_51, k4_xboole_0(A_51, B_52))=k3_xboole_0(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.12/2.01  tff(c_269, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k3_xboole_0(A_16, B_17))=k3_xboole_0(A_16, k4_xboole_0(A_16, B_17)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_257])).
% 5.12/2.01  tff(c_281, plain, (![A_16, B_17]: (k3_xboole_0(A_16, k4_xboole_0(A_16, B_17))=k4_xboole_0(A_16, B_17))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_269])).
% 5.12/2.01  tff(c_20, plain, (![A_21, B_22]: (k2_xboole_0(k3_xboole_0(A_21, B_22), k4_xboole_0(A_21, B_22))=A_21)), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.12/2.01  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.12/2.01  tff(c_32, plain, (![A_33, B_34]: (k5_xboole_0(A_33, k4_xboole_0(B_34, A_33))=k2_xboole_0(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.12/2.01  tff(c_10, plain, (![A_9, B_10]: (k4_xboole_0(k2_xboole_0(A_9, B_10), B_10)=k4_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.12/2.01  tff(c_284, plain, (![A_53, B_54]: (k5_xboole_0(A_53, k4_xboole_0(B_54, A_53))=k2_xboole_0(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.12/2.01  tff(c_300, plain, (![B_10, A_9]: (k5_xboole_0(B_10, k4_xboole_0(A_9, B_10))=k2_xboole_0(B_10, k2_xboole_0(A_9, B_10)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_284])).
% 5.12/2.01  tff(c_542, plain, (![B_65, A_66]: (k2_xboole_0(B_65, k2_xboole_0(A_66, B_65))=k2_xboole_0(B_65, A_66))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_300])).
% 5.12/2.01  tff(c_669, plain, (![A_70, B_71]: (k2_xboole_0(A_70, k2_xboole_0(A_70, B_71))=k2_xboole_0(A_70, B_71))), inference(superposition, [status(thm), theory('equality')], [c_2, c_542])).
% 5.12/2.01  tff(c_704, plain, (![A_21, B_22]: (k2_xboole_0(k3_xboole_0(A_21, B_22), k4_xboole_0(A_21, B_22))=k2_xboole_0(k3_xboole_0(A_21, B_22), A_21))), inference(superposition, [status(thm), theory('equality')], [c_20, c_669])).
% 5.12/2.01  tff(c_727, plain, (![A_72, B_73]: (k2_xboole_0(A_72, k3_xboole_0(A_72, B_73))=A_72)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_2, c_704])).
% 5.12/2.01  tff(c_751, plain, (![A_16, B_17]: (k2_xboole_0(A_16, k4_xboole_0(A_16, B_17))=A_16)), inference(superposition, [status(thm), theory('equality')], [c_281, c_727])).
% 5.12/2.01  tff(c_70, plain, (![B_38, A_39]: (k5_xboole_0(B_38, A_39)=k5_xboole_0(A_39, B_38))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.12/2.01  tff(c_24, plain, (![A_26]: (k5_xboole_0(A_26, k1_xboole_0)=A_26)), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.12/2.01  tff(c_86, plain, (![A_39]: (k5_xboole_0(k1_xboole_0, A_39)=A_39)), inference(superposition, [status(thm), theory('equality')], [c_70, c_24])).
% 5.12/2.01  tff(c_28, plain, (![A_30]: (k5_xboole_0(A_30, A_30)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.12/2.01  tff(c_951, plain, (![A_81, B_82, C_83]: (k5_xboole_0(k5_xboole_0(A_81, B_82), C_83)=k5_xboole_0(A_81, k5_xboole_0(B_82, C_83)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.12/2.01  tff(c_1028, plain, (![A_30, C_83]: (k5_xboole_0(A_30, k5_xboole_0(A_30, C_83))=k5_xboole_0(k1_xboole_0, C_83))), inference(superposition, [status(thm), theory('equality')], [c_28, c_951])).
% 5.12/2.01  tff(c_1042, plain, (![A_84, C_85]: (k5_xboole_0(A_84, k5_xboole_0(A_84, C_85))=C_85)), inference(demodulation, [status(thm), theory('equality')], [c_86, c_1028])).
% 5.12/2.01  tff(c_3623, plain, (![A_131, B_132]: (k5_xboole_0(A_131, k2_xboole_0(A_131, B_132))=k4_xboole_0(B_132, A_131))), inference(superposition, [status(thm), theory('equality')], [c_32, c_1042])).
% 5.12/2.01  tff(c_1091, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k5_xboole_0(B_4, A_3))=B_4)), inference(superposition, [status(thm), theory('equality')], [c_4, c_1042])).
% 5.12/2.01  tff(c_4465, plain, (![A_140, B_141]: (k5_xboole_0(k2_xboole_0(A_140, B_141), k4_xboole_0(B_141, A_140))=A_140)), inference(superposition, [status(thm), theory('equality')], [c_3623, c_1091])).
% 5.12/2.01  tff(c_4561, plain, (![A_16, B_17]: (k5_xboole_0(k2_xboole_0(k4_xboole_0(A_16, B_17), A_16), k3_xboole_0(A_16, B_17))=k4_xboole_0(A_16, B_17))), inference(superposition, [status(thm), theory('equality')], [c_16, c_4465])).
% 5.12/2.01  tff(c_4601, plain, (![A_16, B_17]: (k5_xboole_0(A_16, k3_xboole_0(A_16, B_17))=k4_xboole_0(A_16, B_17))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_751, c_4, c_2, c_4561])).
% 5.12/2.01  tff(c_34, plain, (k5_xboole_0('#skF_1', k3_xboole_0('#skF_1', '#skF_2'))!=k4_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.12/2.01  tff(c_6526, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4601, c_34])).
% 5.12/2.01  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.12/2.01  
% 5.12/2.01  Inference rules
% 5.12/2.01  ----------------------
% 5.12/2.01  #Ref     : 1
% 5.12/2.01  #Sup     : 1630
% 5.12/2.01  #Fact    : 0
% 5.12/2.01  #Define  : 0
% 5.12/2.01  #Split   : 0
% 5.12/2.01  #Chain   : 0
% 5.12/2.01  #Close   : 0
% 5.12/2.01  
% 5.12/2.01  Ordering : KBO
% 5.12/2.01  
% 5.12/2.01  Simplification rules
% 5.12/2.01  ----------------------
% 5.12/2.01  #Subsume      : 50
% 5.12/2.01  #Demod        : 1701
% 5.12/2.01  #Tautology    : 965
% 5.12/2.01  #SimpNegUnit  : 0
% 5.12/2.01  #BackRed      : 7
% 5.12/2.01  
% 5.12/2.01  #Partial instantiations: 0
% 5.12/2.01  #Strategies tried      : 1
% 5.12/2.01  
% 5.12/2.01  Timing (in seconds)
% 5.12/2.01  ----------------------
% 5.12/2.02  Preprocessing        : 0.28
% 5.12/2.02  Parsing              : 0.15
% 5.12/2.02  CNF conversion       : 0.02
% 5.12/2.02  Main loop            : 0.97
% 5.12/2.02  Inferencing          : 0.29
% 5.12/2.02  Reduction            : 0.47
% 5.12/2.02  Demodulation         : 0.40
% 5.12/2.02  BG Simplification    : 0.04
% 5.12/2.02  Subsumption          : 0.12
% 5.12/2.02  Abstraction          : 0.06
% 5.12/2.02  MUC search           : 0.00
% 5.12/2.02  Cooper               : 0.00
% 5.12/2.02  Total                : 1.28
% 5.12/2.02  Index Insertion      : 0.00
% 5.12/2.02  Index Deletion       : 0.00
% 5.12/2.02  Index Matching       : 0.00
% 5.12/2.02  BG Taut test         : 0.00
%------------------------------------------------------------------------------
