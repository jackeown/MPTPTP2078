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
% DateTime   : Thu Dec  3 09:47:16 EST 2020

% Result     : Theorem 2.70s
% Output     : CNFRefutation 2.70s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 116 expanded)
%              Number of leaves         :   21 (  49 expanded)
%              Depth                    :    9
%              Number of atoms          :   38 ( 103 expanded)
%              Number of equality atoms :   37 ( 102 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(f_35,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k2_tarski(A,B),k1_tarski(C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).

tff(f_39,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_46,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(B,A),k2_tarski(C,A)) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_enumset1)).

tff(c_10,plain,(
    ! [A_12,B_13,C_14] : k2_xboole_0(k2_tarski(A_12,B_13),k1_tarski(C_14)) = k1_enumset1(A_12,B_13,C_14) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14,plain,(
    ! [A_19] : k2_tarski(A_19,A_19) = k1_tarski(A_19) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_401,plain,(
    ! [A_57,B_58,C_59,D_60] : k2_xboole_0(k2_tarski(A_57,B_58),k2_tarski(C_59,D_60)) = k2_enumset1(A_57,B_58,C_59,D_60) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_437,plain,(
    ! [A_57,B_58,A_19] : k2_xboole_0(k2_tarski(A_57,B_58),k1_tarski(A_19)) = k2_enumset1(A_57,B_58,A_19,A_19) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_401])).

tff(c_441,plain,(
    ! [A_57,B_58,A_19] : k2_enumset1(A_57,B_58,A_19,A_19) = k1_enumset1(A_57,B_58,A_19) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_437])).

tff(c_8,plain,(
    ! [A_9,B_10,C_11] : k2_xboole_0(k1_tarski(A_9),k2_tarski(B_10,C_11)) = k1_enumset1(A_9,B_10,C_11) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_170,plain,(
    ! [A_41,B_42,C_43] : k2_xboole_0(k2_tarski(A_41,B_42),k1_tarski(C_43)) = k1_enumset1(A_41,B_42,C_43) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_535,plain,(
    ! [C_69,A_70,B_71] : k2_xboole_0(k1_tarski(C_69),k2_tarski(A_70,B_71)) = k1_enumset1(A_70,B_71,C_69) ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_2])).

tff(c_576,plain,(
    ! [C_72,A_73,B_74] : k1_enumset1(C_72,A_73,B_74) = k1_enumset1(A_73,B_74,C_72) ),
    inference(superposition,[status(thm),theory(equality)],[c_535,c_8])).

tff(c_16,plain,(
    ! [A_20,B_21] : k1_enumset1(A_20,A_20,B_21) = k2_tarski(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_878,plain,(
    ! [C_84,B_85] : k1_enumset1(C_84,B_85,B_85) = k2_tarski(B_85,C_84) ),
    inference(superposition,[status(thm),theory(equality)],[c_576,c_16])).

tff(c_12,plain,(
    ! [A_15,B_16,C_17,D_18] : k2_xboole_0(k1_tarski(A_15),k1_enumset1(B_16,C_17,D_18)) = k2_enumset1(A_15,B_16,C_17,D_18) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_902,plain,(
    ! [A_15,B_85,C_84] : k2_xboole_0(k1_tarski(A_15),k2_tarski(B_85,C_84)) = k2_enumset1(A_15,C_84,B_85,B_85) ),
    inference(superposition,[status(thm),theory(equality)],[c_878,c_12])).

tff(c_953,plain,(
    ! [A_15,C_84,B_85] : k1_enumset1(A_15,C_84,B_85) = k1_enumset1(A_15,B_85,C_84) ),
    inference(demodulation,[status(thm),theory(equality)],[c_441,c_8,c_902])).

tff(c_541,plain,(
    ! [C_69,A_70,B_71] : k1_enumset1(C_69,A_70,B_71) = k1_enumset1(A_70,B_71,C_69) ),
    inference(superposition,[status(thm),theory(equality)],[c_535,c_8])).

tff(c_191,plain,(
    ! [A_19,C_43] : k2_xboole_0(k1_tarski(A_19),k1_tarski(C_43)) = k1_enumset1(A_19,A_19,C_43) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_170])).

tff(c_194,plain,(
    ! [A_19,C_43] : k2_xboole_0(k1_tarski(A_19),k1_tarski(C_43)) = k2_tarski(A_19,C_43) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_191])).

tff(c_91,plain,(
    ! [A_35,B_36,C_37] : k2_xboole_0(k1_tarski(A_35),k2_tarski(B_36,C_37)) = k1_enumset1(A_35,B_36,C_37) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_112,plain,(
    ! [A_35,A_19] : k2_xboole_0(k1_tarski(A_35),k1_tarski(A_19)) = k1_enumset1(A_35,A_19,A_19) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_91])).

tff(c_224,plain,(
    ! [A_35,A_19] : k1_enumset1(A_35,A_19,A_19) = k2_tarski(A_35,A_19) ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_112])).

tff(c_639,plain,(
    ! [C_75,A_76] : k1_enumset1(C_75,A_76,C_75) = k2_tarski(A_76,C_75) ),
    inference(superposition,[status(thm),theory(equality)],[c_576,c_224])).

tff(c_651,plain,(
    ! [A_15,A_76,C_75] : k2_xboole_0(k1_tarski(A_15),k2_tarski(A_76,C_75)) = k2_enumset1(A_15,C_75,A_76,C_75) ),
    inference(superposition,[status(thm),theory(equality)],[c_639,c_12])).

tff(c_688,plain,(
    ! [A_15,C_75,A_76] : k2_enumset1(A_15,C_75,A_76,C_75) = k1_enumset1(A_15,A_76,C_75) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_651])).

tff(c_6,plain,(
    ! [A_5,B_6,C_7,D_8] : k2_xboole_0(k2_tarski(A_5,B_6),k2_tarski(C_7,D_8)) = k2_enumset1(A_5,B_6,C_7,D_8) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_20,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_21,plain,(
    k2_enumset1('#skF_2','#skF_1','#skF_3','#skF_1') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_20])).

tff(c_973,plain,(
    k2_enumset1('#skF_2','#skF_1','#skF_3','#skF_1') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_953,c_21])).

tff(c_1454,plain,(
    k1_enumset1('#skF_2','#skF_3','#skF_1') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_688,c_973])).

tff(c_1457,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_953,c_541,c_541,c_1454])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:35:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.70/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.70/1.43  
% 2.70/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.70/1.43  %$ k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 2.70/1.43  
% 2.70/1.43  %Foreground sorts:
% 2.70/1.43  
% 2.70/1.43  
% 2.70/1.43  %Background operators:
% 2.70/1.43  
% 2.70/1.43  
% 2.70/1.43  %Foreground operators:
% 2.70/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.70/1.43  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.70/1.43  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.70/1.43  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.70/1.43  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.70/1.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.70/1.43  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.70/1.43  tff('#skF_2', type, '#skF_2': $i).
% 2.70/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.70/1.43  tff('#skF_1', type, '#skF_1': $i).
% 2.70/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.70/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.70/1.43  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.70/1.43  
% 2.70/1.45  tff(f_35, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k2_tarski(A, B), k1_tarski(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_enumset1)).
% 2.70/1.45  tff(f_39, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.70/1.45  tff(f_31, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l53_enumset1)).
% 2.70/1.45  tff(f_33, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_enumset1)).
% 2.70/1.45  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.70/1.45  tff(f_41, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.70/1.45  tff(f_37, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_enumset1)).
% 2.70/1.45  tff(f_46, negated_conjecture, ~(![A, B, C]: (k2_xboole_0(k2_tarski(B, A), k2_tarski(C, A)) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t137_enumset1)).
% 2.70/1.45  tff(c_10, plain, (![A_12, B_13, C_14]: (k2_xboole_0(k2_tarski(A_12, B_13), k1_tarski(C_14))=k1_enumset1(A_12, B_13, C_14))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.70/1.45  tff(c_14, plain, (![A_19]: (k2_tarski(A_19, A_19)=k1_tarski(A_19))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.70/1.45  tff(c_401, plain, (![A_57, B_58, C_59, D_60]: (k2_xboole_0(k2_tarski(A_57, B_58), k2_tarski(C_59, D_60))=k2_enumset1(A_57, B_58, C_59, D_60))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.70/1.45  tff(c_437, plain, (![A_57, B_58, A_19]: (k2_xboole_0(k2_tarski(A_57, B_58), k1_tarski(A_19))=k2_enumset1(A_57, B_58, A_19, A_19))), inference(superposition, [status(thm), theory('equality')], [c_14, c_401])).
% 2.70/1.45  tff(c_441, plain, (![A_57, B_58, A_19]: (k2_enumset1(A_57, B_58, A_19, A_19)=k1_enumset1(A_57, B_58, A_19))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_437])).
% 2.70/1.45  tff(c_8, plain, (![A_9, B_10, C_11]: (k2_xboole_0(k1_tarski(A_9), k2_tarski(B_10, C_11))=k1_enumset1(A_9, B_10, C_11))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.70/1.45  tff(c_170, plain, (![A_41, B_42, C_43]: (k2_xboole_0(k2_tarski(A_41, B_42), k1_tarski(C_43))=k1_enumset1(A_41, B_42, C_43))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.70/1.45  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.70/1.45  tff(c_535, plain, (![C_69, A_70, B_71]: (k2_xboole_0(k1_tarski(C_69), k2_tarski(A_70, B_71))=k1_enumset1(A_70, B_71, C_69))), inference(superposition, [status(thm), theory('equality')], [c_170, c_2])).
% 2.70/1.45  tff(c_576, plain, (![C_72, A_73, B_74]: (k1_enumset1(C_72, A_73, B_74)=k1_enumset1(A_73, B_74, C_72))), inference(superposition, [status(thm), theory('equality')], [c_535, c_8])).
% 2.70/1.45  tff(c_16, plain, (![A_20, B_21]: (k1_enumset1(A_20, A_20, B_21)=k2_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.70/1.45  tff(c_878, plain, (![C_84, B_85]: (k1_enumset1(C_84, B_85, B_85)=k2_tarski(B_85, C_84))), inference(superposition, [status(thm), theory('equality')], [c_576, c_16])).
% 2.70/1.45  tff(c_12, plain, (![A_15, B_16, C_17, D_18]: (k2_xboole_0(k1_tarski(A_15), k1_enumset1(B_16, C_17, D_18))=k2_enumset1(A_15, B_16, C_17, D_18))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.70/1.45  tff(c_902, plain, (![A_15, B_85, C_84]: (k2_xboole_0(k1_tarski(A_15), k2_tarski(B_85, C_84))=k2_enumset1(A_15, C_84, B_85, B_85))), inference(superposition, [status(thm), theory('equality')], [c_878, c_12])).
% 2.70/1.45  tff(c_953, plain, (![A_15, C_84, B_85]: (k1_enumset1(A_15, C_84, B_85)=k1_enumset1(A_15, B_85, C_84))), inference(demodulation, [status(thm), theory('equality')], [c_441, c_8, c_902])).
% 2.70/1.45  tff(c_541, plain, (![C_69, A_70, B_71]: (k1_enumset1(C_69, A_70, B_71)=k1_enumset1(A_70, B_71, C_69))), inference(superposition, [status(thm), theory('equality')], [c_535, c_8])).
% 2.70/1.45  tff(c_191, plain, (![A_19, C_43]: (k2_xboole_0(k1_tarski(A_19), k1_tarski(C_43))=k1_enumset1(A_19, A_19, C_43))), inference(superposition, [status(thm), theory('equality')], [c_14, c_170])).
% 2.70/1.45  tff(c_194, plain, (![A_19, C_43]: (k2_xboole_0(k1_tarski(A_19), k1_tarski(C_43))=k2_tarski(A_19, C_43))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_191])).
% 2.70/1.45  tff(c_91, plain, (![A_35, B_36, C_37]: (k2_xboole_0(k1_tarski(A_35), k2_tarski(B_36, C_37))=k1_enumset1(A_35, B_36, C_37))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.70/1.45  tff(c_112, plain, (![A_35, A_19]: (k2_xboole_0(k1_tarski(A_35), k1_tarski(A_19))=k1_enumset1(A_35, A_19, A_19))), inference(superposition, [status(thm), theory('equality')], [c_14, c_91])).
% 2.70/1.45  tff(c_224, plain, (![A_35, A_19]: (k1_enumset1(A_35, A_19, A_19)=k2_tarski(A_35, A_19))), inference(demodulation, [status(thm), theory('equality')], [c_194, c_112])).
% 2.70/1.45  tff(c_639, plain, (![C_75, A_76]: (k1_enumset1(C_75, A_76, C_75)=k2_tarski(A_76, C_75))), inference(superposition, [status(thm), theory('equality')], [c_576, c_224])).
% 2.70/1.45  tff(c_651, plain, (![A_15, A_76, C_75]: (k2_xboole_0(k1_tarski(A_15), k2_tarski(A_76, C_75))=k2_enumset1(A_15, C_75, A_76, C_75))), inference(superposition, [status(thm), theory('equality')], [c_639, c_12])).
% 2.70/1.45  tff(c_688, plain, (![A_15, C_75, A_76]: (k2_enumset1(A_15, C_75, A_76, C_75)=k1_enumset1(A_15, A_76, C_75))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_651])).
% 2.70/1.45  tff(c_6, plain, (![A_5, B_6, C_7, D_8]: (k2_xboole_0(k2_tarski(A_5, B_6), k2_tarski(C_7, D_8))=k2_enumset1(A_5, B_6, C_7, D_8))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.70/1.45  tff(c_20, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.70/1.45  tff(c_21, plain, (k2_enumset1('#skF_2', '#skF_1', '#skF_3', '#skF_1')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_20])).
% 2.70/1.45  tff(c_973, plain, (k2_enumset1('#skF_2', '#skF_1', '#skF_3', '#skF_1')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_953, c_21])).
% 2.70/1.45  tff(c_1454, plain, (k1_enumset1('#skF_2', '#skF_3', '#skF_1')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_688, c_973])).
% 2.70/1.45  tff(c_1457, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_953, c_541, c_541, c_1454])).
% 2.70/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.70/1.45  
% 2.70/1.45  Inference rules
% 2.70/1.45  ----------------------
% 2.70/1.45  #Ref     : 0
% 2.70/1.45  #Sup     : 355
% 2.70/1.45  #Fact    : 0
% 2.70/1.45  #Define  : 0
% 2.70/1.45  #Split   : 0
% 2.70/1.45  #Chain   : 0
% 2.70/1.45  #Close   : 0
% 2.70/1.45  
% 2.70/1.45  Ordering : KBO
% 2.70/1.45  
% 2.70/1.45  Simplification rules
% 2.70/1.45  ----------------------
% 2.70/1.45  #Subsume      : 67
% 2.70/1.45  #Demod        : 210
% 2.70/1.45  #Tautology    : 237
% 2.70/1.45  #SimpNegUnit  : 0
% 2.70/1.45  #BackRed      : 3
% 2.70/1.45  
% 2.70/1.45  #Partial instantiations: 0
% 2.70/1.45  #Strategies tried      : 1
% 2.70/1.45  
% 2.70/1.45  Timing (in seconds)
% 2.70/1.45  ----------------------
% 3.12/1.45  Preprocessing        : 0.26
% 3.12/1.45  Parsing              : 0.14
% 3.12/1.45  CNF conversion       : 0.01
% 3.12/1.45  Main loop            : 0.39
% 3.12/1.45  Inferencing          : 0.14
% 3.12/1.45  Reduction            : 0.16
% 3.12/1.45  Demodulation         : 0.14
% 3.12/1.45  BG Simplification    : 0.02
% 3.12/1.45  Subsumption          : 0.05
% 3.12/1.45  Abstraction          : 0.02
% 3.12/1.45  MUC search           : 0.00
% 3.12/1.45  Cooper               : 0.00
% 3.12/1.45  Total                : 0.68
% 3.12/1.45  Index Insertion      : 0.00
% 3.12/1.45  Index Deletion       : 0.00
% 3.12/1.45  Index Matching       : 0.00
% 3.12/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
