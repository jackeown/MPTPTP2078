%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:27 EST 2020

% Result     : Theorem 1.99s
% Output     : CNFRefutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :   47 (  61 expanded)
%              Number of leaves         :   26 (  32 expanded)
%              Depth                    :    9
%              Number of atoms          :   40 (  55 expanded)
%              Number of equality atoms :   39 (  54 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_33,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_48,axiom,(
    ! [A,B] : k4_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_60,axiom,(
    ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_35,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_58,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & k1_setfam_1(k2_xboole_0(A,B)) != k3_xboole_0(k1_setfam_1(A),k1_setfam_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_setfam_1)).

tff(f_63,negated_conjecture,(
    ~ ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_8,plain,(
    ! [A_12] : k2_tarski(A_12,A_12) = k1_tarski(A_12) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_47,plain,(
    ! [A_31,B_32] : k4_xboole_0(k1_tarski(A_31),k2_tarski(A_31,B_32)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_54,plain,(
    ! [A_12] : k4_xboole_0(k1_tarski(A_12),k1_tarski(A_12)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_47])).

tff(c_18,plain,(
    ! [B_23] : k4_xboole_0(k1_tarski(B_23),k1_tarski(B_23)) != k1_tarski(B_23) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_73,plain,(
    ! [B_23] : k1_tarski(B_23) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_18])).

tff(c_26,plain,(
    ! [A_28] : k1_setfam_1(k1_tarski(A_28)) = A_28 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_10,plain,(
    ! [A_13,B_14] : k1_enumset1(A_13,A_13,B_14) = k2_tarski(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_15,B_16,C_17] : k2_enumset1(A_15,A_15,B_16,C_17) = k1_enumset1(A_15,B_16,C_17) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_180,plain,(
    ! [A_51,B_52,C_53,D_54] : k2_xboole_0(k1_enumset1(A_51,B_52,C_53),k1_tarski(D_54)) = k2_enumset1(A_51,B_52,C_53,D_54) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_189,plain,(
    ! [A_13,B_14,D_54] : k2_xboole_0(k2_tarski(A_13,B_14),k1_tarski(D_54)) = k2_enumset1(A_13,A_13,B_14,D_54) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_180])).

tff(c_193,plain,(
    ! [A_55,B_56,D_57] : k2_xboole_0(k2_tarski(A_55,B_56),k1_tarski(D_57)) = k1_enumset1(A_55,B_56,D_57) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_189])).

tff(c_202,plain,(
    ! [A_12,D_57] : k2_xboole_0(k1_tarski(A_12),k1_tarski(D_57)) = k1_enumset1(A_12,A_12,D_57) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_193])).

tff(c_205,plain,(
    ! [A_12,D_57] : k2_xboole_0(k1_tarski(A_12),k1_tarski(D_57)) = k2_tarski(A_12,D_57) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_202])).

tff(c_225,plain,(
    ! [A_60,B_61] :
      ( k3_xboole_0(k1_setfam_1(A_60),k1_setfam_1(B_61)) = k1_setfam_1(k2_xboole_0(A_60,B_61))
      | k1_xboole_0 = B_61
      | k1_xboole_0 = A_60 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_237,plain,(
    ! [A_28,B_61] :
      ( k1_setfam_1(k2_xboole_0(k1_tarski(A_28),B_61)) = k3_xboole_0(A_28,k1_setfam_1(B_61))
      | k1_xboole_0 = B_61
      | k1_tarski(A_28) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_225])).

tff(c_255,plain,(
    ! [A_63,B_64] :
      ( k1_setfam_1(k2_xboole_0(k1_tarski(A_63),B_64)) = k3_xboole_0(A_63,k1_setfam_1(B_64))
      | k1_xboole_0 = B_64 ) ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_237])).

tff(c_270,plain,(
    ! [A_12,D_57] :
      ( k3_xboole_0(A_12,k1_setfam_1(k1_tarski(D_57))) = k1_setfam_1(k2_tarski(A_12,D_57))
      | k1_tarski(D_57) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_205,c_255])).

tff(c_277,plain,(
    ! [A_12,D_57] :
      ( k1_setfam_1(k2_tarski(A_12,D_57)) = k3_xboole_0(A_12,D_57)
      | k1_tarski(D_57) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_270])).

tff(c_278,plain,(
    ! [A_12,D_57] : k1_setfam_1(k2_tarski(A_12,D_57)) = k3_xboole_0(A_12,D_57) ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_277])).

tff(c_28,plain,(
    k1_setfam_1(k2_tarski('#skF_1','#skF_2')) != k3_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_334,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_278,c_28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:30:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.99/1.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.20  
% 1.99/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.21  %$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.99/1.21  
% 1.99/1.21  %Foreground sorts:
% 1.99/1.21  
% 1.99/1.21  
% 1.99/1.21  %Background operators:
% 1.99/1.21  
% 1.99/1.21  
% 1.99/1.21  %Foreground operators:
% 1.99/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.99/1.21  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.99/1.21  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.99/1.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.99/1.21  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.99/1.21  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.99/1.21  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.99/1.21  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.99/1.21  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.99/1.21  tff('#skF_2', type, '#skF_2': $i).
% 1.99/1.21  tff('#skF_1', type, '#skF_1': $i).
% 1.99/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.99/1.21  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.99/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.99/1.21  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.99/1.21  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.99/1.21  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.99/1.21  
% 1.99/1.22  tff(f_33, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.99/1.22  tff(f_48, axiom, (![A, B]: (k4_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_zfmisc_1)).
% 1.99/1.22  tff(f_46, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 1.99/1.22  tff(f_60, axiom, (![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_setfam_1)).
% 1.99/1.22  tff(f_35, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 1.99/1.22  tff(f_37, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 1.99/1.22  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_enumset1)).
% 1.99/1.22  tff(f_58, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(k1_setfam_1(k2_xboole_0(A, B)) = k3_xboole_0(k1_setfam_1(A), k1_setfam_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_setfam_1)).
% 1.99/1.22  tff(f_63, negated_conjecture, ~(![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 1.99/1.22  tff(c_8, plain, (![A_12]: (k2_tarski(A_12, A_12)=k1_tarski(A_12))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.99/1.22  tff(c_47, plain, (![A_31, B_32]: (k4_xboole_0(k1_tarski(A_31), k2_tarski(A_31, B_32))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.99/1.22  tff(c_54, plain, (![A_12]: (k4_xboole_0(k1_tarski(A_12), k1_tarski(A_12))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8, c_47])).
% 1.99/1.22  tff(c_18, plain, (![B_23]: (k4_xboole_0(k1_tarski(B_23), k1_tarski(B_23))!=k1_tarski(B_23))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.99/1.22  tff(c_73, plain, (![B_23]: (k1_tarski(B_23)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_54, c_18])).
% 1.99/1.22  tff(c_26, plain, (![A_28]: (k1_setfam_1(k1_tarski(A_28))=A_28)), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.99/1.22  tff(c_10, plain, (![A_13, B_14]: (k1_enumset1(A_13, A_13, B_14)=k2_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.99/1.22  tff(c_12, plain, (![A_15, B_16, C_17]: (k2_enumset1(A_15, A_15, B_16, C_17)=k1_enumset1(A_15, B_16, C_17))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.99/1.22  tff(c_180, plain, (![A_51, B_52, C_53, D_54]: (k2_xboole_0(k1_enumset1(A_51, B_52, C_53), k1_tarski(D_54))=k2_enumset1(A_51, B_52, C_53, D_54))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.99/1.22  tff(c_189, plain, (![A_13, B_14, D_54]: (k2_xboole_0(k2_tarski(A_13, B_14), k1_tarski(D_54))=k2_enumset1(A_13, A_13, B_14, D_54))), inference(superposition, [status(thm), theory('equality')], [c_10, c_180])).
% 1.99/1.22  tff(c_193, plain, (![A_55, B_56, D_57]: (k2_xboole_0(k2_tarski(A_55, B_56), k1_tarski(D_57))=k1_enumset1(A_55, B_56, D_57))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_189])).
% 1.99/1.22  tff(c_202, plain, (![A_12, D_57]: (k2_xboole_0(k1_tarski(A_12), k1_tarski(D_57))=k1_enumset1(A_12, A_12, D_57))), inference(superposition, [status(thm), theory('equality')], [c_8, c_193])).
% 1.99/1.22  tff(c_205, plain, (![A_12, D_57]: (k2_xboole_0(k1_tarski(A_12), k1_tarski(D_57))=k2_tarski(A_12, D_57))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_202])).
% 1.99/1.22  tff(c_225, plain, (![A_60, B_61]: (k3_xboole_0(k1_setfam_1(A_60), k1_setfam_1(B_61))=k1_setfam_1(k2_xboole_0(A_60, B_61)) | k1_xboole_0=B_61 | k1_xboole_0=A_60)), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.99/1.22  tff(c_237, plain, (![A_28, B_61]: (k1_setfam_1(k2_xboole_0(k1_tarski(A_28), B_61))=k3_xboole_0(A_28, k1_setfam_1(B_61)) | k1_xboole_0=B_61 | k1_tarski(A_28)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_26, c_225])).
% 1.99/1.22  tff(c_255, plain, (![A_63, B_64]: (k1_setfam_1(k2_xboole_0(k1_tarski(A_63), B_64))=k3_xboole_0(A_63, k1_setfam_1(B_64)) | k1_xboole_0=B_64)), inference(negUnitSimplification, [status(thm)], [c_73, c_237])).
% 1.99/1.22  tff(c_270, plain, (![A_12, D_57]: (k3_xboole_0(A_12, k1_setfam_1(k1_tarski(D_57)))=k1_setfam_1(k2_tarski(A_12, D_57)) | k1_tarski(D_57)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_205, c_255])).
% 1.99/1.22  tff(c_277, plain, (![A_12, D_57]: (k1_setfam_1(k2_tarski(A_12, D_57))=k3_xboole_0(A_12, D_57) | k1_tarski(D_57)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_270])).
% 1.99/1.22  tff(c_278, plain, (![A_12, D_57]: (k1_setfam_1(k2_tarski(A_12, D_57))=k3_xboole_0(A_12, D_57))), inference(negUnitSimplification, [status(thm)], [c_73, c_277])).
% 1.99/1.22  tff(c_28, plain, (k1_setfam_1(k2_tarski('#skF_1', '#skF_2'))!=k3_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.99/1.22  tff(c_334, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_278, c_28])).
% 1.99/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.22  
% 1.99/1.22  Inference rules
% 1.99/1.22  ----------------------
% 1.99/1.22  #Ref     : 0
% 1.99/1.22  #Sup     : 70
% 1.99/1.22  #Fact    : 0
% 1.99/1.22  #Define  : 0
% 1.99/1.22  #Split   : 0
% 1.99/1.22  #Chain   : 0
% 1.99/1.22  #Close   : 0
% 1.99/1.22  
% 1.99/1.22  Ordering : KBO
% 1.99/1.22  
% 1.99/1.22  Simplification rules
% 1.99/1.22  ----------------------
% 1.99/1.22  #Subsume      : 0
% 1.99/1.22  #Demod        : 18
% 1.99/1.22  #Tautology    : 53
% 1.99/1.22  #SimpNegUnit  : 6
% 1.99/1.22  #BackRed      : 1
% 1.99/1.22  
% 1.99/1.22  #Partial instantiations: 0
% 1.99/1.22  #Strategies tried      : 1
% 1.99/1.22  
% 1.99/1.22  Timing (in seconds)
% 1.99/1.22  ----------------------
% 2.10/1.22  Preprocessing        : 0.29
% 2.10/1.22  Parsing              : 0.16
% 2.10/1.22  CNF conversion       : 0.02
% 2.10/1.22  Main loop            : 0.17
% 2.10/1.22  Inferencing          : 0.07
% 2.10/1.22  Reduction            : 0.06
% 2.10/1.22  Demodulation         : 0.04
% 2.10/1.22  BG Simplification    : 0.01
% 2.10/1.22  Subsumption          : 0.02
% 2.10/1.22  Abstraction          : 0.01
% 2.10/1.22  MUC search           : 0.00
% 2.10/1.22  Cooper               : 0.00
% 2.10/1.22  Total                : 0.49
% 2.10/1.22  Index Insertion      : 0.00
% 2.10/1.22  Index Deletion       : 0.00
% 2.10/1.22  Index Matching       : 0.00
% 2.10/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
