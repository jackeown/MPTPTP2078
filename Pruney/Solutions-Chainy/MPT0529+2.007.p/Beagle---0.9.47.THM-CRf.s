%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:12 EST 2020

% Result     : Theorem 2.99s
% Output     : CNFRefutation 3.14s
% Verified   : 
% Statistics : Number of formulae       :   52 (  61 expanded)
%              Number of leaves         :   28 (  34 expanded)
%              Depth                    :    9
%              Number of atoms          :   51 (  66 expanded)
%              Number of equality atoms :   27 (  36 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_66,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k8_relat_1(B,k8_relat_1(A,C)) = k8_relat_1(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_relat_1)).

tff(f_59,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_41,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k8_relat_1(A,B)) = k3_xboole_0(k2_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_39,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k8_relat_1(A,k8_relat_1(B,C)) = k8_relat_1(k3_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_relat_1)).

tff(c_32,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_30,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_26,plain,(
    ! [A_33] : k2_relat_1(k6_relat_1(A_33)) = A_33 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_16,plain,(
    ! [A_25] : v1_relat_1(k6_relat_1(A_25)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_203,plain,(
    ! [A_52,B_53] :
      ( k8_relat_1(A_52,B_53) = B_53
      | ~ r1_tarski(k2_relat_1(B_53),A_52)
      | ~ v1_relat_1(B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_206,plain,(
    ! [A_52,A_33] :
      ( k8_relat_1(A_52,k6_relat_1(A_33)) = k6_relat_1(A_33)
      | ~ r1_tarski(A_33,A_52)
      | ~ v1_relat_1(k6_relat_1(A_33)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_203])).

tff(c_224,plain,(
    ! [A_56,A_57] :
      ( k8_relat_1(A_56,k6_relat_1(A_57)) = k6_relat_1(A_57)
      | ~ r1_tarski(A_57,A_56) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_206])).

tff(c_175,plain,(
    ! [B_50,A_51] :
      ( k3_xboole_0(k2_relat_1(B_50),A_51) = k2_relat_1(k8_relat_1(A_51,B_50))
      | ~ v1_relat_1(B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_198,plain,(
    ! [A_51,A_33] :
      ( k2_relat_1(k8_relat_1(A_51,k6_relat_1(A_33))) = k3_xboole_0(A_33,A_51)
      | ~ v1_relat_1(k6_relat_1(A_33)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_175])).

tff(c_202,plain,(
    ! [A_51,A_33] : k2_relat_1(k8_relat_1(A_51,k6_relat_1(A_33))) = k3_xboole_0(A_33,A_51) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_198])).

tff(c_230,plain,(
    ! [A_57,A_56] :
      ( k3_xboole_0(A_57,A_56) = k2_relat_1(k6_relat_1(A_57))
      | ~ r1_tarski(A_57,A_56) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_224,c_202])).

tff(c_237,plain,(
    ! [A_58,A_59] :
      ( k3_xboole_0(A_58,A_59) = A_58
      | ~ r1_tarski(A_58,A_59) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_230])).

tff(c_241,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_30,c_237])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_tarski(B_2,A_1) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_94,plain,(
    ! [A_41,B_42] : k1_setfam_1(k2_tarski(A_41,B_42)) = k3_xboole_0(A_41,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_109,plain,(
    ! [B_43,A_44] : k1_setfam_1(k2_tarski(B_43,A_44)) = k3_xboole_0(A_44,B_43) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_94])).

tff(c_14,plain,(
    ! [A_23,B_24] : k1_setfam_1(k2_tarski(A_23,B_24)) = k3_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_115,plain,(
    ! [B_43,A_44] : k3_xboole_0(B_43,A_44) = k3_xboole_0(A_44,B_43) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_14])).

tff(c_294,plain,(
    ! [A_66,B_67,C_68] :
      ( k8_relat_1(k3_xboole_0(A_66,B_67),C_68) = k8_relat_1(A_66,k8_relat_1(B_67,C_68))
      | ~ v1_relat_1(C_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_774,plain,(
    ! [B_101,A_102,C_103] :
      ( k8_relat_1(k3_xboole_0(B_101,A_102),C_103) = k8_relat_1(A_102,k8_relat_1(B_101,C_103))
      | ~ v1_relat_1(C_103) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_294])).

tff(c_1092,plain,(
    ! [C_107] :
      ( k8_relat_1('#skF_2',k8_relat_1('#skF_1',C_107)) = k8_relat_1('#skF_1',C_107)
      | ~ v1_relat_1(C_107) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_241,c_774])).

tff(c_28,plain,(
    k8_relat_1('#skF_2',k8_relat_1('#skF_1','#skF_3')) != k8_relat_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1108,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1092,c_28])).

tff(c_1126,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1108])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:17:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.99/1.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.99/1.46  
% 2.99/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.99/1.47  %$ r1_tarski > v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.99/1.47  
% 2.99/1.47  %Foreground sorts:
% 2.99/1.47  
% 2.99/1.47  
% 2.99/1.47  %Background operators:
% 2.99/1.47  
% 2.99/1.47  
% 2.99/1.47  %Foreground operators:
% 2.99/1.47  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.99/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.99/1.47  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.99/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.99/1.47  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.99/1.47  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.99/1.47  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.99/1.47  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.99/1.47  tff('#skF_2', type, '#skF_2': $i).
% 2.99/1.47  tff('#skF_3', type, '#skF_3': $i).
% 2.99/1.47  tff('#skF_1', type, '#skF_1': $i).
% 2.99/1.47  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.99/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.99/1.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.99/1.47  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.99/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.99/1.47  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.99/1.47  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.99/1.47  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.99/1.47  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.99/1.47  
% 3.14/1.48  tff(f_66, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k8_relat_1(B, k8_relat_1(A, C)) = k8_relat_1(A, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t129_relat_1)).
% 3.14/1.48  tff(f_59, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 3.14/1.48  tff(f_41, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 3.14/1.48  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_relat_1)).
% 3.14/1.48  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k8_relat_1(A, B)) = k3_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t119_relat_1)).
% 3.14/1.48  tff(f_27, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.14/1.48  tff(f_39, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.14/1.48  tff(f_55, axiom, (![A, B, C]: (v1_relat_1(C) => (k8_relat_1(A, k8_relat_1(B, C)) = k8_relat_1(k3_xboole_0(A, B), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t127_relat_1)).
% 3.14/1.48  tff(c_32, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.14/1.48  tff(c_30, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.14/1.48  tff(c_26, plain, (![A_33]: (k2_relat_1(k6_relat_1(A_33))=A_33)), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.14/1.48  tff(c_16, plain, (![A_25]: (v1_relat_1(k6_relat_1(A_25)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.14/1.48  tff(c_203, plain, (![A_52, B_53]: (k8_relat_1(A_52, B_53)=B_53 | ~r1_tarski(k2_relat_1(B_53), A_52) | ~v1_relat_1(B_53))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.14/1.48  tff(c_206, plain, (![A_52, A_33]: (k8_relat_1(A_52, k6_relat_1(A_33))=k6_relat_1(A_33) | ~r1_tarski(A_33, A_52) | ~v1_relat_1(k6_relat_1(A_33)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_203])).
% 3.14/1.48  tff(c_224, plain, (![A_56, A_57]: (k8_relat_1(A_56, k6_relat_1(A_57))=k6_relat_1(A_57) | ~r1_tarski(A_57, A_56))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_206])).
% 3.14/1.48  tff(c_175, plain, (![B_50, A_51]: (k3_xboole_0(k2_relat_1(B_50), A_51)=k2_relat_1(k8_relat_1(A_51, B_50)) | ~v1_relat_1(B_50))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.14/1.48  tff(c_198, plain, (![A_51, A_33]: (k2_relat_1(k8_relat_1(A_51, k6_relat_1(A_33)))=k3_xboole_0(A_33, A_51) | ~v1_relat_1(k6_relat_1(A_33)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_175])).
% 3.14/1.48  tff(c_202, plain, (![A_51, A_33]: (k2_relat_1(k8_relat_1(A_51, k6_relat_1(A_33)))=k3_xboole_0(A_33, A_51))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_198])).
% 3.14/1.48  tff(c_230, plain, (![A_57, A_56]: (k3_xboole_0(A_57, A_56)=k2_relat_1(k6_relat_1(A_57)) | ~r1_tarski(A_57, A_56))), inference(superposition, [status(thm), theory('equality')], [c_224, c_202])).
% 3.14/1.48  tff(c_237, plain, (![A_58, A_59]: (k3_xboole_0(A_58, A_59)=A_58 | ~r1_tarski(A_58, A_59))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_230])).
% 3.14/1.48  tff(c_241, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_30, c_237])).
% 3.14/1.48  tff(c_2, plain, (![B_2, A_1]: (k2_tarski(B_2, A_1)=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.14/1.48  tff(c_94, plain, (![A_41, B_42]: (k1_setfam_1(k2_tarski(A_41, B_42))=k3_xboole_0(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.14/1.48  tff(c_109, plain, (![B_43, A_44]: (k1_setfam_1(k2_tarski(B_43, A_44))=k3_xboole_0(A_44, B_43))), inference(superposition, [status(thm), theory('equality')], [c_2, c_94])).
% 3.14/1.48  tff(c_14, plain, (![A_23, B_24]: (k1_setfam_1(k2_tarski(A_23, B_24))=k3_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.14/1.48  tff(c_115, plain, (![B_43, A_44]: (k3_xboole_0(B_43, A_44)=k3_xboole_0(A_44, B_43))), inference(superposition, [status(thm), theory('equality')], [c_109, c_14])).
% 3.14/1.48  tff(c_294, plain, (![A_66, B_67, C_68]: (k8_relat_1(k3_xboole_0(A_66, B_67), C_68)=k8_relat_1(A_66, k8_relat_1(B_67, C_68)) | ~v1_relat_1(C_68))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.14/1.48  tff(c_774, plain, (![B_101, A_102, C_103]: (k8_relat_1(k3_xboole_0(B_101, A_102), C_103)=k8_relat_1(A_102, k8_relat_1(B_101, C_103)) | ~v1_relat_1(C_103))), inference(superposition, [status(thm), theory('equality')], [c_115, c_294])).
% 3.14/1.48  tff(c_1092, plain, (![C_107]: (k8_relat_1('#skF_2', k8_relat_1('#skF_1', C_107))=k8_relat_1('#skF_1', C_107) | ~v1_relat_1(C_107))), inference(superposition, [status(thm), theory('equality')], [c_241, c_774])).
% 3.14/1.48  tff(c_28, plain, (k8_relat_1('#skF_2', k8_relat_1('#skF_1', '#skF_3'))!=k8_relat_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.14/1.48  tff(c_1108, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1092, c_28])).
% 3.14/1.48  tff(c_1126, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_1108])).
% 3.14/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.14/1.48  
% 3.14/1.48  Inference rules
% 3.14/1.48  ----------------------
% 3.14/1.48  #Ref     : 0
% 3.14/1.48  #Sup     : 291
% 3.14/1.48  #Fact    : 0
% 3.14/1.48  #Define  : 0
% 3.14/1.48  #Split   : 0
% 3.14/1.48  #Chain   : 0
% 3.14/1.48  #Close   : 0
% 3.14/1.48  
% 3.14/1.48  Ordering : KBO
% 3.14/1.48  
% 3.14/1.48  Simplification rules
% 3.14/1.48  ----------------------
% 3.14/1.48  #Subsume      : 43
% 3.14/1.48  #Demod        : 38
% 3.14/1.48  #Tautology    : 83
% 3.14/1.48  #SimpNegUnit  : 0
% 3.14/1.48  #BackRed      : 0
% 3.14/1.48  
% 3.14/1.48  #Partial instantiations: 0
% 3.14/1.48  #Strategies tried      : 1
% 3.14/1.48  
% 3.14/1.48  Timing (in seconds)
% 3.14/1.48  ----------------------
% 3.14/1.48  Preprocessing        : 0.31
% 3.14/1.48  Parsing              : 0.17
% 3.14/1.48  CNF conversion       : 0.02
% 3.14/1.48  Main loop            : 0.41
% 3.14/1.48  Inferencing          : 0.16
% 3.14/1.48  Reduction            : 0.14
% 3.14/1.48  Demodulation         : 0.12
% 3.14/1.48  BG Simplification    : 0.03
% 3.14/1.48  Subsumption          : 0.06
% 3.14/1.48  Abstraction          : 0.03
% 3.14/1.48  MUC search           : 0.00
% 3.14/1.48  Cooper               : 0.00
% 3.14/1.48  Total                : 0.74
% 3.14/1.48  Index Insertion      : 0.00
% 3.14/1.48  Index Deletion       : 0.00
% 3.14/1.48  Index Matching       : 0.00
% 3.14/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
