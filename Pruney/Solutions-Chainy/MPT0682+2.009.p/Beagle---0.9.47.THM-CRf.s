%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:29 EST 2020

% Result     : Theorem 1.98s
% Output     : CNFRefutation 1.98s
% Verified   : 
% Statistics : Number of formulae       :   52 (  64 expanded)
%              Number of leaves         :   32 (  39 expanded)
%              Depth                    :    9
%              Number of atoms          :   50 (  67 expanded)
%              Number of equality atoms :   24 (  28 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(f_73,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => k9_relat_1(k8_relat_1(A,C),B) = k3_xboole_0(A,k9_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_funct_1)).

tff(f_41,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_60,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_66,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k9_relat_1(k5_relat_1(B,C),A) = k9_relat_1(C,k9_relat_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t159_relat_1)).

tff(c_36,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_16,plain,(
    ! [A_30] : v1_relat_1(k6_relat_1(A_30)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_26,plain,(
    ! [A_39] : k2_relat_1(k6_relat_1(A_39)) = A_39 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_92,plain,(
    ! [B_56,A_57] :
      ( k5_relat_1(B_56,k6_relat_1(A_57)) = k8_relat_1(A_57,B_56)
      | ~ v1_relat_1(B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_30,plain,(
    ! [B_43,A_42] : k5_relat_1(k6_relat_1(B_43),k6_relat_1(A_42)) = k6_relat_1(k3_xboole_0(A_42,B_43)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_99,plain,(
    ! [A_57,B_43] :
      ( k8_relat_1(A_57,k6_relat_1(B_43)) = k6_relat_1(k3_xboole_0(A_57,B_43))
      | ~ v1_relat_1(k6_relat_1(B_43)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_30])).

tff(c_108,plain,(
    ! [A_57,B_43] : k8_relat_1(A_57,k6_relat_1(B_43)) = k6_relat_1(k3_xboole_0(A_57,B_43)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_99])).

tff(c_122,plain,(
    ! [A_60,B_61] :
      ( k5_relat_1(k6_relat_1(A_60),B_61) = k7_relat_1(B_61,A_60)
      | ~ v1_relat_1(B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_18,plain,(
    ! [B_32,A_31] :
      ( k5_relat_1(B_32,k6_relat_1(A_31)) = k8_relat_1(A_31,B_32)
      | ~ v1_relat_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_129,plain,(
    ! [A_31,A_60] :
      ( k8_relat_1(A_31,k6_relat_1(A_60)) = k7_relat_1(k6_relat_1(A_31),A_60)
      | ~ v1_relat_1(k6_relat_1(A_60))
      | ~ v1_relat_1(k6_relat_1(A_31)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_18])).

tff(c_146,plain,(
    ! [A_31,A_60] : k7_relat_1(k6_relat_1(A_31),A_60) = k6_relat_1(k3_xboole_0(A_31,A_60)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_16,c_108,c_129])).

tff(c_163,plain,(
    ! [B_64,A_65] :
      ( k2_relat_1(k7_relat_1(B_64,A_65)) = k9_relat_1(B_64,A_65)
      | ~ v1_relat_1(B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_172,plain,(
    ! [A_31,A_60] :
      ( k2_relat_1(k6_relat_1(k3_xboole_0(A_31,A_60))) = k9_relat_1(k6_relat_1(A_31),A_60)
      | ~ v1_relat_1(k6_relat_1(A_31)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_163])).

tff(c_176,plain,(
    ! [A_31,A_60] : k9_relat_1(k6_relat_1(A_31),A_60) = k3_xboole_0(A_31,A_60) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_26,c_172])).

tff(c_207,plain,(
    ! [B_77,C_78,A_79] :
      ( k9_relat_1(k5_relat_1(B_77,C_78),A_79) = k9_relat_1(C_78,k9_relat_1(B_77,A_79))
      | ~ v1_relat_1(C_78)
      | ~ v1_relat_1(B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_219,plain,(
    ! [A_31,B_32,A_79] :
      ( k9_relat_1(k6_relat_1(A_31),k9_relat_1(B_32,A_79)) = k9_relat_1(k8_relat_1(A_31,B_32),A_79)
      | ~ v1_relat_1(k6_relat_1(A_31))
      | ~ v1_relat_1(B_32)
      | ~ v1_relat_1(B_32) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_207])).

tff(c_248,plain,(
    ! [A_83,B_84,A_85] :
      ( k9_relat_1(k8_relat_1(A_83,B_84),A_85) = k3_xboole_0(A_83,k9_relat_1(B_84,A_85))
      | ~ v1_relat_1(B_84) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_176,c_219])).

tff(c_32,plain,(
    k9_relat_1(k8_relat_1('#skF_1','#skF_3'),'#skF_2') != k3_xboole_0('#skF_1',k9_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_254,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_248,c_32])).

tff(c_265,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_254])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:06:39 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.98/1.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.20  
% 1.98/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.20  %$ v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 1.98/1.20  
% 1.98/1.20  %Foreground sorts:
% 1.98/1.20  
% 1.98/1.20  
% 1.98/1.20  %Background operators:
% 1.98/1.20  
% 1.98/1.20  
% 1.98/1.20  %Foreground operators:
% 1.98/1.20  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.98/1.20  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.98/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.98/1.20  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.98/1.20  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.98/1.20  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.98/1.20  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.98/1.20  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.98/1.20  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.98/1.20  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.98/1.20  tff('#skF_2', type, '#skF_2': $i).
% 1.98/1.20  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.98/1.20  tff('#skF_3', type, '#skF_3': $i).
% 1.98/1.20  tff('#skF_1', type, '#skF_1': $i).
% 1.98/1.20  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.98/1.20  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.98/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.98/1.20  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.98/1.20  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.98/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.98/1.20  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.98/1.20  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.98/1.20  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.98/1.20  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.98/1.20  
% 1.98/1.21  tff(f_73, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (k9_relat_1(k8_relat_1(A, C), B) = k3_xboole_0(A, k9_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t126_funct_1)).
% 1.98/1.21  tff(f_41, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 1.98/1.21  tff(f_60, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 1.98/1.21  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_relat_1)).
% 1.98/1.21  tff(f_66, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 1.98/1.21  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 1.98/1.21  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 1.98/1.21  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k9_relat_1(k5_relat_1(B, C), A) = k9_relat_1(C, k9_relat_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t159_relat_1)).
% 1.98/1.21  tff(c_36, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_73])).
% 1.98/1.21  tff(c_16, plain, (![A_30]: (v1_relat_1(k6_relat_1(A_30)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.98/1.21  tff(c_26, plain, (![A_39]: (k2_relat_1(k6_relat_1(A_39))=A_39)), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.98/1.21  tff(c_92, plain, (![B_56, A_57]: (k5_relat_1(B_56, k6_relat_1(A_57))=k8_relat_1(A_57, B_56) | ~v1_relat_1(B_56))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.98/1.21  tff(c_30, plain, (![B_43, A_42]: (k5_relat_1(k6_relat_1(B_43), k6_relat_1(A_42))=k6_relat_1(k3_xboole_0(A_42, B_43)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.98/1.21  tff(c_99, plain, (![A_57, B_43]: (k8_relat_1(A_57, k6_relat_1(B_43))=k6_relat_1(k3_xboole_0(A_57, B_43)) | ~v1_relat_1(k6_relat_1(B_43)))), inference(superposition, [status(thm), theory('equality')], [c_92, c_30])).
% 1.98/1.21  tff(c_108, plain, (![A_57, B_43]: (k8_relat_1(A_57, k6_relat_1(B_43))=k6_relat_1(k3_xboole_0(A_57, B_43)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_99])).
% 1.98/1.21  tff(c_122, plain, (![A_60, B_61]: (k5_relat_1(k6_relat_1(A_60), B_61)=k7_relat_1(B_61, A_60) | ~v1_relat_1(B_61))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.98/1.21  tff(c_18, plain, (![B_32, A_31]: (k5_relat_1(B_32, k6_relat_1(A_31))=k8_relat_1(A_31, B_32) | ~v1_relat_1(B_32))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.98/1.21  tff(c_129, plain, (![A_31, A_60]: (k8_relat_1(A_31, k6_relat_1(A_60))=k7_relat_1(k6_relat_1(A_31), A_60) | ~v1_relat_1(k6_relat_1(A_60)) | ~v1_relat_1(k6_relat_1(A_31)))), inference(superposition, [status(thm), theory('equality')], [c_122, c_18])).
% 1.98/1.21  tff(c_146, plain, (![A_31, A_60]: (k7_relat_1(k6_relat_1(A_31), A_60)=k6_relat_1(k3_xboole_0(A_31, A_60)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_16, c_108, c_129])).
% 1.98/1.21  tff(c_163, plain, (![B_64, A_65]: (k2_relat_1(k7_relat_1(B_64, A_65))=k9_relat_1(B_64, A_65) | ~v1_relat_1(B_64))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.98/1.21  tff(c_172, plain, (![A_31, A_60]: (k2_relat_1(k6_relat_1(k3_xboole_0(A_31, A_60)))=k9_relat_1(k6_relat_1(A_31), A_60) | ~v1_relat_1(k6_relat_1(A_31)))), inference(superposition, [status(thm), theory('equality')], [c_146, c_163])).
% 1.98/1.21  tff(c_176, plain, (![A_31, A_60]: (k9_relat_1(k6_relat_1(A_31), A_60)=k3_xboole_0(A_31, A_60))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_26, c_172])).
% 1.98/1.21  tff(c_207, plain, (![B_77, C_78, A_79]: (k9_relat_1(k5_relat_1(B_77, C_78), A_79)=k9_relat_1(C_78, k9_relat_1(B_77, A_79)) | ~v1_relat_1(C_78) | ~v1_relat_1(B_77))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.98/1.21  tff(c_219, plain, (![A_31, B_32, A_79]: (k9_relat_1(k6_relat_1(A_31), k9_relat_1(B_32, A_79))=k9_relat_1(k8_relat_1(A_31, B_32), A_79) | ~v1_relat_1(k6_relat_1(A_31)) | ~v1_relat_1(B_32) | ~v1_relat_1(B_32))), inference(superposition, [status(thm), theory('equality')], [c_18, c_207])).
% 1.98/1.21  tff(c_248, plain, (![A_83, B_84, A_85]: (k9_relat_1(k8_relat_1(A_83, B_84), A_85)=k3_xboole_0(A_83, k9_relat_1(B_84, A_85)) | ~v1_relat_1(B_84))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_176, c_219])).
% 1.98/1.21  tff(c_32, plain, (k9_relat_1(k8_relat_1('#skF_1', '#skF_3'), '#skF_2')!=k3_xboole_0('#skF_1', k9_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_73])).
% 1.98/1.21  tff(c_254, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_248, c_32])).
% 1.98/1.21  tff(c_265, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_254])).
% 1.98/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.21  
% 1.98/1.21  Inference rules
% 1.98/1.21  ----------------------
% 1.98/1.21  #Ref     : 0
% 1.98/1.21  #Sup     : 48
% 1.98/1.21  #Fact    : 0
% 1.98/1.21  #Define  : 0
% 1.98/1.21  #Split   : 0
% 1.98/1.21  #Chain   : 0
% 1.98/1.21  #Close   : 0
% 1.98/1.21  
% 1.98/1.21  Ordering : KBO
% 1.98/1.21  
% 1.98/1.21  Simplification rules
% 1.98/1.21  ----------------------
% 1.98/1.21  #Subsume      : 0
% 1.98/1.21  #Demod        : 32
% 1.98/1.21  #Tautology    : 39
% 1.98/1.21  #SimpNegUnit  : 0
% 1.98/1.21  #BackRed      : 0
% 1.98/1.21  
% 1.98/1.21  #Partial instantiations: 0
% 1.98/1.21  #Strategies tried      : 1
% 1.98/1.21  
% 1.98/1.21  Timing (in seconds)
% 1.98/1.21  ----------------------
% 1.98/1.21  Preprocessing        : 0.33
% 1.98/1.21  Parsing              : 0.18
% 1.98/1.21  CNF conversion       : 0.02
% 1.98/1.21  Main loop            : 0.17
% 1.98/1.22  Inferencing          : 0.07
% 1.98/1.22  Reduction            : 0.06
% 1.98/1.22  Demodulation         : 0.04
% 1.98/1.22  BG Simplification    : 0.01
% 1.98/1.22  Subsumption          : 0.02
% 1.98/1.22  Abstraction          : 0.01
% 1.98/1.22  MUC search           : 0.00
% 1.98/1.22  Cooper               : 0.00
% 1.98/1.22  Total                : 0.53
% 1.98/1.22  Index Insertion      : 0.00
% 1.98/1.22  Index Deletion       : 0.00
% 1.98/1.22  Index Matching       : 0.00
% 1.98/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
