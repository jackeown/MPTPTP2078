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
% DateTime   : Thu Dec  3 10:03:34 EST 2020

% Result     : Theorem 1.99s
% Output     : CNFRefutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :   50 (  63 expanded)
%              Number of leaves         :   27 (  34 expanded)
%              Depth                    :    8
%              Number of atoms          :   54 (  70 expanded)
%              Number of equality atoms :   28 (  32 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_35,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_53,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_64,negated_conjecture,(
    ~ ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_10] : v1_relat_1(k6_relat_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_18,plain,(
    ! [A_18] : k1_relat_1(k6_relat_1(A_18)) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_47,plain,(
    ! [A_27] :
      ( k7_relat_1(A_27,k1_relat_1(A_27)) = A_27
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_56,plain,(
    ! [A_18] :
      ( k7_relat_1(k6_relat_1(A_18),A_18) = k6_relat_1(A_18)
      | ~ v1_relat_1(k6_relat_1(A_18)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_47])).

tff(c_60,plain,(
    ! [A_18] : k7_relat_1(k6_relat_1(A_18),A_18) = k6_relat_1(A_18) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_56])).

tff(c_188,plain,(
    ! [C_46,A_47,B_48] :
      ( k7_relat_1(k7_relat_1(C_46,A_47),B_48) = k7_relat_1(C_46,k3_xboole_0(A_47,B_48))
      | ~ v1_relat_1(C_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_210,plain,(
    ! [A_18,B_48] :
      ( k7_relat_1(k6_relat_1(A_18),k3_xboole_0(A_18,B_48)) = k7_relat_1(k6_relat_1(A_18),B_48)
      | ~ v1_relat_1(k6_relat_1(A_18)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_188])).

tff(c_224,plain,(
    ! [A_49,B_50] : k7_relat_1(k6_relat_1(A_49),k3_xboole_0(A_49,B_50)) = k7_relat_1(k6_relat_1(A_49),B_50) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_210])).

tff(c_102,plain,(
    ! [A_35,B_36] :
      ( k5_relat_1(k6_relat_1(A_35),B_36) = k7_relat_1(B_36,A_35)
      | ~ v1_relat_1(B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_14,plain,(
    ! [B_15,A_14] :
      ( k5_relat_1(B_15,k6_relat_1(A_14)) = k8_relat_1(A_14,B_15)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_112,plain,(
    ! [A_14,A_35] :
      ( k8_relat_1(A_14,k6_relat_1(A_35)) = k7_relat_1(k6_relat_1(A_14),A_35)
      | ~ v1_relat_1(k6_relat_1(A_35))
      | ~ v1_relat_1(k6_relat_1(A_14)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_14])).

tff(c_124,plain,(
    ! [A_14,A_35] : k8_relat_1(A_14,k6_relat_1(A_35)) = k7_relat_1(k6_relat_1(A_14),A_35) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_10,c_112])).

tff(c_20,plain,(
    ! [A_18] : k2_relat_1(k6_relat_1(A_18)) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_148,plain,(
    ! [A_42,B_43] :
      ( k8_relat_1(A_42,B_43) = B_43
      | ~ r1_tarski(k2_relat_1(B_43),A_42)
      | ~ v1_relat_1(B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_151,plain,(
    ! [A_42,A_18] :
      ( k8_relat_1(A_42,k6_relat_1(A_18)) = k6_relat_1(A_18)
      | ~ r1_tarski(A_18,A_42)
      | ~ v1_relat_1(k6_relat_1(A_18)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_148])).

tff(c_153,plain,(
    ! [A_42,A_18] :
      ( k7_relat_1(k6_relat_1(A_42),A_18) = k6_relat_1(A_18)
      | ~ r1_tarski(A_18,A_42) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_124,c_151])).

tff(c_233,plain,(
    ! [A_49,B_50] :
      ( k7_relat_1(k6_relat_1(A_49),B_50) = k6_relat_1(k3_xboole_0(A_49,B_50))
      | ~ r1_tarski(k3_xboole_0(A_49,B_50),A_49) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_224,c_153])).

tff(c_245,plain,(
    ! [A_49,B_50] : k7_relat_1(k6_relat_1(A_49),B_50) = k6_relat_1(k3_xboole_0(A_49,B_50)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_233])).

tff(c_26,plain,(
    k5_relat_1(k6_relat_1('#skF_2'),k6_relat_1('#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_108,plain,
    ( k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_26])).

tff(c_122,plain,(
    k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_108])).

tff(c_254,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_245,c_122])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:33:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.99/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.22  
% 1.99/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.22  %$ r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.08/1.22  
% 2.08/1.22  %Foreground sorts:
% 2.08/1.22  
% 2.08/1.22  
% 2.08/1.22  %Background operators:
% 2.08/1.22  
% 2.08/1.22  
% 2.08/1.22  %Foreground operators:
% 2.08/1.22  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.08/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.08/1.22  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.08/1.22  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.08/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.08/1.22  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.08/1.22  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.08/1.22  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.08/1.22  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.08/1.22  tff('#skF_2', type, '#skF_2': $i).
% 2.08/1.22  tff('#skF_1', type, '#skF_1': $i).
% 2.08/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.08/1.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.08/1.22  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.08/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.08/1.22  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.08/1.22  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.08/1.22  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.08/1.22  
% 2.10/1.24  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.10/1.24  tff(f_35, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.10/1.24  tff(f_53, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 2.10/1.24  tff(f_61, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_relat_1)).
% 2.10/1.24  tff(f_39, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_relat_1)).
% 2.10/1.24  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 2.10/1.24  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_relat_1)).
% 2.10/1.24  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_relat_1)).
% 2.10/1.24  tff(f_64, negated_conjecture, ~(![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 2.10/1.24  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.10/1.24  tff(c_10, plain, (![A_10]: (v1_relat_1(k6_relat_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.10/1.24  tff(c_18, plain, (![A_18]: (k1_relat_1(k6_relat_1(A_18))=A_18)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.10/1.24  tff(c_47, plain, (![A_27]: (k7_relat_1(A_27, k1_relat_1(A_27))=A_27 | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.10/1.24  tff(c_56, plain, (![A_18]: (k7_relat_1(k6_relat_1(A_18), A_18)=k6_relat_1(A_18) | ~v1_relat_1(k6_relat_1(A_18)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_47])).
% 2.10/1.24  tff(c_60, plain, (![A_18]: (k7_relat_1(k6_relat_1(A_18), A_18)=k6_relat_1(A_18))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_56])).
% 2.10/1.24  tff(c_188, plain, (![C_46, A_47, B_48]: (k7_relat_1(k7_relat_1(C_46, A_47), B_48)=k7_relat_1(C_46, k3_xboole_0(A_47, B_48)) | ~v1_relat_1(C_46))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.10/1.24  tff(c_210, plain, (![A_18, B_48]: (k7_relat_1(k6_relat_1(A_18), k3_xboole_0(A_18, B_48))=k7_relat_1(k6_relat_1(A_18), B_48) | ~v1_relat_1(k6_relat_1(A_18)))), inference(superposition, [status(thm), theory('equality')], [c_60, c_188])).
% 2.10/1.24  tff(c_224, plain, (![A_49, B_50]: (k7_relat_1(k6_relat_1(A_49), k3_xboole_0(A_49, B_50))=k7_relat_1(k6_relat_1(A_49), B_50))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_210])).
% 2.10/1.24  tff(c_102, plain, (![A_35, B_36]: (k5_relat_1(k6_relat_1(A_35), B_36)=k7_relat_1(B_36, A_35) | ~v1_relat_1(B_36))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.10/1.24  tff(c_14, plain, (![B_15, A_14]: (k5_relat_1(B_15, k6_relat_1(A_14))=k8_relat_1(A_14, B_15) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.10/1.24  tff(c_112, plain, (![A_14, A_35]: (k8_relat_1(A_14, k6_relat_1(A_35))=k7_relat_1(k6_relat_1(A_14), A_35) | ~v1_relat_1(k6_relat_1(A_35)) | ~v1_relat_1(k6_relat_1(A_14)))), inference(superposition, [status(thm), theory('equality')], [c_102, c_14])).
% 2.10/1.24  tff(c_124, plain, (![A_14, A_35]: (k8_relat_1(A_14, k6_relat_1(A_35))=k7_relat_1(k6_relat_1(A_14), A_35))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_10, c_112])).
% 2.10/1.24  tff(c_20, plain, (![A_18]: (k2_relat_1(k6_relat_1(A_18))=A_18)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.10/1.24  tff(c_148, plain, (![A_42, B_43]: (k8_relat_1(A_42, B_43)=B_43 | ~r1_tarski(k2_relat_1(B_43), A_42) | ~v1_relat_1(B_43))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.10/1.24  tff(c_151, plain, (![A_42, A_18]: (k8_relat_1(A_42, k6_relat_1(A_18))=k6_relat_1(A_18) | ~r1_tarski(A_18, A_42) | ~v1_relat_1(k6_relat_1(A_18)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_148])).
% 2.10/1.24  tff(c_153, plain, (![A_42, A_18]: (k7_relat_1(k6_relat_1(A_42), A_18)=k6_relat_1(A_18) | ~r1_tarski(A_18, A_42))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_124, c_151])).
% 2.10/1.24  tff(c_233, plain, (![A_49, B_50]: (k7_relat_1(k6_relat_1(A_49), B_50)=k6_relat_1(k3_xboole_0(A_49, B_50)) | ~r1_tarski(k3_xboole_0(A_49, B_50), A_49))), inference(superposition, [status(thm), theory('equality')], [c_224, c_153])).
% 2.10/1.24  tff(c_245, plain, (![A_49, B_50]: (k7_relat_1(k6_relat_1(A_49), B_50)=k6_relat_1(k3_xboole_0(A_49, B_50)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_233])).
% 2.10/1.24  tff(c_26, plain, (k5_relat_1(k6_relat_1('#skF_2'), k6_relat_1('#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.10/1.24  tff(c_108, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_102, c_26])).
% 2.10/1.24  tff(c_122, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_108])).
% 2.10/1.24  tff(c_254, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_245, c_122])).
% 2.10/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.24  
% 2.10/1.24  Inference rules
% 2.10/1.24  ----------------------
% 2.10/1.24  #Ref     : 0
% 2.10/1.24  #Sup     : 47
% 2.10/1.24  #Fact    : 0
% 2.10/1.24  #Define  : 0
% 2.10/1.24  #Split   : 1
% 2.10/1.24  #Chain   : 0
% 2.10/1.24  #Close   : 0
% 2.10/1.24  
% 2.10/1.24  Ordering : KBO
% 2.10/1.24  
% 2.10/1.24  Simplification rules
% 2.10/1.24  ----------------------
% 2.10/1.24  #Subsume      : 1
% 2.10/1.24  #Demod        : 26
% 2.10/1.24  #Tautology    : 31
% 2.10/1.24  #SimpNegUnit  : 0
% 2.10/1.24  #BackRed      : 5
% 2.10/1.24  
% 2.10/1.24  #Partial instantiations: 0
% 2.10/1.24  #Strategies tried      : 1
% 2.10/1.24  
% 2.10/1.24  Timing (in seconds)
% 2.10/1.24  ----------------------
% 2.10/1.24  Preprocessing        : 0.30
% 2.10/1.24  Parsing              : 0.16
% 2.10/1.24  CNF conversion       : 0.02
% 2.10/1.24  Main loop            : 0.18
% 2.10/1.24  Inferencing          : 0.07
% 2.10/1.24  Reduction            : 0.06
% 2.10/1.24  Demodulation         : 0.04
% 2.10/1.24  BG Simplification    : 0.01
% 2.10/1.24  Subsumption          : 0.02
% 2.10/1.24  Abstraction          : 0.02
% 2.10/1.24  MUC search           : 0.00
% 2.10/1.24  Cooper               : 0.00
% 2.10/1.24  Total                : 0.51
% 2.10/1.24  Index Insertion      : 0.00
% 2.10/1.24  Index Deletion       : 0.00
% 2.10/1.24  Index Matching       : 0.00
% 2.10/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
