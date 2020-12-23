%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:36 EST 2020

% Result     : Theorem 1.96s
% Output     : CNFRefutation 2.15s
% Verified   : 
% Statistics : Number of formulae       :   52 (  65 expanded)
%              Number of leaves         :   29 (  36 expanded)
%              Depth                    :    8
%              Number of atoms          :   58 (  85 expanded)
%              Number of equality atoms :   27 (  29 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v4_relat_1(k6_relat_1(A),A)
      & v5_relat_1(k6_relat_1(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc24_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_57,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_70,negated_conjecture,(
    ~ ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_24,plain,(
    ! [A_22] : v1_relat_1(k6_relat_1(A_22)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_26,plain,(
    ! [A_22] : v4_relat_1(k6_relat_1(A_22),A_22) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_85,plain,(
    ! [B_36,A_37] :
      ( k7_relat_1(B_36,A_37) = B_36
      | ~ v4_relat_1(B_36,A_37)
      | ~ v1_relat_1(B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_88,plain,(
    ! [A_22] :
      ( k7_relat_1(k6_relat_1(A_22),A_22) = k6_relat_1(A_22)
      | ~ v1_relat_1(k6_relat_1(A_22)) ) ),
    inference(resolution,[status(thm)],[c_26,c_85])).

tff(c_91,plain,(
    ! [A_22] : k7_relat_1(k6_relat_1(A_22),A_22) = k6_relat_1(A_22) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_88])).

tff(c_153,plain,(
    ! [C_48,A_49,B_50] :
      ( k7_relat_1(k7_relat_1(C_48,A_49),B_50) = k7_relat_1(C_48,k3_xboole_0(A_49,B_50))
      | ~ v1_relat_1(C_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_168,plain,(
    ! [A_22,B_50] :
      ( k7_relat_1(k6_relat_1(A_22),k3_xboole_0(A_22,B_50)) = k7_relat_1(k6_relat_1(A_22),B_50)
      | ~ v1_relat_1(k6_relat_1(A_22)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_153])).

tff(c_200,plain,(
    ! [A_53,B_54] : k7_relat_1(k6_relat_1(A_53),k3_xboole_0(A_53,B_54)) = k7_relat_1(k6_relat_1(A_53),B_54) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_168])).

tff(c_101,plain,(
    ! [B_39,A_40] :
      ( k5_relat_1(B_39,k6_relat_1(A_40)) = k8_relat_1(A_40,B_39)
      | ~ v1_relat_1(B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_22,plain,(
    ! [A_20,B_21] :
      ( k5_relat_1(k6_relat_1(A_20),B_21) = k7_relat_1(B_21,A_20)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_111,plain,(
    ! [A_40,A_20] :
      ( k8_relat_1(A_40,k6_relat_1(A_20)) = k7_relat_1(k6_relat_1(A_40),A_20)
      | ~ v1_relat_1(k6_relat_1(A_40))
      | ~ v1_relat_1(k6_relat_1(A_20)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_22])).

tff(c_123,plain,(
    ! [A_40,A_20] : k8_relat_1(A_40,k6_relat_1(A_20)) = k7_relat_1(k6_relat_1(A_40),A_20) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_24,c_111])).

tff(c_20,plain,(
    ! [A_19] : k2_relat_1(k6_relat_1(A_19)) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_147,plain,(
    ! [A_46,B_47] :
      ( k8_relat_1(A_46,B_47) = B_47
      | ~ r1_tarski(k2_relat_1(B_47),A_46)
      | ~ v1_relat_1(B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_150,plain,(
    ! [A_46,A_19] :
      ( k8_relat_1(A_46,k6_relat_1(A_19)) = k6_relat_1(A_19)
      | ~ r1_tarski(A_19,A_46)
      | ~ v1_relat_1(k6_relat_1(A_19)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_147])).

tff(c_152,plain,(
    ! [A_46,A_19] :
      ( k7_relat_1(k6_relat_1(A_46),A_19) = k6_relat_1(A_19)
      | ~ r1_tarski(A_19,A_46) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_123,c_150])).

tff(c_206,plain,(
    ! [A_53,B_54] :
      ( k7_relat_1(k6_relat_1(A_53),B_54) = k6_relat_1(k3_xboole_0(A_53,B_54))
      | ~ r1_tarski(k3_xboole_0(A_53,B_54),A_53) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_200,c_152])).

tff(c_219,plain,(
    ! [A_53,B_54] : k7_relat_1(k6_relat_1(A_53),B_54) = k6_relat_1(k3_xboole_0(A_53,B_54)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_206])).

tff(c_30,plain,(
    k5_relat_1(k6_relat_1('#skF_2'),k6_relat_1('#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_82,plain,
    ( k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_30])).

tff(c_84,plain,(
    k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_82])).

tff(c_230,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_219,c_84])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:30:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.96/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.96/1.29  
% 1.96/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.96/1.30  %$ v5_relat_1 > v4_relat_1 > r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 1.96/1.30  
% 1.96/1.30  %Foreground sorts:
% 1.96/1.30  
% 1.96/1.30  
% 1.96/1.30  %Background operators:
% 1.96/1.30  
% 1.96/1.30  
% 1.96/1.30  %Foreground operators:
% 1.96/1.30  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.96/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.96/1.30  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.96/1.30  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.96/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.96/1.30  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.96/1.30  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.96/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.96/1.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.96/1.30  tff('#skF_2', type, '#skF_2': $i).
% 1.96/1.30  tff('#skF_1', type, '#skF_1': $i).
% 1.96/1.30  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.96/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.96/1.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.96/1.30  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.96/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.96/1.30  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 1.96/1.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.96/1.30  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.96/1.30  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.96/1.30  
% 2.15/1.31  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.15/1.31  tff(f_67, axiom, (![A]: ((v1_relat_1(k6_relat_1(A)) & v4_relat_1(k6_relat_1(A), A)) & v5_relat_1(k6_relat_1(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc24_relat_1)).
% 2.15/1.31  tff(f_53, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 2.15/1.31  tff(f_37, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_relat_1)).
% 2.15/1.31  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_relat_1)).
% 2.15/1.31  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 2.15/1.31  tff(f_57, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 2.15/1.31  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_relat_1)).
% 2.15/1.31  tff(f_70, negated_conjecture, ~(![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 2.15/1.31  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.15/1.31  tff(c_24, plain, (![A_22]: (v1_relat_1(k6_relat_1(A_22)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.15/1.31  tff(c_26, plain, (![A_22]: (v4_relat_1(k6_relat_1(A_22), A_22))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.15/1.31  tff(c_85, plain, (![B_36, A_37]: (k7_relat_1(B_36, A_37)=B_36 | ~v4_relat_1(B_36, A_37) | ~v1_relat_1(B_36))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.15/1.31  tff(c_88, plain, (![A_22]: (k7_relat_1(k6_relat_1(A_22), A_22)=k6_relat_1(A_22) | ~v1_relat_1(k6_relat_1(A_22)))), inference(resolution, [status(thm)], [c_26, c_85])).
% 2.15/1.31  tff(c_91, plain, (![A_22]: (k7_relat_1(k6_relat_1(A_22), A_22)=k6_relat_1(A_22))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_88])).
% 2.15/1.31  tff(c_153, plain, (![C_48, A_49, B_50]: (k7_relat_1(k7_relat_1(C_48, A_49), B_50)=k7_relat_1(C_48, k3_xboole_0(A_49, B_50)) | ~v1_relat_1(C_48))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.15/1.31  tff(c_168, plain, (![A_22, B_50]: (k7_relat_1(k6_relat_1(A_22), k3_xboole_0(A_22, B_50))=k7_relat_1(k6_relat_1(A_22), B_50) | ~v1_relat_1(k6_relat_1(A_22)))), inference(superposition, [status(thm), theory('equality')], [c_91, c_153])).
% 2.15/1.31  tff(c_200, plain, (![A_53, B_54]: (k7_relat_1(k6_relat_1(A_53), k3_xboole_0(A_53, B_54))=k7_relat_1(k6_relat_1(A_53), B_54))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_168])).
% 2.15/1.31  tff(c_101, plain, (![B_39, A_40]: (k5_relat_1(B_39, k6_relat_1(A_40))=k8_relat_1(A_40, B_39) | ~v1_relat_1(B_39))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.15/1.31  tff(c_22, plain, (![A_20, B_21]: (k5_relat_1(k6_relat_1(A_20), B_21)=k7_relat_1(B_21, A_20) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.15/1.31  tff(c_111, plain, (![A_40, A_20]: (k8_relat_1(A_40, k6_relat_1(A_20))=k7_relat_1(k6_relat_1(A_40), A_20) | ~v1_relat_1(k6_relat_1(A_40)) | ~v1_relat_1(k6_relat_1(A_20)))), inference(superposition, [status(thm), theory('equality')], [c_101, c_22])).
% 2.15/1.31  tff(c_123, plain, (![A_40, A_20]: (k8_relat_1(A_40, k6_relat_1(A_20))=k7_relat_1(k6_relat_1(A_40), A_20))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_24, c_111])).
% 2.15/1.31  tff(c_20, plain, (![A_19]: (k2_relat_1(k6_relat_1(A_19))=A_19)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.15/1.31  tff(c_147, plain, (![A_46, B_47]: (k8_relat_1(A_46, B_47)=B_47 | ~r1_tarski(k2_relat_1(B_47), A_46) | ~v1_relat_1(B_47))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.15/1.31  tff(c_150, plain, (![A_46, A_19]: (k8_relat_1(A_46, k6_relat_1(A_19))=k6_relat_1(A_19) | ~r1_tarski(A_19, A_46) | ~v1_relat_1(k6_relat_1(A_19)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_147])).
% 2.15/1.31  tff(c_152, plain, (![A_46, A_19]: (k7_relat_1(k6_relat_1(A_46), A_19)=k6_relat_1(A_19) | ~r1_tarski(A_19, A_46))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_123, c_150])).
% 2.15/1.31  tff(c_206, plain, (![A_53, B_54]: (k7_relat_1(k6_relat_1(A_53), B_54)=k6_relat_1(k3_xboole_0(A_53, B_54)) | ~r1_tarski(k3_xboole_0(A_53, B_54), A_53))), inference(superposition, [status(thm), theory('equality')], [c_200, c_152])).
% 2.15/1.31  tff(c_219, plain, (![A_53, B_54]: (k7_relat_1(k6_relat_1(A_53), B_54)=k6_relat_1(k3_xboole_0(A_53, B_54)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_206])).
% 2.15/1.31  tff(c_30, plain, (k5_relat_1(k6_relat_1('#skF_2'), k6_relat_1('#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.15/1.31  tff(c_82, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_22, c_30])).
% 2.15/1.31  tff(c_84, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_82])).
% 2.15/1.31  tff(c_230, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_219, c_84])).
% 2.15/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.31  
% 2.15/1.31  Inference rules
% 2.15/1.31  ----------------------
% 2.15/1.31  #Ref     : 0
% 2.15/1.31  #Sup     : 40
% 2.15/1.31  #Fact    : 0
% 2.15/1.31  #Define  : 0
% 2.15/1.31  #Split   : 1
% 2.15/1.31  #Chain   : 0
% 2.15/1.31  #Close   : 0
% 2.15/1.31  
% 2.15/1.31  Ordering : KBO
% 2.15/1.31  
% 2.15/1.31  Simplification rules
% 2.15/1.31  ----------------------
% 2.15/1.31  #Subsume      : 1
% 2.15/1.31  #Demod        : 20
% 2.15/1.31  #Tautology    : 27
% 2.15/1.31  #SimpNegUnit  : 0
% 2.15/1.31  #BackRed      : 5
% 2.15/1.31  
% 2.15/1.31  #Partial instantiations: 0
% 2.15/1.31  #Strategies tried      : 1
% 2.15/1.31  
% 2.15/1.31  Timing (in seconds)
% 2.15/1.31  ----------------------
% 2.15/1.32  Preprocessing        : 0.28
% 2.15/1.32  Parsing              : 0.16
% 2.15/1.32  CNF conversion       : 0.02
% 2.15/1.32  Main loop            : 0.20
% 2.15/1.32  Inferencing          : 0.08
% 2.15/1.32  Reduction            : 0.07
% 2.15/1.32  Demodulation         : 0.05
% 2.15/1.32  BG Simplification    : 0.01
% 2.15/1.32  Subsumption          : 0.02
% 2.15/1.32  Abstraction          : 0.02
% 2.15/1.32  MUC search           : 0.00
% 2.15/1.32  Cooper               : 0.00
% 2.15/1.32  Total                : 0.52
% 2.15/1.32  Index Insertion      : 0.00
% 2.15/1.32  Index Deletion       : 0.00
% 2.15/1.32  Index Matching       : 0.00
% 2.15/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
