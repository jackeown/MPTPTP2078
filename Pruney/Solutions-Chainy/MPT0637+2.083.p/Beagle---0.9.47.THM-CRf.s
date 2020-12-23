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
% DateTime   : Thu Dec  3 10:03:35 EST 2020

% Result     : Theorem 2.37s
% Output     : CNFRefutation 2.37s
% Verified   : 
% Statistics : Number of formulae       :   51 (  92 expanded)
%              Number of leaves         :   27 (  46 expanded)
%              Depth                    :    7
%              Number of atoms          :   58 ( 117 expanded)
%              Number of equality atoms :   26 (  51 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    5 (   2 average)

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

tff(f_33,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_59,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k8_relat_1(A,B)) = k3_xboole_0(k2_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k2_relat_1(k8_relat_1(A,B)),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k7_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_relat_1)).

tff(f_66,negated_conjecture,(
    ~ ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(c_8,plain,(
    ! [A_8] : v1_relat_1(k6_relat_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_78,plain,(
    ! [B_31,A_32] :
      ( k5_relat_1(B_31,k6_relat_1(A_32)) = k8_relat_1(A_32,B_31)
      | ~ v1_relat_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_24,plain,(
    ! [A_20,B_21] :
      ( k5_relat_1(k6_relat_1(A_20),B_21) = k7_relat_1(B_21,A_20)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_88,plain,(
    ! [A_32,A_20] :
      ( k8_relat_1(A_32,k6_relat_1(A_20)) = k7_relat_1(k6_relat_1(A_32),A_20)
      | ~ v1_relat_1(k6_relat_1(A_32))
      | ~ v1_relat_1(k6_relat_1(A_20)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_24])).

tff(c_100,plain,(
    ! [A_32,A_20] : k8_relat_1(A_32,k6_relat_1(A_20)) = k7_relat_1(k6_relat_1(A_32),A_20) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_8,c_88])).

tff(c_22,plain,(
    ! [A_19] : k2_relat_1(k6_relat_1(A_19)) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_137,plain,(
    ! [B_42,A_43] :
      ( k3_xboole_0(k2_relat_1(B_42),A_43) = k2_relat_1(k8_relat_1(A_43,B_42))
      | ~ v1_relat_1(B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_146,plain,(
    ! [A_43,A_19] :
      ( k2_relat_1(k8_relat_1(A_43,k6_relat_1(A_19))) = k3_xboole_0(A_19,A_43)
      | ~ v1_relat_1(k6_relat_1(A_19)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_137])).

tff(c_150,plain,(
    ! [A_43,A_19] : k2_relat_1(k7_relat_1(k6_relat_1(A_43),A_19)) = k3_xboole_0(A_19,A_43) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_100,c_146])).

tff(c_115,plain,(
    ! [A_35,B_36] :
      ( r1_tarski(k2_relat_1(k8_relat_1(A_35,B_36)),k2_relat_1(B_36))
      | ~ v1_relat_1(B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_121,plain,(
    ! [A_35,A_19] :
      ( r1_tarski(k2_relat_1(k8_relat_1(A_35,k6_relat_1(A_19))),A_19)
      | ~ v1_relat_1(k6_relat_1(A_19)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_115])).

tff(c_125,plain,(
    ! [A_35,A_19] : r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(A_35),A_19)),A_19) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_100,c_121])).

tff(c_151,plain,(
    ! [A_19,A_35] : r1_tarski(k3_xboole_0(A_19,A_35),A_19) ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_125])).

tff(c_20,plain,(
    ! [A_19] : k1_relat_1(k6_relat_1(A_19)) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_171,plain,(
    ! [A_48,B_49] :
      ( k8_relat_1(A_48,B_49) = B_49
      | ~ r1_tarski(k2_relat_1(B_49),A_48)
      | ~ v1_relat_1(B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_180,plain,(
    ! [A_48,A_19] :
      ( k8_relat_1(A_48,k6_relat_1(A_19)) = k6_relat_1(A_19)
      | ~ r1_tarski(A_19,A_48)
      | ~ v1_relat_1(k6_relat_1(A_19)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_171])).

tff(c_183,plain,(
    ! [A_48,A_19] :
      ( k7_relat_1(k6_relat_1(A_48),A_19) = k6_relat_1(A_19)
      | ~ r1_tarski(A_19,A_48) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_100,c_180])).

tff(c_252,plain,(
    ! [B_58,A_59] :
      ( k7_relat_1(B_58,k3_xboole_0(k1_relat_1(B_58),A_59)) = k7_relat_1(B_58,A_59)
      | ~ v1_relat_1(B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_270,plain,(
    ! [A_48,A_59] :
      ( k6_relat_1(k3_xboole_0(k1_relat_1(k6_relat_1(A_48)),A_59)) = k7_relat_1(k6_relat_1(A_48),A_59)
      | ~ v1_relat_1(k6_relat_1(A_48))
      | ~ r1_tarski(k3_xboole_0(k1_relat_1(k6_relat_1(A_48)),A_59),A_48) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_252])).

tff(c_281,plain,(
    ! [A_48,A_59] : k7_relat_1(k6_relat_1(A_48),A_59) = k6_relat_1(k3_xboole_0(A_48,A_59)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_20,c_8,c_20,c_270])).

tff(c_26,plain,(
    k5_relat_1(k6_relat_1('#skF_2'),k6_relat_1('#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_75,plain,
    ( k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_26])).

tff(c_77,plain,(
    k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_75])).

tff(c_492,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_281,c_77])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:28:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.37/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.37/1.38  
% 2.37/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.37/1.38  %$ r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.37/1.38  
% 2.37/1.38  %Foreground sorts:
% 2.37/1.38  
% 2.37/1.38  
% 2.37/1.38  %Background operators:
% 2.37/1.38  
% 2.37/1.38  
% 2.37/1.38  %Foreground operators:
% 2.37/1.38  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.37/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.37/1.38  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.37/1.38  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.37/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.37/1.38  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.37/1.38  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.37/1.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.37/1.38  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.37/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.37/1.38  tff('#skF_1', type, '#skF_1': $i).
% 2.37/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.37/1.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.37/1.38  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.37/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.37/1.38  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.37/1.38  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.37/1.38  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.37/1.38  
% 2.37/1.39  tff(f_33, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.37/1.39  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_relat_1)).
% 2.37/1.39  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 2.37/1.39  tff(f_59, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 2.37/1.39  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k8_relat_1(A, B)) = k3_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t119_relat_1)).
% 2.37/1.39  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k8_relat_1(A, B)), k2_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t118_relat_1)).
% 2.37/1.39  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_relat_1)).
% 2.37/1.39  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k7_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t192_relat_1)).
% 2.37/1.39  tff(f_66, negated_conjecture, ~(![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 2.37/1.39  tff(c_8, plain, (![A_8]: (v1_relat_1(k6_relat_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.37/1.39  tff(c_78, plain, (![B_31, A_32]: (k5_relat_1(B_31, k6_relat_1(A_32))=k8_relat_1(A_32, B_31) | ~v1_relat_1(B_31))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.37/1.39  tff(c_24, plain, (![A_20, B_21]: (k5_relat_1(k6_relat_1(A_20), B_21)=k7_relat_1(B_21, A_20) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.37/1.39  tff(c_88, plain, (![A_32, A_20]: (k8_relat_1(A_32, k6_relat_1(A_20))=k7_relat_1(k6_relat_1(A_32), A_20) | ~v1_relat_1(k6_relat_1(A_32)) | ~v1_relat_1(k6_relat_1(A_20)))), inference(superposition, [status(thm), theory('equality')], [c_78, c_24])).
% 2.37/1.39  tff(c_100, plain, (![A_32, A_20]: (k8_relat_1(A_32, k6_relat_1(A_20))=k7_relat_1(k6_relat_1(A_32), A_20))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_8, c_88])).
% 2.37/1.39  tff(c_22, plain, (![A_19]: (k2_relat_1(k6_relat_1(A_19))=A_19)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.37/1.39  tff(c_137, plain, (![B_42, A_43]: (k3_xboole_0(k2_relat_1(B_42), A_43)=k2_relat_1(k8_relat_1(A_43, B_42)) | ~v1_relat_1(B_42))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.37/1.39  tff(c_146, plain, (![A_43, A_19]: (k2_relat_1(k8_relat_1(A_43, k6_relat_1(A_19)))=k3_xboole_0(A_19, A_43) | ~v1_relat_1(k6_relat_1(A_19)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_137])).
% 2.37/1.39  tff(c_150, plain, (![A_43, A_19]: (k2_relat_1(k7_relat_1(k6_relat_1(A_43), A_19))=k3_xboole_0(A_19, A_43))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_100, c_146])).
% 2.37/1.39  tff(c_115, plain, (![A_35, B_36]: (r1_tarski(k2_relat_1(k8_relat_1(A_35, B_36)), k2_relat_1(B_36)) | ~v1_relat_1(B_36))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.37/1.39  tff(c_121, plain, (![A_35, A_19]: (r1_tarski(k2_relat_1(k8_relat_1(A_35, k6_relat_1(A_19))), A_19) | ~v1_relat_1(k6_relat_1(A_19)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_115])).
% 2.37/1.39  tff(c_125, plain, (![A_35, A_19]: (r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(A_35), A_19)), A_19))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_100, c_121])).
% 2.37/1.39  tff(c_151, plain, (![A_19, A_35]: (r1_tarski(k3_xboole_0(A_19, A_35), A_19))), inference(demodulation, [status(thm), theory('equality')], [c_150, c_125])).
% 2.37/1.39  tff(c_20, plain, (![A_19]: (k1_relat_1(k6_relat_1(A_19))=A_19)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.37/1.39  tff(c_171, plain, (![A_48, B_49]: (k8_relat_1(A_48, B_49)=B_49 | ~r1_tarski(k2_relat_1(B_49), A_48) | ~v1_relat_1(B_49))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.37/1.39  tff(c_180, plain, (![A_48, A_19]: (k8_relat_1(A_48, k6_relat_1(A_19))=k6_relat_1(A_19) | ~r1_tarski(A_19, A_48) | ~v1_relat_1(k6_relat_1(A_19)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_171])).
% 2.37/1.39  tff(c_183, plain, (![A_48, A_19]: (k7_relat_1(k6_relat_1(A_48), A_19)=k6_relat_1(A_19) | ~r1_tarski(A_19, A_48))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_100, c_180])).
% 2.37/1.39  tff(c_252, plain, (![B_58, A_59]: (k7_relat_1(B_58, k3_xboole_0(k1_relat_1(B_58), A_59))=k7_relat_1(B_58, A_59) | ~v1_relat_1(B_58))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.37/1.39  tff(c_270, plain, (![A_48, A_59]: (k6_relat_1(k3_xboole_0(k1_relat_1(k6_relat_1(A_48)), A_59))=k7_relat_1(k6_relat_1(A_48), A_59) | ~v1_relat_1(k6_relat_1(A_48)) | ~r1_tarski(k3_xboole_0(k1_relat_1(k6_relat_1(A_48)), A_59), A_48))), inference(superposition, [status(thm), theory('equality')], [c_183, c_252])).
% 2.37/1.39  tff(c_281, plain, (![A_48, A_59]: (k7_relat_1(k6_relat_1(A_48), A_59)=k6_relat_1(k3_xboole_0(A_48, A_59)))), inference(demodulation, [status(thm), theory('equality')], [c_151, c_20, c_8, c_20, c_270])).
% 2.37/1.39  tff(c_26, plain, (k5_relat_1(k6_relat_1('#skF_2'), k6_relat_1('#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.37/1.39  tff(c_75, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_24, c_26])).
% 2.37/1.39  tff(c_77, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_75])).
% 2.37/1.39  tff(c_492, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_281, c_77])).
% 2.37/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.37/1.39  
% 2.37/1.39  Inference rules
% 2.37/1.39  ----------------------
% 2.37/1.39  #Ref     : 0
% 2.37/1.39  #Sup     : 108
% 2.37/1.39  #Fact    : 0
% 2.37/1.40  #Define  : 0
% 2.37/1.40  #Split   : 1
% 2.37/1.40  #Chain   : 0
% 2.37/1.40  #Close   : 0
% 2.37/1.40  
% 2.37/1.40  Ordering : KBO
% 2.37/1.40  
% 2.37/1.40  Simplification rules
% 2.37/1.40  ----------------------
% 2.37/1.40  #Subsume      : 3
% 2.37/1.40  #Demod        : 62
% 2.37/1.40  #Tautology    : 53
% 2.37/1.40  #SimpNegUnit  : 0
% 2.37/1.40  #BackRed      : 7
% 2.37/1.40  
% 2.37/1.40  #Partial instantiations: 0
% 2.37/1.40  #Strategies tried      : 1
% 2.37/1.40  
% 2.37/1.40  Timing (in seconds)
% 2.37/1.40  ----------------------
% 2.37/1.40  Preprocessing        : 0.33
% 2.37/1.40  Parsing              : 0.18
% 2.37/1.40  CNF conversion       : 0.02
% 2.37/1.40  Main loop            : 0.23
% 2.37/1.40  Inferencing          : 0.08
% 2.37/1.40  Reduction            : 0.08
% 2.37/1.40  Demodulation         : 0.06
% 2.37/1.40  BG Simplification    : 0.02
% 2.37/1.40  Subsumption          : 0.03
% 2.37/1.40  Abstraction          : 0.02
% 2.37/1.40  MUC search           : 0.00
% 2.37/1.40  Cooper               : 0.00
% 2.37/1.40  Total                : 0.59
% 2.37/1.40  Index Insertion      : 0.00
% 2.37/1.40  Index Deletion       : 0.00
% 2.37/1.40  Index Matching       : 0.00
% 2.37/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
