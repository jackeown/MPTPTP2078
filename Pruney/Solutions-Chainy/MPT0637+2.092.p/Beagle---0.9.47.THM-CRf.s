%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:36 EST 2020

% Result     : Theorem 2.10s
% Output     : CNFRefutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :   50 (  68 expanded)
%              Number of leaves         :   28 (  37 expanded)
%              Depth                    :    8
%              Number of atoms          :   55 (  84 expanded)
%              Number of equality atoms :   27 (  34 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_80,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_68,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_72,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_83,negated_conjecture,(
    ~ ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_28,plain,(
    ! [A_32] : v1_relat_1(k6_relat_1(A_32)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_22,plain,(
    ! [A_28] : k2_relat_1(k6_relat_1(A_28)) = A_28 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_146,plain,(
    ! [A_51,B_52] :
      ( k5_relat_1(k6_relat_1(A_51),B_52) = k7_relat_1(B_52,A_51)
      | ~ v1_relat_1(B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_24,plain,(
    ! [A_29] :
      ( k5_relat_1(A_29,k6_relat_1(k2_relat_1(A_29))) = A_29
      | ~ v1_relat_1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_164,plain,(
    ! [A_51] :
      ( k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_51))),A_51) = k6_relat_1(A_51)
      | ~ v1_relat_1(k6_relat_1(A_51))
      | ~ v1_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_51)))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_24])).

tff(c_187,plain,(
    ! [A_51] : k7_relat_1(k6_relat_1(A_51),A_51) = k6_relat_1(A_51) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_28,c_22,c_164])).

tff(c_281,plain,(
    ! [C_61,A_62,B_63] :
      ( k7_relat_1(k7_relat_1(C_61,A_62),B_63) = k7_relat_1(C_61,k3_xboole_0(A_62,B_63))
      | ~ v1_relat_1(C_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_299,plain,(
    ! [A_51,B_63] :
      ( k7_relat_1(k6_relat_1(A_51),k3_xboole_0(A_51,B_63)) = k7_relat_1(k6_relat_1(A_51),B_63)
      | ~ v1_relat_1(k6_relat_1(A_51)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_187,c_281])).

tff(c_306,plain,(
    ! [A_64,B_65] : k7_relat_1(k6_relat_1(A_64),k3_xboole_0(A_64,B_65)) = k7_relat_1(k6_relat_1(A_64),B_65) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_299])).

tff(c_14,plain,(
    ! [B_18,A_17] :
      ( k5_relat_1(B_18,k6_relat_1(A_17)) = k8_relat_1(A_17,B_18)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_171,plain,(
    ! [A_17,A_51] :
      ( k8_relat_1(A_17,k6_relat_1(A_51)) = k7_relat_1(k6_relat_1(A_17),A_51)
      | ~ v1_relat_1(k6_relat_1(A_17))
      | ~ v1_relat_1(k6_relat_1(A_51)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_146])).

tff(c_190,plain,(
    ! [A_17,A_51] : k8_relat_1(A_17,k6_relat_1(A_51)) = k7_relat_1(k6_relat_1(A_17),A_51) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_28,c_171])).

tff(c_253,plain,(
    ! [A_57,B_58] :
      ( k8_relat_1(A_57,B_58) = B_58
      | ~ r1_tarski(k2_relat_1(B_58),A_57)
      | ~ v1_relat_1(B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_256,plain,(
    ! [A_57,A_28] :
      ( k8_relat_1(A_57,k6_relat_1(A_28)) = k6_relat_1(A_28)
      | ~ r1_tarski(A_28,A_57)
      | ~ v1_relat_1(k6_relat_1(A_28)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_253])).

tff(c_258,plain,(
    ! [A_57,A_28] :
      ( k7_relat_1(k6_relat_1(A_57),A_28) = k6_relat_1(A_28)
      | ~ r1_tarski(A_28,A_57) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_190,c_256])).

tff(c_315,plain,(
    ! [A_64,B_65] :
      ( k7_relat_1(k6_relat_1(A_64),B_65) = k6_relat_1(k3_xboole_0(A_64,B_65))
      | ~ r1_tarski(k3_xboole_0(A_64,B_65),A_64) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_306,c_258])).

tff(c_327,plain,(
    ! [A_64,B_65] : k7_relat_1(k6_relat_1(A_64),B_65) = k6_relat_1(k3_xboole_0(A_64,B_65)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_315])).

tff(c_32,plain,(
    k5_relat_1(k6_relat_1('#skF_2'),k6_relat_1('#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_156,plain,
    ( k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_32])).

tff(c_183,plain,(
    k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_156])).

tff(c_336,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_327,c_183])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:17:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.10/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.25  
% 2.10/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.25  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.10/1.25  
% 2.10/1.25  %Foreground sorts:
% 2.10/1.25  
% 2.10/1.25  
% 2.10/1.25  %Background operators:
% 2.10/1.25  
% 2.10/1.25  
% 2.10/1.25  %Foreground operators:
% 2.10/1.25  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.10/1.25  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.10/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.10/1.25  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.10/1.25  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.10/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.10/1.25  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.10/1.25  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.10/1.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.10/1.25  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.10/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.10/1.25  tff('#skF_1', type, '#skF_1': $i).
% 2.10/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.10/1.25  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.10/1.25  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.10/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.10/1.25  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.10/1.25  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.10/1.25  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.10/1.25  
% 2.10/1.26  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.10/1.26  tff(f_80, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.10/1.26  tff(f_68, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.10/1.26  tff(f_76, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 2.10/1.26  tff(f_72, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_relat_1)).
% 2.10/1.26  tff(f_37, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 2.10/1.26  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_relat_1)).
% 2.10/1.26  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_relat_1)).
% 2.10/1.26  tff(f_83, negated_conjecture, ~(![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 2.10/1.26  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.10/1.26  tff(c_28, plain, (![A_32]: (v1_relat_1(k6_relat_1(A_32)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.10/1.26  tff(c_22, plain, (![A_28]: (k2_relat_1(k6_relat_1(A_28))=A_28)), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.10/1.26  tff(c_146, plain, (![A_51, B_52]: (k5_relat_1(k6_relat_1(A_51), B_52)=k7_relat_1(B_52, A_51) | ~v1_relat_1(B_52))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.10/1.26  tff(c_24, plain, (![A_29]: (k5_relat_1(A_29, k6_relat_1(k2_relat_1(A_29)))=A_29 | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.10/1.26  tff(c_164, plain, (![A_51]: (k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_51))), A_51)=k6_relat_1(A_51) | ~v1_relat_1(k6_relat_1(A_51)) | ~v1_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_51)))))), inference(superposition, [status(thm), theory('equality')], [c_146, c_24])).
% 2.10/1.26  tff(c_187, plain, (![A_51]: (k7_relat_1(k6_relat_1(A_51), A_51)=k6_relat_1(A_51))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_28, c_22, c_164])).
% 2.10/1.26  tff(c_281, plain, (![C_61, A_62, B_63]: (k7_relat_1(k7_relat_1(C_61, A_62), B_63)=k7_relat_1(C_61, k3_xboole_0(A_62, B_63)) | ~v1_relat_1(C_61))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.10/1.26  tff(c_299, plain, (![A_51, B_63]: (k7_relat_1(k6_relat_1(A_51), k3_xboole_0(A_51, B_63))=k7_relat_1(k6_relat_1(A_51), B_63) | ~v1_relat_1(k6_relat_1(A_51)))), inference(superposition, [status(thm), theory('equality')], [c_187, c_281])).
% 2.10/1.26  tff(c_306, plain, (![A_64, B_65]: (k7_relat_1(k6_relat_1(A_64), k3_xboole_0(A_64, B_65))=k7_relat_1(k6_relat_1(A_64), B_65))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_299])).
% 2.10/1.26  tff(c_14, plain, (![B_18, A_17]: (k5_relat_1(B_18, k6_relat_1(A_17))=k8_relat_1(A_17, B_18) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.10/1.26  tff(c_171, plain, (![A_17, A_51]: (k8_relat_1(A_17, k6_relat_1(A_51))=k7_relat_1(k6_relat_1(A_17), A_51) | ~v1_relat_1(k6_relat_1(A_17)) | ~v1_relat_1(k6_relat_1(A_51)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_146])).
% 2.10/1.26  tff(c_190, plain, (![A_17, A_51]: (k8_relat_1(A_17, k6_relat_1(A_51))=k7_relat_1(k6_relat_1(A_17), A_51))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_28, c_171])).
% 2.10/1.26  tff(c_253, plain, (![A_57, B_58]: (k8_relat_1(A_57, B_58)=B_58 | ~r1_tarski(k2_relat_1(B_58), A_57) | ~v1_relat_1(B_58))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.10/1.26  tff(c_256, plain, (![A_57, A_28]: (k8_relat_1(A_57, k6_relat_1(A_28))=k6_relat_1(A_28) | ~r1_tarski(A_28, A_57) | ~v1_relat_1(k6_relat_1(A_28)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_253])).
% 2.10/1.26  tff(c_258, plain, (![A_57, A_28]: (k7_relat_1(k6_relat_1(A_57), A_28)=k6_relat_1(A_28) | ~r1_tarski(A_28, A_57))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_190, c_256])).
% 2.10/1.26  tff(c_315, plain, (![A_64, B_65]: (k7_relat_1(k6_relat_1(A_64), B_65)=k6_relat_1(k3_xboole_0(A_64, B_65)) | ~r1_tarski(k3_xboole_0(A_64, B_65), A_64))), inference(superposition, [status(thm), theory('equality')], [c_306, c_258])).
% 2.10/1.26  tff(c_327, plain, (![A_64, B_65]: (k7_relat_1(k6_relat_1(A_64), B_65)=k6_relat_1(k3_xboole_0(A_64, B_65)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_315])).
% 2.10/1.26  tff(c_32, plain, (k5_relat_1(k6_relat_1('#skF_2'), k6_relat_1('#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.10/1.26  tff(c_156, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_146, c_32])).
% 2.10/1.26  tff(c_183, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_156])).
% 2.10/1.26  tff(c_336, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_327, c_183])).
% 2.10/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.26  
% 2.10/1.26  Inference rules
% 2.10/1.26  ----------------------
% 2.10/1.26  #Ref     : 0
% 2.10/1.26  #Sup     : 61
% 2.10/1.26  #Fact    : 0
% 2.10/1.26  #Define  : 0
% 2.10/1.26  #Split   : 1
% 2.10/1.26  #Chain   : 0
% 2.10/1.26  #Close   : 0
% 2.10/1.26  
% 2.10/1.26  Ordering : KBO
% 2.10/1.26  
% 2.10/1.26  Simplification rules
% 2.10/1.26  ----------------------
% 2.10/1.26  #Subsume      : 2
% 2.10/1.26  #Demod        : 47
% 2.10/1.26  #Tautology    : 44
% 2.10/1.26  #SimpNegUnit  : 0
% 2.10/1.26  #BackRed      : 5
% 2.10/1.26  
% 2.10/1.26  #Partial instantiations: 0
% 2.10/1.26  #Strategies tried      : 1
% 2.10/1.26  
% 2.10/1.26  Timing (in seconds)
% 2.10/1.26  ----------------------
% 2.10/1.27  Preprocessing        : 0.29
% 2.10/1.27  Parsing              : 0.16
% 2.10/1.27  CNF conversion       : 0.02
% 2.10/1.27  Main loop            : 0.18
% 2.10/1.27  Inferencing          : 0.07
% 2.10/1.27  Reduction            : 0.06
% 2.10/1.27  Demodulation         : 0.04
% 2.10/1.27  BG Simplification    : 0.01
% 2.10/1.27  Subsumption          : 0.02
% 2.10/1.27  Abstraction          : 0.01
% 2.10/1.27  MUC search           : 0.00
% 2.10/1.27  Cooper               : 0.00
% 2.10/1.27  Total                : 0.50
% 2.10/1.27  Index Insertion      : 0.00
% 2.10/1.27  Index Deletion       : 0.00
% 2.10/1.27  Index Matching       : 0.00
% 2.10/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
