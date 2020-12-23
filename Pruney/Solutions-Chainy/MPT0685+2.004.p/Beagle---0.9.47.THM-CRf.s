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
% DateTime   : Thu Dec  3 10:04:30 EST 2020

% Result     : Theorem 5.90s
% Output     : CNFRefutation 5.90s
% Verified   : 
% Statistics : Number of formulae       :   49 (  63 expanded)
%              Number of leaves         :   28 (  36 expanded)
%              Depth                    :    9
%              Number of atoms          :   54 (  77 expanded)
%              Number of equality atoms :   25 (  32 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

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

tff(f_68,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_53,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_63,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k10_relat_1(k5_relat_1(B,C),A) = k10_relat_1(B,k10_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t181_relat_1)).

tff(c_30,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_22,plain,(
    ! [A_22] : v1_relat_1(k6_relat_1(A_22)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_16,plain,(
    ! [A_19] : k1_relat_1(k6_relat_1(A_19)) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_135,plain,(
    ! [A_42,B_43] :
      ( k5_relat_1(k6_relat_1(A_42),B_43) = k7_relat_1(B_43,A_42)
      | ~ v1_relat_1(B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_26,plain,(
    ! [B_24,A_23] : k5_relat_1(k6_relat_1(B_24),k6_relat_1(A_23)) = k6_relat_1(k3_xboole_0(A_23,B_24)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_142,plain,(
    ! [A_23,A_42] :
      ( k7_relat_1(k6_relat_1(A_23),A_42) = k6_relat_1(k3_xboole_0(A_23,A_42))
      | ~ v1_relat_1(k6_relat_1(A_23)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_26])).

tff(c_151,plain,(
    ! [A_23,A_42] : k7_relat_1(k6_relat_1(A_23),A_42) = k6_relat_1(k3_xboole_0(A_23,A_42)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_142])).

tff(c_20,plain,(
    ! [A_20,B_21] :
      ( k5_relat_1(k6_relat_1(A_20),B_21) = k7_relat_1(B_21,A_20)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_165,plain,(
    ! [A_46,B_47] :
      ( k10_relat_1(A_46,k1_relat_1(B_47)) = k1_relat_1(k5_relat_1(A_46,B_47))
      | ~ v1_relat_1(B_47)
      | ~ v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_174,plain,(
    ! [A_46,A_19] :
      ( k1_relat_1(k5_relat_1(A_46,k6_relat_1(A_19))) = k10_relat_1(A_46,A_19)
      | ~ v1_relat_1(k6_relat_1(A_19))
      | ~ v1_relat_1(A_46) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_165])).

tff(c_197,plain,(
    ! [A_50,A_51] :
      ( k1_relat_1(k5_relat_1(A_50,k6_relat_1(A_51))) = k10_relat_1(A_50,A_51)
      | ~ v1_relat_1(A_50) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_174])).

tff(c_210,plain,(
    ! [A_51,A_20] :
      ( k1_relat_1(k7_relat_1(k6_relat_1(A_51),A_20)) = k10_relat_1(k6_relat_1(A_20),A_51)
      | ~ v1_relat_1(k6_relat_1(A_20))
      | ~ v1_relat_1(k6_relat_1(A_51)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_197])).

tff(c_217,plain,(
    ! [A_20,A_51] : k10_relat_1(k6_relat_1(A_20),A_51) = k3_xboole_0(A_51,A_20) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_22,c_16,c_151,c_210])).

tff(c_241,plain,(
    ! [B_54,C_55,A_56] :
      ( k10_relat_1(k5_relat_1(B_54,C_55),A_56) = k10_relat_1(B_54,k10_relat_1(C_55,A_56))
      | ~ v1_relat_1(C_55)
      | ~ v1_relat_1(B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_258,plain,(
    ! [A_20,B_21,A_56] :
      ( k10_relat_1(k6_relat_1(A_20),k10_relat_1(B_21,A_56)) = k10_relat_1(k7_relat_1(B_21,A_20),A_56)
      | ~ v1_relat_1(B_21)
      | ~ v1_relat_1(k6_relat_1(A_20))
      | ~ v1_relat_1(B_21) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_241])).

tff(c_1319,plain,(
    ! [B_80,A_81,A_82] :
      ( k3_xboole_0(k10_relat_1(B_80,A_81),A_82) = k10_relat_1(k7_relat_1(B_80,A_82),A_81)
      | ~ v1_relat_1(B_80) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_217,c_258])).

tff(c_2887,plain,(
    ! [A_107,B_108,A_109] :
      ( k3_xboole_0(A_107,k10_relat_1(B_108,A_109)) = k10_relat_1(k7_relat_1(B_108,A_107),A_109)
      | ~ v1_relat_1(B_108) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1319])).

tff(c_28,plain,(
    k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2')) != k10_relat_1(k7_relat_1('#skF_3','#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2965,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2887,c_28])).

tff(c_3027,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_2965])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:02:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.90/2.11  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.90/2.12  
% 5.90/2.12  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.90/2.12  %$ v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 5.90/2.12  
% 5.90/2.12  %Foreground sorts:
% 5.90/2.12  
% 5.90/2.12  
% 5.90/2.12  %Background operators:
% 5.90/2.12  
% 5.90/2.12  
% 5.90/2.12  %Foreground operators:
% 5.90/2.12  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.90/2.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.90/2.12  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.90/2.12  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 5.90/2.12  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.90/2.12  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.90/2.12  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.90/2.12  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.90/2.12  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.90/2.12  tff('#skF_2', type, '#skF_2': $i).
% 5.90/2.12  tff('#skF_3', type, '#skF_3': $i).
% 5.90/2.12  tff('#skF_1', type, '#skF_1': $i).
% 5.90/2.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.90/2.12  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 5.90/2.12  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.90/2.12  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.90/2.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.90/2.12  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.90/2.12  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.90/2.12  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 5.90/2.12  
% 5.90/2.13  tff(f_68, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_funct_1)).
% 5.90/2.13  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.90/2.13  tff(f_61, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 5.90/2.13  tff(f_53, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 5.90/2.13  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 5.90/2.13  tff(f_63, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 5.90/2.13  tff(f_49, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 5.90/2.13  tff(f_42, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k10_relat_1(k5_relat_1(B, C), A) = k10_relat_1(B, k10_relat_1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t181_relat_1)).
% 5.90/2.13  tff(c_30, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.90/2.13  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.90/2.13  tff(c_22, plain, (![A_22]: (v1_relat_1(k6_relat_1(A_22)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.90/2.13  tff(c_16, plain, (![A_19]: (k1_relat_1(k6_relat_1(A_19))=A_19)), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.90/2.13  tff(c_135, plain, (![A_42, B_43]: (k5_relat_1(k6_relat_1(A_42), B_43)=k7_relat_1(B_43, A_42) | ~v1_relat_1(B_43))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.90/2.13  tff(c_26, plain, (![B_24, A_23]: (k5_relat_1(k6_relat_1(B_24), k6_relat_1(A_23))=k6_relat_1(k3_xboole_0(A_23, B_24)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.90/2.13  tff(c_142, plain, (![A_23, A_42]: (k7_relat_1(k6_relat_1(A_23), A_42)=k6_relat_1(k3_xboole_0(A_23, A_42)) | ~v1_relat_1(k6_relat_1(A_23)))), inference(superposition, [status(thm), theory('equality')], [c_135, c_26])).
% 5.90/2.13  tff(c_151, plain, (![A_23, A_42]: (k7_relat_1(k6_relat_1(A_23), A_42)=k6_relat_1(k3_xboole_0(A_23, A_42)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_142])).
% 5.90/2.13  tff(c_20, plain, (![A_20, B_21]: (k5_relat_1(k6_relat_1(A_20), B_21)=k7_relat_1(B_21, A_20) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.90/2.13  tff(c_165, plain, (![A_46, B_47]: (k10_relat_1(A_46, k1_relat_1(B_47))=k1_relat_1(k5_relat_1(A_46, B_47)) | ~v1_relat_1(B_47) | ~v1_relat_1(A_46))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.90/2.13  tff(c_174, plain, (![A_46, A_19]: (k1_relat_1(k5_relat_1(A_46, k6_relat_1(A_19)))=k10_relat_1(A_46, A_19) | ~v1_relat_1(k6_relat_1(A_19)) | ~v1_relat_1(A_46))), inference(superposition, [status(thm), theory('equality')], [c_16, c_165])).
% 5.90/2.13  tff(c_197, plain, (![A_50, A_51]: (k1_relat_1(k5_relat_1(A_50, k6_relat_1(A_51)))=k10_relat_1(A_50, A_51) | ~v1_relat_1(A_50))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_174])).
% 5.90/2.13  tff(c_210, plain, (![A_51, A_20]: (k1_relat_1(k7_relat_1(k6_relat_1(A_51), A_20))=k10_relat_1(k6_relat_1(A_20), A_51) | ~v1_relat_1(k6_relat_1(A_20)) | ~v1_relat_1(k6_relat_1(A_51)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_197])).
% 5.90/2.13  tff(c_217, plain, (![A_20, A_51]: (k10_relat_1(k6_relat_1(A_20), A_51)=k3_xboole_0(A_51, A_20))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_22, c_16, c_151, c_210])).
% 5.90/2.13  tff(c_241, plain, (![B_54, C_55, A_56]: (k10_relat_1(k5_relat_1(B_54, C_55), A_56)=k10_relat_1(B_54, k10_relat_1(C_55, A_56)) | ~v1_relat_1(C_55) | ~v1_relat_1(B_54))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.90/2.13  tff(c_258, plain, (![A_20, B_21, A_56]: (k10_relat_1(k6_relat_1(A_20), k10_relat_1(B_21, A_56))=k10_relat_1(k7_relat_1(B_21, A_20), A_56) | ~v1_relat_1(B_21) | ~v1_relat_1(k6_relat_1(A_20)) | ~v1_relat_1(B_21))), inference(superposition, [status(thm), theory('equality')], [c_20, c_241])).
% 5.90/2.13  tff(c_1319, plain, (![B_80, A_81, A_82]: (k3_xboole_0(k10_relat_1(B_80, A_81), A_82)=k10_relat_1(k7_relat_1(B_80, A_82), A_81) | ~v1_relat_1(B_80))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_217, c_258])).
% 5.90/2.13  tff(c_2887, plain, (![A_107, B_108, A_109]: (k3_xboole_0(A_107, k10_relat_1(B_108, A_109))=k10_relat_1(k7_relat_1(B_108, A_107), A_109) | ~v1_relat_1(B_108))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1319])).
% 5.90/2.13  tff(c_28, plain, (k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))!=k10_relat_1(k7_relat_1('#skF_3', '#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.90/2.13  tff(c_2965, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2887, c_28])).
% 5.90/2.13  tff(c_3027, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_2965])).
% 5.90/2.13  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.90/2.13  
% 5.90/2.13  Inference rules
% 5.90/2.13  ----------------------
% 5.90/2.13  #Ref     : 0
% 5.90/2.13  #Sup     : 782
% 5.90/2.13  #Fact    : 0
% 5.90/2.13  #Define  : 0
% 5.90/2.13  #Split   : 0
% 5.90/2.13  #Chain   : 0
% 5.90/2.13  #Close   : 0
% 5.90/2.13  
% 5.90/2.13  Ordering : KBO
% 5.90/2.13  
% 5.90/2.13  Simplification rules
% 5.90/2.13  ----------------------
% 5.90/2.13  #Subsume      : 136
% 5.90/2.13  #Demod        : 459
% 5.90/2.13  #Tautology    : 156
% 5.90/2.13  #SimpNegUnit  : 0
% 5.90/2.13  #BackRed      : 0
% 5.90/2.13  
% 5.90/2.13  #Partial instantiations: 0
% 5.90/2.13  #Strategies tried      : 1
% 5.90/2.13  
% 5.90/2.13  Timing (in seconds)
% 5.90/2.13  ----------------------
% 5.90/2.13  Preprocessing        : 0.30
% 5.90/2.13  Parsing              : 0.16
% 5.90/2.13  CNF conversion       : 0.02
% 5.90/2.13  Main loop            : 1.08
% 5.90/2.13  Inferencing          : 0.25
% 5.90/2.13  Reduction            : 0.64
% 5.90/2.13  Demodulation         : 0.59
% 5.90/2.13  BG Simplification    : 0.04
% 5.90/2.13  Subsumption          : 0.11
% 5.90/2.13  Abstraction          : 0.06
% 5.90/2.13  MUC search           : 0.00
% 5.90/2.13  Cooper               : 0.00
% 5.90/2.14  Total                : 1.41
% 5.90/2.14  Index Insertion      : 0.00
% 5.90/2.14  Index Deletion       : 0.00
% 5.90/2.14  Index Matching       : 0.00
% 5.90/2.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
