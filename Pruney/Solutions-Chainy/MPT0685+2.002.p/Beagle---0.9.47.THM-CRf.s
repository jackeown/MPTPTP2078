%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:30 EST 2020

% Result     : Theorem 6.06s
% Output     : CNFRefutation 6.06s
% Verified   : 
% Statistics : Number of formulae       :   51 (  59 expanded)
%              Number of leaves         :   28 (  33 expanded)
%              Depth                    :    9
%              Number of atoms          :   55 (  67 expanded)
%              Number of equality atoms :   28 (  33 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(f_66,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_33,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_51,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_61,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k10_relat_1(k5_relat_1(B,C),A) = k10_relat_1(B,k10_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t181_relat_1)).

tff(c_28,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_tarski(B_2,A_1) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_91,plain,(
    ! [A_31,B_32] : k1_setfam_1(k2_tarski(A_31,B_32)) = k3_xboole_0(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_106,plain,(
    ! [B_33,A_34] : k1_setfam_1(k2_tarski(B_33,A_34)) = k3_xboole_0(A_34,B_33) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_91])).

tff(c_8,plain,(
    ! [A_8,B_9] : k1_setfam_1(k2_tarski(A_8,B_9)) = k3_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_112,plain,(
    ! [B_33,A_34] : k3_xboole_0(B_33,A_34) = k3_xboole_0(A_34,B_33) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_8])).

tff(c_20,plain,(
    ! [A_20] : v1_relat_1(k6_relat_1(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_14,plain,(
    ! [A_17] : k1_relat_1(k6_relat_1(A_17)) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_24,plain,(
    ! [B_22,A_21] : k5_relat_1(k6_relat_1(B_22),k6_relat_1(A_21)) = k6_relat_1(k3_xboole_0(A_21,B_22)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_211,plain,(
    ! [A_46,B_47] :
      ( k10_relat_1(A_46,k1_relat_1(B_47)) = k1_relat_1(k5_relat_1(A_46,B_47))
      | ~ v1_relat_1(B_47)
      | ~ v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_220,plain,(
    ! [A_46,A_17] :
      ( k1_relat_1(k5_relat_1(A_46,k6_relat_1(A_17))) = k10_relat_1(A_46,A_17)
      | ~ v1_relat_1(k6_relat_1(A_17))
      | ~ v1_relat_1(A_46) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_211])).

tff(c_252,plain,(
    ! [A_51,A_52] :
      ( k1_relat_1(k5_relat_1(A_51,k6_relat_1(A_52))) = k10_relat_1(A_51,A_52)
      | ~ v1_relat_1(A_51) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_220])).

tff(c_264,plain,(
    ! [A_21,B_22] :
      ( k1_relat_1(k6_relat_1(k3_xboole_0(A_21,B_22))) = k10_relat_1(k6_relat_1(B_22),A_21)
      | ~ v1_relat_1(k6_relat_1(B_22)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_252])).

tff(c_272,plain,(
    ! [B_22,A_21] : k10_relat_1(k6_relat_1(B_22),A_21) = k3_xboole_0(A_21,B_22) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_14,c_264])).

tff(c_18,plain,(
    ! [A_18,B_19] :
      ( k5_relat_1(k6_relat_1(A_18),B_19) = k7_relat_1(B_19,A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_225,plain,(
    ! [B_48,C_49,A_50] :
      ( k10_relat_1(k5_relat_1(B_48,C_49),A_50) = k10_relat_1(B_48,k10_relat_1(C_49,A_50))
      | ~ v1_relat_1(C_49)
      | ~ v1_relat_1(B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_245,plain,(
    ! [A_18,B_19,A_50] :
      ( k10_relat_1(k6_relat_1(A_18),k10_relat_1(B_19,A_50)) = k10_relat_1(k7_relat_1(B_19,A_18),A_50)
      | ~ v1_relat_1(B_19)
      | ~ v1_relat_1(k6_relat_1(A_18))
      | ~ v1_relat_1(B_19) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_225])).

tff(c_251,plain,(
    ! [A_18,B_19,A_50] :
      ( k10_relat_1(k6_relat_1(A_18),k10_relat_1(B_19,A_50)) = k10_relat_1(k7_relat_1(B_19,A_18),A_50)
      | ~ v1_relat_1(B_19) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_245])).

tff(c_1176,plain,(
    ! [B_74,A_75,A_76] :
      ( k3_xboole_0(k10_relat_1(B_74,A_75),A_76) = k10_relat_1(k7_relat_1(B_74,A_76),A_75)
      | ~ v1_relat_1(B_74) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_272,c_251])).

tff(c_3399,plain,(
    ! [A_121,B_122,A_123] :
      ( k3_xboole_0(A_121,k10_relat_1(B_122,A_123)) = k10_relat_1(k7_relat_1(B_122,A_121),A_123)
      | ~ v1_relat_1(B_122) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_1176])).

tff(c_26,plain,(
    k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2')) != k10_relat_1(k7_relat_1('#skF_3','#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_3493,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3399,c_26])).

tff(c_3564,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_3493])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:49:11 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.06/2.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.06/2.16  
% 6.06/2.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.06/2.16  %$ v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 6.06/2.16  
% 6.06/2.16  %Foreground sorts:
% 6.06/2.16  
% 6.06/2.16  
% 6.06/2.16  %Background operators:
% 6.06/2.16  
% 6.06/2.16  
% 6.06/2.16  %Foreground operators:
% 6.06/2.16  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.06/2.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.06/2.16  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 6.06/2.16  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 6.06/2.16  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.06/2.16  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.06/2.16  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.06/2.16  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.06/2.16  tff('#skF_2', type, '#skF_2': $i).
% 6.06/2.16  tff('#skF_3', type, '#skF_3': $i).
% 6.06/2.16  tff('#skF_1', type, '#skF_1': $i).
% 6.06/2.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.06/2.16  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 6.06/2.16  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.06/2.16  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 6.06/2.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.06/2.16  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.06/2.16  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.06/2.16  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 6.06/2.16  
% 6.06/2.17  tff(f_66, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 6.06/2.17  tff(f_27, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 6.06/2.17  tff(f_33, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 6.06/2.17  tff(f_59, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 6.06/2.17  tff(f_51, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 6.06/2.17  tff(f_61, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 6.06/2.17  tff(f_47, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 6.06/2.17  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 6.06/2.17  tff(f_40, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k10_relat_1(k5_relat_1(B, C), A) = k10_relat_1(B, k10_relat_1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t181_relat_1)).
% 6.06/2.17  tff(c_28, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.06/2.17  tff(c_2, plain, (![B_2, A_1]: (k2_tarski(B_2, A_1)=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.06/2.17  tff(c_91, plain, (![A_31, B_32]: (k1_setfam_1(k2_tarski(A_31, B_32))=k3_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.06/2.17  tff(c_106, plain, (![B_33, A_34]: (k1_setfam_1(k2_tarski(B_33, A_34))=k3_xboole_0(A_34, B_33))), inference(superposition, [status(thm), theory('equality')], [c_2, c_91])).
% 6.06/2.17  tff(c_8, plain, (![A_8, B_9]: (k1_setfam_1(k2_tarski(A_8, B_9))=k3_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.06/2.17  tff(c_112, plain, (![B_33, A_34]: (k3_xboole_0(B_33, A_34)=k3_xboole_0(A_34, B_33))), inference(superposition, [status(thm), theory('equality')], [c_106, c_8])).
% 6.06/2.17  tff(c_20, plain, (![A_20]: (v1_relat_1(k6_relat_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.06/2.17  tff(c_14, plain, (![A_17]: (k1_relat_1(k6_relat_1(A_17))=A_17)), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.06/2.17  tff(c_24, plain, (![B_22, A_21]: (k5_relat_1(k6_relat_1(B_22), k6_relat_1(A_21))=k6_relat_1(k3_xboole_0(A_21, B_22)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.06/2.17  tff(c_211, plain, (![A_46, B_47]: (k10_relat_1(A_46, k1_relat_1(B_47))=k1_relat_1(k5_relat_1(A_46, B_47)) | ~v1_relat_1(B_47) | ~v1_relat_1(A_46))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.06/2.17  tff(c_220, plain, (![A_46, A_17]: (k1_relat_1(k5_relat_1(A_46, k6_relat_1(A_17)))=k10_relat_1(A_46, A_17) | ~v1_relat_1(k6_relat_1(A_17)) | ~v1_relat_1(A_46))), inference(superposition, [status(thm), theory('equality')], [c_14, c_211])).
% 6.06/2.17  tff(c_252, plain, (![A_51, A_52]: (k1_relat_1(k5_relat_1(A_51, k6_relat_1(A_52)))=k10_relat_1(A_51, A_52) | ~v1_relat_1(A_51))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_220])).
% 6.06/2.17  tff(c_264, plain, (![A_21, B_22]: (k1_relat_1(k6_relat_1(k3_xboole_0(A_21, B_22)))=k10_relat_1(k6_relat_1(B_22), A_21) | ~v1_relat_1(k6_relat_1(B_22)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_252])).
% 6.06/2.17  tff(c_272, plain, (![B_22, A_21]: (k10_relat_1(k6_relat_1(B_22), A_21)=k3_xboole_0(A_21, B_22))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_14, c_264])).
% 6.06/2.17  tff(c_18, plain, (![A_18, B_19]: (k5_relat_1(k6_relat_1(A_18), B_19)=k7_relat_1(B_19, A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.06/2.17  tff(c_225, plain, (![B_48, C_49, A_50]: (k10_relat_1(k5_relat_1(B_48, C_49), A_50)=k10_relat_1(B_48, k10_relat_1(C_49, A_50)) | ~v1_relat_1(C_49) | ~v1_relat_1(B_48))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.06/2.17  tff(c_245, plain, (![A_18, B_19, A_50]: (k10_relat_1(k6_relat_1(A_18), k10_relat_1(B_19, A_50))=k10_relat_1(k7_relat_1(B_19, A_18), A_50) | ~v1_relat_1(B_19) | ~v1_relat_1(k6_relat_1(A_18)) | ~v1_relat_1(B_19))), inference(superposition, [status(thm), theory('equality')], [c_18, c_225])).
% 6.06/2.17  tff(c_251, plain, (![A_18, B_19, A_50]: (k10_relat_1(k6_relat_1(A_18), k10_relat_1(B_19, A_50))=k10_relat_1(k7_relat_1(B_19, A_18), A_50) | ~v1_relat_1(B_19))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_245])).
% 6.06/2.17  tff(c_1176, plain, (![B_74, A_75, A_76]: (k3_xboole_0(k10_relat_1(B_74, A_75), A_76)=k10_relat_1(k7_relat_1(B_74, A_76), A_75) | ~v1_relat_1(B_74))), inference(demodulation, [status(thm), theory('equality')], [c_272, c_251])).
% 6.06/2.17  tff(c_3399, plain, (![A_121, B_122, A_123]: (k3_xboole_0(A_121, k10_relat_1(B_122, A_123))=k10_relat_1(k7_relat_1(B_122, A_121), A_123) | ~v1_relat_1(B_122))), inference(superposition, [status(thm), theory('equality')], [c_112, c_1176])).
% 6.06/2.17  tff(c_26, plain, (k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))!=k10_relat_1(k7_relat_1('#skF_3', '#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.06/2.17  tff(c_3493, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3399, c_26])).
% 6.06/2.17  tff(c_3564, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_3493])).
% 6.06/2.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.06/2.17  
% 6.06/2.17  Inference rules
% 6.06/2.17  ----------------------
% 6.06/2.17  #Ref     : 0
% 6.06/2.17  #Sup     : 920
% 6.06/2.17  #Fact    : 0
% 6.06/2.17  #Define  : 0
% 6.06/2.17  #Split   : 0
% 6.06/2.17  #Chain   : 0
% 6.06/2.17  #Close   : 0
% 6.06/2.17  
% 6.06/2.17  Ordering : KBO
% 6.06/2.17  
% 6.06/2.17  Simplification rules
% 6.06/2.17  ----------------------
% 6.06/2.17  #Subsume      : 146
% 6.06/2.17  #Demod        : 535
% 6.06/2.17  #Tautology    : 172
% 6.06/2.17  #SimpNegUnit  : 0
% 6.06/2.17  #BackRed      : 0
% 6.06/2.17  
% 6.06/2.17  #Partial instantiations: 0
% 6.06/2.17  #Strategies tried      : 1
% 6.06/2.17  
% 6.06/2.17  Timing (in seconds)
% 6.06/2.17  ----------------------
% 6.06/2.18  Preprocessing        : 0.29
% 6.06/2.18  Parsing              : 0.15
% 6.06/2.18  CNF conversion       : 0.02
% 6.06/2.18  Main loop            : 1.14
% 6.06/2.18  Inferencing          : 0.30
% 6.06/2.18  Reduction            : 0.62
% 6.06/2.18  Demodulation         : 0.57
% 6.06/2.18  BG Simplification    : 0.05
% 6.06/2.18  Subsumption          : 0.13
% 6.06/2.18  Abstraction          : 0.07
% 6.06/2.18  MUC search           : 0.00
% 6.06/2.18  Cooper               : 0.00
% 6.06/2.18  Total                : 1.46
% 6.06/2.18  Index Insertion      : 0.00
% 6.06/2.18  Index Deletion       : 0.00
% 6.06/2.18  Index Matching       : 0.00
% 6.06/2.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
