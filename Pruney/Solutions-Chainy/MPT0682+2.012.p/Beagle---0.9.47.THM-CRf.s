%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:30 EST 2020

% Result     : Theorem 2.09s
% Output     : CNFRefutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :   46 (  60 expanded)
%              Number of leaves         :   26 (  34 expanded)
%              Depth                    :    8
%              Number of atoms          :   53 (  77 expanded)
%              Number of equality atoms :   23 (  30 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k8_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_66,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => k9_relat_1(k8_relat_1(A,C),B) = k3_xboole_0(A,k9_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t126_funct_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_53,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_59,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k9_relat_1(k5_relat_1(B,C),A) = k9_relat_1(C,k9_relat_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t159_relat_1)).

tff(c_28,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_18,plain,(
    ! [A_18] : v1_relat_1(k6_relat_1(A_18)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_16,plain,(
    ! [A_17] : k2_relat_1(k6_relat_1(A_17)) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_85,plain,(
    ! [B_34,A_35] :
      ( k5_relat_1(B_34,k6_relat_1(A_35)) = k8_relat_1(A_35,B_34)
      | ~ v1_relat_1(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_22,plain,(
    ! [B_20,A_19] : k5_relat_1(k6_relat_1(B_20),k6_relat_1(A_19)) = k6_relat_1(k3_xboole_0(A_19,B_20)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_92,plain,(
    ! [A_35,B_20] :
      ( k8_relat_1(A_35,k6_relat_1(B_20)) = k6_relat_1(k3_xboole_0(A_35,B_20))
      | ~ v1_relat_1(k6_relat_1(B_20)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_22])).

tff(c_101,plain,(
    ! [A_35,B_20] : k8_relat_1(A_35,k6_relat_1(B_20)) = k6_relat_1(k3_xboole_0(A_35,B_20)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_92])).

tff(c_8,plain,(
    ! [B_9,A_8] :
      ( k5_relat_1(B_9,k6_relat_1(A_8)) = k8_relat_1(A_8,B_9)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_115,plain,(
    ! [B_38,A_39] :
      ( k9_relat_1(B_38,k2_relat_1(A_39)) = k2_relat_1(k5_relat_1(A_39,B_38))
      | ~ v1_relat_1(B_38)
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_124,plain,(
    ! [A_17,B_38] :
      ( k2_relat_1(k5_relat_1(k6_relat_1(A_17),B_38)) = k9_relat_1(B_38,A_17)
      | ~ v1_relat_1(B_38)
      | ~ v1_relat_1(k6_relat_1(A_17)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_115])).

tff(c_156,plain,(
    ! [A_43,B_44] :
      ( k2_relat_1(k5_relat_1(k6_relat_1(A_43),B_44)) = k9_relat_1(B_44,A_43)
      | ~ v1_relat_1(B_44) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_124])).

tff(c_169,plain,(
    ! [A_8,A_43] :
      ( k2_relat_1(k8_relat_1(A_8,k6_relat_1(A_43))) = k9_relat_1(k6_relat_1(A_8),A_43)
      | ~ v1_relat_1(k6_relat_1(A_8))
      | ~ v1_relat_1(k6_relat_1(A_43)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_156])).

tff(c_176,plain,(
    ! [A_8,A_43] : k9_relat_1(k6_relat_1(A_8),A_43) = k3_xboole_0(A_8,A_43) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_16,c_101,c_169])).

tff(c_129,plain,(
    ! [B_40,C_41,A_42] :
      ( k9_relat_1(k5_relat_1(B_40,C_41),A_42) = k9_relat_1(C_41,k9_relat_1(B_40,A_42))
      | ~ v1_relat_1(C_41)
      | ~ v1_relat_1(B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_146,plain,(
    ! [A_8,B_9,A_42] :
      ( k9_relat_1(k6_relat_1(A_8),k9_relat_1(B_9,A_42)) = k9_relat_1(k8_relat_1(A_8,B_9),A_42)
      | ~ v1_relat_1(k6_relat_1(A_8))
      | ~ v1_relat_1(B_9)
      | ~ v1_relat_1(B_9) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_129])).

tff(c_153,plain,(
    ! [A_8,B_9,A_42] :
      ( k9_relat_1(k6_relat_1(A_8),k9_relat_1(B_9,A_42)) = k9_relat_1(k8_relat_1(A_8,B_9),A_42)
      | ~ v1_relat_1(B_9) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_146])).

tff(c_298,plain,(
    ! [A_54,B_55,A_56] :
      ( k9_relat_1(k8_relat_1(A_54,B_55),A_56) = k3_xboole_0(A_54,k9_relat_1(B_55,A_56))
      | ~ v1_relat_1(B_55) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_153])).

tff(c_24,plain,(
    k9_relat_1(k8_relat_1('#skF_1','#skF_3'),'#skF_2') != k3_xboole_0('#skF_1',k9_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_308,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_298,c_24])).

tff(c_323,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_308])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:38:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.09/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.27  
% 2.09/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.28  %$ v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k8_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.09/1.28  
% 2.09/1.28  %Foreground sorts:
% 2.09/1.28  
% 2.09/1.28  
% 2.09/1.28  %Background operators:
% 2.09/1.28  
% 2.09/1.28  
% 2.09/1.28  %Foreground operators:
% 2.09/1.28  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.09/1.28  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.09/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.09/1.28  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.09/1.28  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.09/1.28  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.09/1.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.09/1.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.09/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.09/1.28  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.09/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.09/1.28  tff('#skF_1', type, '#skF_1': $i).
% 2.09/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.09/1.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.09/1.28  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.09/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.09/1.28  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.09/1.28  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.09/1.28  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.09/1.28  
% 2.09/1.29  tff(f_66, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (k9_relat_1(k8_relat_1(A, C), B) = k3_xboole_0(A, k9_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t126_funct_1)).
% 2.09/1.29  tff(f_57, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.09/1.29  tff(f_53, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.09/1.29  tff(f_35, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_relat_1)).
% 2.09/1.29  tff(f_59, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 2.09/1.29  tff(f_49, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t160_relat_1)).
% 2.09/1.29  tff(f_42, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k9_relat_1(k5_relat_1(B, C), A) = k9_relat_1(C, k9_relat_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t159_relat_1)).
% 2.09/1.29  tff(c_28, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.09/1.29  tff(c_18, plain, (![A_18]: (v1_relat_1(k6_relat_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.09/1.29  tff(c_16, plain, (![A_17]: (k2_relat_1(k6_relat_1(A_17))=A_17)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.09/1.29  tff(c_85, plain, (![B_34, A_35]: (k5_relat_1(B_34, k6_relat_1(A_35))=k8_relat_1(A_35, B_34) | ~v1_relat_1(B_34))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.09/1.29  tff(c_22, plain, (![B_20, A_19]: (k5_relat_1(k6_relat_1(B_20), k6_relat_1(A_19))=k6_relat_1(k3_xboole_0(A_19, B_20)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.09/1.29  tff(c_92, plain, (![A_35, B_20]: (k8_relat_1(A_35, k6_relat_1(B_20))=k6_relat_1(k3_xboole_0(A_35, B_20)) | ~v1_relat_1(k6_relat_1(B_20)))), inference(superposition, [status(thm), theory('equality')], [c_85, c_22])).
% 2.09/1.29  tff(c_101, plain, (![A_35, B_20]: (k8_relat_1(A_35, k6_relat_1(B_20))=k6_relat_1(k3_xboole_0(A_35, B_20)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_92])).
% 2.09/1.29  tff(c_8, plain, (![B_9, A_8]: (k5_relat_1(B_9, k6_relat_1(A_8))=k8_relat_1(A_8, B_9) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.09/1.29  tff(c_115, plain, (![B_38, A_39]: (k9_relat_1(B_38, k2_relat_1(A_39))=k2_relat_1(k5_relat_1(A_39, B_38)) | ~v1_relat_1(B_38) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.09/1.29  tff(c_124, plain, (![A_17, B_38]: (k2_relat_1(k5_relat_1(k6_relat_1(A_17), B_38))=k9_relat_1(B_38, A_17) | ~v1_relat_1(B_38) | ~v1_relat_1(k6_relat_1(A_17)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_115])).
% 2.09/1.29  tff(c_156, plain, (![A_43, B_44]: (k2_relat_1(k5_relat_1(k6_relat_1(A_43), B_44))=k9_relat_1(B_44, A_43) | ~v1_relat_1(B_44))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_124])).
% 2.09/1.29  tff(c_169, plain, (![A_8, A_43]: (k2_relat_1(k8_relat_1(A_8, k6_relat_1(A_43)))=k9_relat_1(k6_relat_1(A_8), A_43) | ~v1_relat_1(k6_relat_1(A_8)) | ~v1_relat_1(k6_relat_1(A_43)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_156])).
% 2.09/1.29  tff(c_176, plain, (![A_8, A_43]: (k9_relat_1(k6_relat_1(A_8), A_43)=k3_xboole_0(A_8, A_43))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_16, c_101, c_169])).
% 2.09/1.29  tff(c_129, plain, (![B_40, C_41, A_42]: (k9_relat_1(k5_relat_1(B_40, C_41), A_42)=k9_relat_1(C_41, k9_relat_1(B_40, A_42)) | ~v1_relat_1(C_41) | ~v1_relat_1(B_40))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.09/1.29  tff(c_146, plain, (![A_8, B_9, A_42]: (k9_relat_1(k6_relat_1(A_8), k9_relat_1(B_9, A_42))=k9_relat_1(k8_relat_1(A_8, B_9), A_42) | ~v1_relat_1(k6_relat_1(A_8)) | ~v1_relat_1(B_9) | ~v1_relat_1(B_9))), inference(superposition, [status(thm), theory('equality')], [c_8, c_129])).
% 2.09/1.29  tff(c_153, plain, (![A_8, B_9, A_42]: (k9_relat_1(k6_relat_1(A_8), k9_relat_1(B_9, A_42))=k9_relat_1(k8_relat_1(A_8, B_9), A_42) | ~v1_relat_1(B_9))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_146])).
% 2.09/1.29  tff(c_298, plain, (![A_54, B_55, A_56]: (k9_relat_1(k8_relat_1(A_54, B_55), A_56)=k3_xboole_0(A_54, k9_relat_1(B_55, A_56)) | ~v1_relat_1(B_55))), inference(demodulation, [status(thm), theory('equality')], [c_176, c_153])).
% 2.09/1.29  tff(c_24, plain, (k9_relat_1(k8_relat_1('#skF_1', '#skF_3'), '#skF_2')!=k3_xboole_0('#skF_1', k9_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.09/1.29  tff(c_308, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_298, c_24])).
% 2.09/1.29  tff(c_323, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_308])).
% 2.09/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.29  
% 2.09/1.29  Inference rules
% 2.09/1.29  ----------------------
% 2.09/1.29  #Ref     : 0
% 2.09/1.29  #Sup     : 63
% 2.09/1.29  #Fact    : 0
% 2.09/1.29  #Define  : 0
% 2.09/1.29  #Split   : 0
% 2.09/1.29  #Chain   : 0
% 2.09/1.29  #Close   : 0
% 2.09/1.29  
% 2.09/1.29  Ordering : KBO
% 2.09/1.29  
% 2.09/1.29  Simplification rules
% 2.09/1.29  ----------------------
% 2.09/1.29  #Subsume      : 3
% 2.09/1.29  #Demod        : 49
% 2.09/1.29  #Tautology    : 37
% 2.09/1.29  #SimpNegUnit  : 0
% 2.09/1.29  #BackRed      : 0
% 2.09/1.29  
% 2.09/1.29  #Partial instantiations: 0
% 2.09/1.29  #Strategies tried      : 1
% 2.09/1.29  
% 2.09/1.29  Timing (in seconds)
% 2.09/1.29  ----------------------
% 2.09/1.29  Preprocessing        : 0.30
% 2.09/1.29  Parsing              : 0.16
% 2.09/1.29  CNF conversion       : 0.02
% 2.09/1.29  Main loop            : 0.20
% 2.09/1.29  Inferencing          : 0.08
% 2.09/1.29  Reduction            : 0.07
% 2.09/1.29  Demodulation         : 0.05
% 2.09/1.29  BG Simplification    : 0.01
% 2.09/1.29  Subsumption          : 0.03
% 2.09/1.29  Abstraction          : 0.01
% 2.09/1.29  MUC search           : 0.00
% 2.09/1.29  Cooper               : 0.00
% 2.09/1.29  Total                : 0.54
% 2.09/1.29  Index Insertion      : 0.00
% 2.09/1.29  Index Deletion       : 0.00
% 2.09/1.29  Index Matching       : 0.00
% 2.09/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
