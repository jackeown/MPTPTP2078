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
% DateTime   : Thu Dec  3 10:04:31 EST 2020

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.50s
% Verified   : 
% Statistics : Number of formulae       :   47 (  60 expanded)
%              Number of leaves         :   27 (  34 expanded)
%              Depth                    :    9
%              Number of atoms          :   54 (  75 expanded)
%              Number of equality atoms :   24 (  30 expanded)
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

tff(f_68,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_51,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k10_relat_1(k5_relat_1(B,C),A) = k10_relat_1(B,k10_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t181_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_28,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_22,plain,(
    ! [A_22] : v1_relat_1(k6_relat_1(A_22)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_14,plain,(
    ! [A_17] : k1_relat_1(k6_relat_1(A_17)) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_118,plain,(
    ! [B_38,A_39] :
      ( k3_xboole_0(k1_relat_1(B_38),A_39) = k1_relat_1(k7_relat_1(B_38,A_39))
      | ~ v1_relat_1(B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_141,plain,(
    ! [A_17,A_39] :
      ( k1_relat_1(k7_relat_1(k6_relat_1(A_17),A_39)) = k3_xboole_0(A_17,A_39)
      | ~ v1_relat_1(k6_relat_1(A_17)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_118])).

tff(c_145,plain,(
    ! [A_17,A_39] : k1_relat_1(k7_relat_1(k6_relat_1(A_17),A_39)) = k3_xboole_0(A_17,A_39) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_141])).

tff(c_20,plain,(
    ! [A_20,B_21] :
      ( k5_relat_1(k6_relat_1(A_20),B_21) = k7_relat_1(B_21,A_20)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_197,plain,(
    ! [A_44,B_45] :
      ( k10_relat_1(A_44,k1_relat_1(B_45)) = k1_relat_1(k5_relat_1(A_44,B_45))
      | ~ v1_relat_1(B_45)
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_209,plain,(
    ! [A_44,A_17] :
      ( k1_relat_1(k5_relat_1(A_44,k6_relat_1(A_17))) = k10_relat_1(A_44,A_17)
      | ~ v1_relat_1(k6_relat_1(A_17))
      | ~ v1_relat_1(A_44) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_197])).

tff(c_214,plain,(
    ! [A_46,A_47] :
      ( k1_relat_1(k5_relat_1(A_46,k6_relat_1(A_47))) = k10_relat_1(A_46,A_47)
      | ~ v1_relat_1(A_46) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_209])).

tff(c_233,plain,(
    ! [A_47,A_20] :
      ( k1_relat_1(k7_relat_1(k6_relat_1(A_47),A_20)) = k10_relat_1(k6_relat_1(A_20),A_47)
      | ~ v1_relat_1(k6_relat_1(A_20))
      | ~ v1_relat_1(k6_relat_1(A_47)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_214])).

tff(c_237,plain,(
    ! [A_20,A_47] : k10_relat_1(k6_relat_1(A_20),A_47) = k3_xboole_0(A_47,A_20) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_22,c_145,c_233])).

tff(c_259,plain,(
    ! [B_50,C_51,A_52] :
      ( k10_relat_1(k5_relat_1(B_50,C_51),A_52) = k10_relat_1(B_50,k10_relat_1(C_51,A_52))
      | ~ v1_relat_1(C_51)
      | ~ v1_relat_1(B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_276,plain,(
    ! [A_20,B_21,A_52] :
      ( k10_relat_1(k6_relat_1(A_20),k10_relat_1(B_21,A_52)) = k10_relat_1(k7_relat_1(B_21,A_20),A_52)
      | ~ v1_relat_1(B_21)
      | ~ v1_relat_1(k6_relat_1(A_20))
      | ~ v1_relat_1(B_21) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_259])).

tff(c_314,plain,(
    ! [B_55,A_56,A_57] :
      ( k3_xboole_0(k10_relat_1(B_55,A_56),A_57) = k10_relat_1(k7_relat_1(B_55,A_57),A_56)
      | ~ v1_relat_1(B_55) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_237,c_276])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_447,plain,(
    ! [A_64,B_65,A_66] :
      ( k3_xboole_0(A_64,k10_relat_1(B_65,A_66)) = k10_relat_1(k7_relat_1(B_65,A_64),A_66)
      | ~ v1_relat_1(B_65) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_314,c_2])).

tff(c_26,plain,(
    k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2')) != k10_relat_1(k7_relat_1('#skF_3','#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_461,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_447,c_26])).

tff(c_506,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_461])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:47:45 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.18/1.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.37  
% 2.18/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.37  %$ v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.18/1.37  
% 2.18/1.37  %Foreground sorts:
% 2.18/1.37  
% 2.18/1.37  
% 2.18/1.37  %Background operators:
% 2.18/1.37  
% 2.18/1.37  
% 2.18/1.37  %Foreground operators:
% 2.18/1.37  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.18/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.18/1.37  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.18/1.37  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.18/1.37  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.18/1.37  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.18/1.37  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.18/1.37  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.18/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.18/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.18/1.37  tff('#skF_1', type, '#skF_1': $i).
% 2.18/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.18/1.37  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.18/1.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.18/1.37  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.18/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.18/1.37  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.18/1.37  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.18/1.37  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.18/1.37  
% 2.50/1.38  tff(f_68, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 2.50/1.38  tff(f_63, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.50/1.38  tff(f_51, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.50/1.38  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 2.50/1.38  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 2.50/1.38  tff(f_47, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 2.50/1.38  tff(f_40, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k10_relat_1(k5_relat_1(B, C), A) = k10_relat_1(B, k10_relat_1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t181_relat_1)).
% 2.50/1.38  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.50/1.38  tff(c_28, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.50/1.38  tff(c_22, plain, (![A_22]: (v1_relat_1(k6_relat_1(A_22)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.50/1.38  tff(c_14, plain, (![A_17]: (k1_relat_1(k6_relat_1(A_17))=A_17)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.50/1.38  tff(c_118, plain, (![B_38, A_39]: (k3_xboole_0(k1_relat_1(B_38), A_39)=k1_relat_1(k7_relat_1(B_38, A_39)) | ~v1_relat_1(B_38))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.50/1.38  tff(c_141, plain, (![A_17, A_39]: (k1_relat_1(k7_relat_1(k6_relat_1(A_17), A_39))=k3_xboole_0(A_17, A_39) | ~v1_relat_1(k6_relat_1(A_17)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_118])).
% 2.50/1.38  tff(c_145, plain, (![A_17, A_39]: (k1_relat_1(k7_relat_1(k6_relat_1(A_17), A_39))=k3_xboole_0(A_17, A_39))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_141])).
% 2.50/1.38  tff(c_20, plain, (![A_20, B_21]: (k5_relat_1(k6_relat_1(A_20), B_21)=k7_relat_1(B_21, A_20) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.50/1.38  tff(c_197, plain, (![A_44, B_45]: (k10_relat_1(A_44, k1_relat_1(B_45))=k1_relat_1(k5_relat_1(A_44, B_45)) | ~v1_relat_1(B_45) | ~v1_relat_1(A_44))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.50/1.38  tff(c_209, plain, (![A_44, A_17]: (k1_relat_1(k5_relat_1(A_44, k6_relat_1(A_17)))=k10_relat_1(A_44, A_17) | ~v1_relat_1(k6_relat_1(A_17)) | ~v1_relat_1(A_44))), inference(superposition, [status(thm), theory('equality')], [c_14, c_197])).
% 2.50/1.38  tff(c_214, plain, (![A_46, A_47]: (k1_relat_1(k5_relat_1(A_46, k6_relat_1(A_47)))=k10_relat_1(A_46, A_47) | ~v1_relat_1(A_46))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_209])).
% 2.50/1.38  tff(c_233, plain, (![A_47, A_20]: (k1_relat_1(k7_relat_1(k6_relat_1(A_47), A_20))=k10_relat_1(k6_relat_1(A_20), A_47) | ~v1_relat_1(k6_relat_1(A_20)) | ~v1_relat_1(k6_relat_1(A_47)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_214])).
% 2.50/1.38  tff(c_237, plain, (![A_20, A_47]: (k10_relat_1(k6_relat_1(A_20), A_47)=k3_xboole_0(A_47, A_20))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_22, c_145, c_233])).
% 2.50/1.38  tff(c_259, plain, (![B_50, C_51, A_52]: (k10_relat_1(k5_relat_1(B_50, C_51), A_52)=k10_relat_1(B_50, k10_relat_1(C_51, A_52)) | ~v1_relat_1(C_51) | ~v1_relat_1(B_50))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.50/1.38  tff(c_276, plain, (![A_20, B_21, A_52]: (k10_relat_1(k6_relat_1(A_20), k10_relat_1(B_21, A_52))=k10_relat_1(k7_relat_1(B_21, A_20), A_52) | ~v1_relat_1(B_21) | ~v1_relat_1(k6_relat_1(A_20)) | ~v1_relat_1(B_21))), inference(superposition, [status(thm), theory('equality')], [c_20, c_259])).
% 2.50/1.38  tff(c_314, plain, (![B_55, A_56, A_57]: (k3_xboole_0(k10_relat_1(B_55, A_56), A_57)=k10_relat_1(k7_relat_1(B_55, A_57), A_56) | ~v1_relat_1(B_55))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_237, c_276])).
% 2.50/1.38  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.50/1.38  tff(c_447, plain, (![A_64, B_65, A_66]: (k3_xboole_0(A_64, k10_relat_1(B_65, A_66))=k10_relat_1(k7_relat_1(B_65, A_64), A_66) | ~v1_relat_1(B_65))), inference(superposition, [status(thm), theory('equality')], [c_314, c_2])).
% 2.50/1.38  tff(c_26, plain, (k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))!=k10_relat_1(k7_relat_1('#skF_3', '#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.50/1.38  tff(c_461, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_447, c_26])).
% 2.50/1.38  tff(c_506, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_461])).
% 2.50/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.50/1.38  
% 2.50/1.38  Inference rules
% 2.50/1.38  ----------------------
% 2.50/1.38  #Ref     : 0
% 2.50/1.38  #Sup     : 116
% 2.50/1.38  #Fact    : 0
% 2.50/1.38  #Define  : 0
% 2.50/1.38  #Split   : 0
% 2.50/1.38  #Chain   : 0
% 2.50/1.38  #Close   : 0
% 2.50/1.38  
% 2.50/1.38  Ordering : KBO
% 2.50/1.38  
% 2.50/1.38  Simplification rules
% 2.50/1.38  ----------------------
% 2.50/1.38  #Subsume      : 10
% 2.50/1.38  #Demod        : 25
% 2.50/1.38  #Tautology    : 45
% 2.50/1.38  #SimpNegUnit  : 0
% 2.50/1.38  #BackRed      : 0
% 2.50/1.38  
% 2.50/1.38  #Partial instantiations: 0
% 2.50/1.38  #Strategies tried      : 1
% 2.50/1.38  
% 2.50/1.38  Timing (in seconds)
% 2.50/1.38  ----------------------
% 2.50/1.38  Preprocessing        : 0.32
% 2.50/1.38  Parsing              : 0.17
% 2.50/1.38  CNF conversion       : 0.02
% 2.50/1.38  Main loop            : 0.25
% 2.50/1.38  Inferencing          : 0.10
% 2.50/1.38  Reduction            : 0.08
% 2.50/1.38  Demodulation         : 0.07
% 2.50/1.38  BG Simplification    : 0.02
% 2.50/1.39  Subsumption          : 0.04
% 2.50/1.39  Abstraction          : 0.02
% 2.50/1.39  MUC search           : 0.00
% 2.50/1.39  Cooper               : 0.00
% 2.50/1.39  Total                : 0.60
% 2.50/1.39  Index Insertion      : 0.00
% 2.50/1.39  Index Deletion       : 0.00
% 2.50/1.39  Index Matching       : 0.00
% 2.50/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
