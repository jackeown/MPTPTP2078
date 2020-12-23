%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:30 EST 2020

% Result     : Theorem 2.92s
% Output     : CNFRefutation 2.92s
% Verified   : 
% Statistics : Number of formulae       :   58 (  72 expanded)
%              Number of leaves         :   34 (  42 expanded)
%              Depth                    :    9
%              Number of atoms          :   59 (  81 expanded)
%              Number of equality atoms :   29 (  36 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_82,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

tff(f_77,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_65,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k10_relat_1(k5_relat_1(B,C),A) = k10_relat_1(B,k10_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t181_relat_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_43,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_40,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_34,plain,(
    ! [A_48] : v1_relat_1(k6_relat_1(A_48)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_26,plain,(
    ! [A_43] : k1_relat_1(k6_relat_1(A_43)) = A_43 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_239,plain,(
    ! [B_74,A_75] :
      ( k3_xboole_0(k1_relat_1(B_74),A_75) = k1_relat_1(k7_relat_1(B_74,A_75))
      | ~ v1_relat_1(B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_262,plain,(
    ! [A_43,A_75] :
      ( k1_relat_1(k7_relat_1(k6_relat_1(A_43),A_75)) = k3_xboole_0(A_43,A_75)
      | ~ v1_relat_1(k6_relat_1(A_43)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_239])).

tff(c_266,plain,(
    ! [A_43,A_75] : k1_relat_1(k7_relat_1(k6_relat_1(A_43),A_75)) = k3_xboole_0(A_43,A_75) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_262])).

tff(c_32,plain,(
    ! [A_46,B_47] :
      ( k5_relat_1(k6_relat_1(A_46),B_47) = k7_relat_1(B_47,A_46)
      | ~ v1_relat_1(B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_389,plain,(
    ! [A_88,B_89] :
      ( k10_relat_1(A_88,k1_relat_1(B_89)) = k1_relat_1(k5_relat_1(A_88,B_89))
      | ~ v1_relat_1(B_89)
      | ~ v1_relat_1(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_401,plain,(
    ! [A_88,A_43] :
      ( k1_relat_1(k5_relat_1(A_88,k6_relat_1(A_43))) = k10_relat_1(A_88,A_43)
      | ~ v1_relat_1(k6_relat_1(A_43))
      | ~ v1_relat_1(A_88) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_389])).

tff(c_406,plain,(
    ! [A_90,A_91] :
      ( k1_relat_1(k5_relat_1(A_90,k6_relat_1(A_91))) = k10_relat_1(A_90,A_91)
      | ~ v1_relat_1(A_90) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_401])).

tff(c_428,plain,(
    ! [A_91,A_46] :
      ( k1_relat_1(k7_relat_1(k6_relat_1(A_91),A_46)) = k10_relat_1(k6_relat_1(A_46),A_91)
      | ~ v1_relat_1(k6_relat_1(A_46))
      | ~ v1_relat_1(k6_relat_1(A_91)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_406])).

tff(c_432,plain,(
    ! [A_46,A_91] : k10_relat_1(k6_relat_1(A_46),A_91) = k3_xboole_0(A_91,A_46) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_34,c_266,c_428])).

tff(c_623,plain,(
    ! [B_107,C_108,A_109] :
      ( k10_relat_1(k5_relat_1(B_107,C_108),A_109) = k10_relat_1(B_107,k10_relat_1(C_108,A_109))
      | ~ v1_relat_1(C_108)
      | ~ v1_relat_1(B_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_643,plain,(
    ! [A_46,B_47,A_109] :
      ( k10_relat_1(k6_relat_1(A_46),k10_relat_1(B_47,A_109)) = k10_relat_1(k7_relat_1(B_47,A_46),A_109)
      | ~ v1_relat_1(B_47)
      | ~ v1_relat_1(k6_relat_1(A_46))
      | ~ v1_relat_1(B_47) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_623])).

tff(c_773,plain,(
    ! [B_124,A_125,A_126] :
      ( k3_xboole_0(k10_relat_1(B_124,A_125),A_126) = k10_relat_1(k7_relat_1(B_124,A_126),A_125)
      | ~ v1_relat_1(B_124) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_432,c_643])).

tff(c_4,plain,(
    ! [B_4,A_3] : k2_tarski(B_4,A_3) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_94,plain,(
    ! [A_55,B_56] : k1_setfam_1(k2_tarski(A_55,B_56)) = k3_xboole_0(A_55,B_56) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_118,plain,(
    ! [B_59,A_60] : k1_setfam_1(k2_tarski(B_59,A_60)) = k3_xboole_0(A_60,B_59) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_94])).

tff(c_18,plain,(
    ! [A_32,B_33] : k1_setfam_1(k2_tarski(A_32,B_33)) = k3_xboole_0(A_32,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_124,plain,(
    ! [B_59,A_60] : k3_xboole_0(B_59,A_60) = k3_xboole_0(A_60,B_59) ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_18])).

tff(c_857,plain,(
    ! [A_127,B_128,A_129] :
      ( k3_xboole_0(A_127,k10_relat_1(B_128,A_129)) = k10_relat_1(k7_relat_1(B_128,A_127),A_129)
      | ~ v1_relat_1(B_128) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_773,c_124])).

tff(c_38,plain,(
    k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2')) != k10_relat_1(k7_relat_1('#skF_3','#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_889,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_857,c_38])).

tff(c_928,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_889])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:57:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.92/1.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.92/1.42  
% 2.92/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.92/1.42  %$ v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.92/1.42  
% 2.92/1.42  %Foreground sorts:
% 2.92/1.42  
% 2.92/1.42  
% 2.92/1.42  %Background operators:
% 2.92/1.42  
% 2.92/1.42  
% 2.92/1.42  %Foreground operators:
% 2.92/1.42  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.92/1.42  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.92/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.92/1.42  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.92/1.42  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.92/1.42  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.92/1.42  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.92/1.42  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.92/1.42  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.92/1.42  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.92/1.42  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.92/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.92/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.92/1.42  tff('#skF_1', type, '#skF_1': $i).
% 2.92/1.42  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.92/1.42  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.92/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.92/1.42  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.92/1.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.92/1.42  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.92/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.92/1.42  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.92/1.42  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.92/1.42  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.92/1.42  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.92/1.42  
% 2.92/1.43  tff(f_82, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 2.92/1.43  tff(f_77, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.92/1.43  tff(f_65, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.92/1.43  tff(f_69, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 2.92/1.43  tff(f_73, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 2.92/1.43  tff(f_61, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 2.92/1.43  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k10_relat_1(k5_relat_1(B, C), A) = k10_relat_1(B, k10_relat_1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t181_relat_1)).
% 2.92/1.43  tff(f_29, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.92/1.43  tff(f_43, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.92/1.43  tff(c_40, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.92/1.43  tff(c_34, plain, (![A_48]: (v1_relat_1(k6_relat_1(A_48)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.92/1.43  tff(c_26, plain, (![A_43]: (k1_relat_1(k6_relat_1(A_43))=A_43)), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.92/1.43  tff(c_239, plain, (![B_74, A_75]: (k3_xboole_0(k1_relat_1(B_74), A_75)=k1_relat_1(k7_relat_1(B_74, A_75)) | ~v1_relat_1(B_74))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.92/1.43  tff(c_262, plain, (![A_43, A_75]: (k1_relat_1(k7_relat_1(k6_relat_1(A_43), A_75))=k3_xboole_0(A_43, A_75) | ~v1_relat_1(k6_relat_1(A_43)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_239])).
% 2.92/1.43  tff(c_266, plain, (![A_43, A_75]: (k1_relat_1(k7_relat_1(k6_relat_1(A_43), A_75))=k3_xboole_0(A_43, A_75))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_262])).
% 2.92/1.43  tff(c_32, plain, (![A_46, B_47]: (k5_relat_1(k6_relat_1(A_46), B_47)=k7_relat_1(B_47, A_46) | ~v1_relat_1(B_47))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.92/1.43  tff(c_389, plain, (![A_88, B_89]: (k10_relat_1(A_88, k1_relat_1(B_89))=k1_relat_1(k5_relat_1(A_88, B_89)) | ~v1_relat_1(B_89) | ~v1_relat_1(A_88))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.92/1.43  tff(c_401, plain, (![A_88, A_43]: (k1_relat_1(k5_relat_1(A_88, k6_relat_1(A_43)))=k10_relat_1(A_88, A_43) | ~v1_relat_1(k6_relat_1(A_43)) | ~v1_relat_1(A_88))), inference(superposition, [status(thm), theory('equality')], [c_26, c_389])).
% 2.92/1.43  tff(c_406, plain, (![A_90, A_91]: (k1_relat_1(k5_relat_1(A_90, k6_relat_1(A_91)))=k10_relat_1(A_90, A_91) | ~v1_relat_1(A_90))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_401])).
% 2.92/1.43  tff(c_428, plain, (![A_91, A_46]: (k1_relat_1(k7_relat_1(k6_relat_1(A_91), A_46))=k10_relat_1(k6_relat_1(A_46), A_91) | ~v1_relat_1(k6_relat_1(A_46)) | ~v1_relat_1(k6_relat_1(A_91)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_406])).
% 2.92/1.43  tff(c_432, plain, (![A_46, A_91]: (k10_relat_1(k6_relat_1(A_46), A_91)=k3_xboole_0(A_91, A_46))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_34, c_266, c_428])).
% 2.92/1.43  tff(c_623, plain, (![B_107, C_108, A_109]: (k10_relat_1(k5_relat_1(B_107, C_108), A_109)=k10_relat_1(B_107, k10_relat_1(C_108, A_109)) | ~v1_relat_1(C_108) | ~v1_relat_1(B_107))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.92/1.43  tff(c_643, plain, (![A_46, B_47, A_109]: (k10_relat_1(k6_relat_1(A_46), k10_relat_1(B_47, A_109))=k10_relat_1(k7_relat_1(B_47, A_46), A_109) | ~v1_relat_1(B_47) | ~v1_relat_1(k6_relat_1(A_46)) | ~v1_relat_1(B_47))), inference(superposition, [status(thm), theory('equality')], [c_32, c_623])).
% 2.92/1.43  tff(c_773, plain, (![B_124, A_125, A_126]: (k3_xboole_0(k10_relat_1(B_124, A_125), A_126)=k10_relat_1(k7_relat_1(B_124, A_126), A_125) | ~v1_relat_1(B_124))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_432, c_643])).
% 2.92/1.43  tff(c_4, plain, (![B_4, A_3]: (k2_tarski(B_4, A_3)=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.92/1.43  tff(c_94, plain, (![A_55, B_56]: (k1_setfam_1(k2_tarski(A_55, B_56))=k3_xboole_0(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.92/1.43  tff(c_118, plain, (![B_59, A_60]: (k1_setfam_1(k2_tarski(B_59, A_60))=k3_xboole_0(A_60, B_59))), inference(superposition, [status(thm), theory('equality')], [c_4, c_94])).
% 2.92/1.43  tff(c_18, plain, (![A_32, B_33]: (k1_setfam_1(k2_tarski(A_32, B_33))=k3_xboole_0(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.92/1.43  tff(c_124, plain, (![B_59, A_60]: (k3_xboole_0(B_59, A_60)=k3_xboole_0(A_60, B_59))), inference(superposition, [status(thm), theory('equality')], [c_118, c_18])).
% 2.92/1.43  tff(c_857, plain, (![A_127, B_128, A_129]: (k3_xboole_0(A_127, k10_relat_1(B_128, A_129))=k10_relat_1(k7_relat_1(B_128, A_127), A_129) | ~v1_relat_1(B_128))), inference(superposition, [status(thm), theory('equality')], [c_773, c_124])).
% 2.92/1.43  tff(c_38, plain, (k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))!=k10_relat_1(k7_relat_1('#skF_3', '#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.92/1.43  tff(c_889, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_857, c_38])).
% 2.92/1.43  tff(c_928, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_889])).
% 2.92/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.92/1.43  
% 2.92/1.43  Inference rules
% 2.92/1.43  ----------------------
% 2.92/1.43  #Ref     : 0
% 2.92/1.43  #Sup     : 222
% 2.92/1.43  #Fact    : 0
% 2.92/1.43  #Define  : 0
% 2.92/1.43  #Split   : 0
% 2.92/1.43  #Chain   : 0
% 2.92/1.43  #Close   : 0
% 2.92/1.43  
% 2.92/1.43  Ordering : KBO
% 2.92/1.43  
% 2.92/1.43  Simplification rules
% 2.92/1.43  ----------------------
% 2.92/1.43  #Subsume      : 16
% 2.92/1.43  #Demod        : 59
% 2.92/1.43  #Tautology    : 100
% 2.92/1.43  #SimpNegUnit  : 0
% 2.92/1.43  #BackRed      : 0
% 2.92/1.43  
% 2.92/1.43  #Partial instantiations: 0
% 2.92/1.43  #Strategies tried      : 1
% 2.92/1.43  
% 2.92/1.43  Timing (in seconds)
% 2.92/1.43  ----------------------
% 2.92/1.43  Preprocessing        : 0.32
% 2.92/1.43  Parsing              : 0.17
% 2.92/1.43  CNF conversion       : 0.02
% 2.92/1.43  Main loop            : 0.35
% 2.92/1.43  Inferencing          : 0.13
% 2.92/1.43  Reduction            : 0.13
% 2.92/1.43  Demodulation         : 0.10
% 2.92/1.43  BG Simplification    : 0.03
% 2.92/1.43  Subsumption          : 0.05
% 2.92/1.43  Abstraction          : 0.02
% 2.92/1.43  MUC search           : 0.00
% 2.92/1.43  Cooper               : 0.00
% 2.92/1.43  Total                : 0.70
% 2.92/1.43  Index Insertion      : 0.00
% 2.92/1.43  Index Deletion       : 0.00
% 2.92/1.43  Index Matching       : 0.00
% 2.92/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
