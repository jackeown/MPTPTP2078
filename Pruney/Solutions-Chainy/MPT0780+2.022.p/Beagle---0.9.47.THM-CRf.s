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
% DateTime   : Thu Dec  3 10:06:42 EST 2020

% Result     : Theorem 3.32s
% Output     : CNFRefutation 3.32s
% Verified   : 
% Statistics : Number of formulae       :   59 (  74 expanded)
%              Number of leaves         :   32 (  41 expanded)
%              Depth                    :    8
%              Number of atoms          :   67 (  94 expanded)
%              Number of equality atoms :   32 (  43 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_wellord1 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_wellord1,type,(
    k2_wellord1: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_113,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k2_wellord1(k2_wellord1(C,B),A) = k2_wellord1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_wellord1)).

tff(f_88,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_70,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_90,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_102,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k2_wellord1(k2_wellord1(C,A),B) = k2_wellord1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_wellord1)).

tff(f_106,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k2_wellord1(k2_wellord1(C,A),B) = k2_wellord1(k2_wellord1(C,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_wellord1)).

tff(c_52,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_36,plain,(
    ! [A_32] : v1_relat_1(k6_relat_1(A_32)) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_28,plain,(
    ! [A_26] : k2_relat_1(k6_relat_1(A_26)) = A_26 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_40,plain,(
    ! [B_34,A_33] : k5_relat_1(k6_relat_1(B_34),k6_relat_1(A_33)) = k6_relat_1(k3_xboole_0(A_33,B_34)) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_974,plain,(
    ! [B_120,A_121] :
      ( k9_relat_1(B_120,k2_relat_1(A_121)) = k2_relat_1(k5_relat_1(A_121,B_120))
      | ~ v1_relat_1(B_120)
      | ~ v1_relat_1(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1002,plain,(
    ! [A_26,B_120] :
      ( k2_relat_1(k5_relat_1(k6_relat_1(A_26),B_120)) = k9_relat_1(B_120,A_26)
      | ~ v1_relat_1(B_120)
      | ~ v1_relat_1(k6_relat_1(A_26)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_974])).

tff(c_1015,plain,(
    ! [A_122,B_123] :
      ( k2_relat_1(k5_relat_1(k6_relat_1(A_122),B_123)) = k9_relat_1(B_123,A_122)
      | ~ v1_relat_1(B_123) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1002])).

tff(c_1036,plain,(
    ! [A_33,B_34] :
      ( k2_relat_1(k6_relat_1(k3_xboole_0(A_33,B_34))) = k9_relat_1(k6_relat_1(A_33),B_34)
      | ~ v1_relat_1(k6_relat_1(A_33)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_1015])).

tff(c_1040,plain,(
    ! [A_33,B_34] : k9_relat_1(k6_relat_1(A_33),B_34) = k3_xboole_0(A_33,B_34) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_28,c_1036])).

tff(c_26,plain,(
    ! [A_26] : k1_relat_1(k6_relat_1(A_26)) = A_26 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_214,plain,(
    ! [B_77,A_78] :
      ( k7_relat_1(B_77,A_78) = B_77
      | ~ r1_tarski(k1_relat_1(B_77),A_78)
      | ~ v1_relat_1(B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_224,plain,(
    ! [A_26,A_78] :
      ( k7_relat_1(k6_relat_1(A_26),A_78) = k6_relat_1(A_26)
      | ~ r1_tarski(A_26,A_78)
      | ~ v1_relat_1(k6_relat_1(A_26)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_214])).

tff(c_234,plain,(
    ! [A_79,A_80] :
      ( k7_relat_1(k6_relat_1(A_79),A_80) = k6_relat_1(A_79)
      | ~ r1_tarski(A_79,A_80) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_224])).

tff(c_22,plain,(
    ! [B_22,A_21] :
      ( k2_relat_1(k7_relat_1(B_22,A_21)) = k9_relat_1(B_22,A_21)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_240,plain,(
    ! [A_79,A_80] :
      ( k9_relat_1(k6_relat_1(A_79),A_80) = k2_relat_1(k6_relat_1(A_79))
      | ~ v1_relat_1(k6_relat_1(A_79))
      | ~ r1_tarski(A_79,A_80) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_234,c_22])).

tff(c_264,plain,(
    ! [A_79,A_80] :
      ( k9_relat_1(k6_relat_1(A_79),A_80) = A_79
      | ~ r1_tarski(A_79,A_80) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_28,c_240])).

tff(c_1166,plain,(
    ! [A_130,A_131] :
      ( k3_xboole_0(A_130,A_131) = A_130
      | ~ r1_tarski(A_130,A_131) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1040,c_264])).

tff(c_1195,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_52,c_1166])).

tff(c_54,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_1041,plain,(
    ! [C_124,A_125,B_126] :
      ( k2_wellord1(k2_wellord1(C_124,A_125),B_126) = k2_wellord1(C_124,k3_xboole_0(A_125,B_126))
      | ~ v1_relat_1(C_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_726,plain,(
    ! [C_111,B_112,A_113] :
      ( k2_wellord1(k2_wellord1(C_111,B_112),A_113) = k2_wellord1(k2_wellord1(C_111,A_113),B_112)
      | ~ v1_relat_1(C_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_50,plain,(
    k2_wellord1(k2_wellord1('#skF_3','#skF_2'),'#skF_1') != k2_wellord1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_753,plain,
    ( k2_wellord1(k2_wellord1('#skF_3','#skF_1'),'#skF_2') != k2_wellord1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_726,c_50])).

tff(c_798,plain,(
    k2_wellord1(k2_wellord1('#skF_3','#skF_1'),'#skF_2') != k2_wellord1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_753])).

tff(c_1054,plain,
    ( k2_wellord1('#skF_3',k3_xboole_0('#skF_1','#skF_2')) != k2_wellord1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1041,c_798])).

tff(c_1104,plain,(
    k2_wellord1('#skF_3',k3_xboole_0('#skF_1','#skF_2')) != k2_wellord1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1054])).

tff(c_1254,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1195,c_1104])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:58:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.32/1.56  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.32/1.57  
% 3.32/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.32/1.57  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_wellord1 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.32/1.57  
% 3.32/1.57  %Foreground sorts:
% 3.32/1.57  
% 3.32/1.57  
% 3.32/1.57  %Background operators:
% 3.32/1.57  
% 3.32/1.57  
% 3.32/1.57  %Foreground operators:
% 3.32/1.57  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 3.32/1.57  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.32/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.32/1.57  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.32/1.57  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.32/1.57  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.32/1.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.32/1.57  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.32/1.57  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.32/1.57  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.32/1.57  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.32/1.57  tff('#skF_2', type, '#skF_2': $i).
% 3.32/1.57  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.32/1.57  tff('#skF_3', type, '#skF_3': $i).
% 3.32/1.57  tff('#skF_1', type, '#skF_1': $i).
% 3.32/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.32/1.57  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.32/1.57  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.32/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.32/1.57  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.32/1.57  tff(k2_wellord1, type, k2_wellord1: ($i * $i) > $i).
% 3.32/1.57  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.32/1.57  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.32/1.57  
% 3.32/1.58  tff(f_113, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k2_wellord1(k2_wellord1(C, B), A) = k2_wellord1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_wellord1)).
% 3.32/1.58  tff(f_88, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 3.32/1.58  tff(f_70, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 3.32/1.58  tff(f_90, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 3.32/1.58  tff(f_66, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t160_relat_1)).
% 3.32/1.58  tff(f_80, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 3.32/1.58  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 3.32/1.58  tff(f_102, axiom, (![A, B, C]: (v1_relat_1(C) => (k2_wellord1(k2_wellord1(C, A), B) = k2_wellord1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_wellord1)).
% 3.32/1.58  tff(f_106, axiom, (![A, B, C]: (v1_relat_1(C) => (k2_wellord1(k2_wellord1(C, A), B) = k2_wellord1(k2_wellord1(C, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_wellord1)).
% 3.32/1.58  tff(c_52, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.32/1.58  tff(c_36, plain, (![A_32]: (v1_relat_1(k6_relat_1(A_32)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.32/1.58  tff(c_28, plain, (![A_26]: (k2_relat_1(k6_relat_1(A_26))=A_26)), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.32/1.58  tff(c_40, plain, (![B_34, A_33]: (k5_relat_1(k6_relat_1(B_34), k6_relat_1(A_33))=k6_relat_1(k3_xboole_0(A_33, B_34)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.32/1.58  tff(c_974, plain, (![B_120, A_121]: (k9_relat_1(B_120, k2_relat_1(A_121))=k2_relat_1(k5_relat_1(A_121, B_120)) | ~v1_relat_1(B_120) | ~v1_relat_1(A_121))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.32/1.58  tff(c_1002, plain, (![A_26, B_120]: (k2_relat_1(k5_relat_1(k6_relat_1(A_26), B_120))=k9_relat_1(B_120, A_26) | ~v1_relat_1(B_120) | ~v1_relat_1(k6_relat_1(A_26)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_974])).
% 3.32/1.58  tff(c_1015, plain, (![A_122, B_123]: (k2_relat_1(k5_relat_1(k6_relat_1(A_122), B_123))=k9_relat_1(B_123, A_122) | ~v1_relat_1(B_123))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1002])).
% 3.32/1.58  tff(c_1036, plain, (![A_33, B_34]: (k2_relat_1(k6_relat_1(k3_xboole_0(A_33, B_34)))=k9_relat_1(k6_relat_1(A_33), B_34) | ~v1_relat_1(k6_relat_1(A_33)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_1015])).
% 3.32/1.58  tff(c_1040, plain, (![A_33, B_34]: (k9_relat_1(k6_relat_1(A_33), B_34)=k3_xboole_0(A_33, B_34))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_28, c_1036])).
% 3.32/1.58  tff(c_26, plain, (![A_26]: (k1_relat_1(k6_relat_1(A_26))=A_26)), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.32/1.58  tff(c_214, plain, (![B_77, A_78]: (k7_relat_1(B_77, A_78)=B_77 | ~r1_tarski(k1_relat_1(B_77), A_78) | ~v1_relat_1(B_77))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.32/1.58  tff(c_224, plain, (![A_26, A_78]: (k7_relat_1(k6_relat_1(A_26), A_78)=k6_relat_1(A_26) | ~r1_tarski(A_26, A_78) | ~v1_relat_1(k6_relat_1(A_26)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_214])).
% 3.32/1.58  tff(c_234, plain, (![A_79, A_80]: (k7_relat_1(k6_relat_1(A_79), A_80)=k6_relat_1(A_79) | ~r1_tarski(A_79, A_80))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_224])).
% 3.32/1.58  tff(c_22, plain, (![B_22, A_21]: (k2_relat_1(k7_relat_1(B_22, A_21))=k9_relat_1(B_22, A_21) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.32/1.58  tff(c_240, plain, (![A_79, A_80]: (k9_relat_1(k6_relat_1(A_79), A_80)=k2_relat_1(k6_relat_1(A_79)) | ~v1_relat_1(k6_relat_1(A_79)) | ~r1_tarski(A_79, A_80))), inference(superposition, [status(thm), theory('equality')], [c_234, c_22])).
% 3.32/1.58  tff(c_264, plain, (![A_79, A_80]: (k9_relat_1(k6_relat_1(A_79), A_80)=A_79 | ~r1_tarski(A_79, A_80))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_28, c_240])).
% 3.32/1.58  tff(c_1166, plain, (![A_130, A_131]: (k3_xboole_0(A_130, A_131)=A_130 | ~r1_tarski(A_130, A_131))), inference(demodulation, [status(thm), theory('equality')], [c_1040, c_264])).
% 3.32/1.58  tff(c_1195, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_52, c_1166])).
% 3.32/1.58  tff(c_54, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.32/1.58  tff(c_1041, plain, (![C_124, A_125, B_126]: (k2_wellord1(k2_wellord1(C_124, A_125), B_126)=k2_wellord1(C_124, k3_xboole_0(A_125, B_126)) | ~v1_relat_1(C_124))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.32/1.58  tff(c_726, plain, (![C_111, B_112, A_113]: (k2_wellord1(k2_wellord1(C_111, B_112), A_113)=k2_wellord1(k2_wellord1(C_111, A_113), B_112) | ~v1_relat_1(C_111))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.32/1.58  tff(c_50, plain, (k2_wellord1(k2_wellord1('#skF_3', '#skF_2'), '#skF_1')!=k2_wellord1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.32/1.58  tff(c_753, plain, (k2_wellord1(k2_wellord1('#skF_3', '#skF_1'), '#skF_2')!=k2_wellord1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_726, c_50])).
% 3.32/1.58  tff(c_798, plain, (k2_wellord1(k2_wellord1('#skF_3', '#skF_1'), '#skF_2')!=k2_wellord1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_753])).
% 3.32/1.58  tff(c_1054, plain, (k2_wellord1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))!=k2_wellord1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1041, c_798])).
% 3.32/1.58  tff(c_1104, plain, (k2_wellord1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))!=k2_wellord1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1054])).
% 3.32/1.58  tff(c_1254, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1195, c_1104])).
% 3.32/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.32/1.58  
% 3.32/1.58  Inference rules
% 3.32/1.58  ----------------------
% 3.32/1.58  #Ref     : 0
% 3.32/1.58  #Sup     : 271
% 3.32/1.58  #Fact    : 0
% 3.32/1.58  #Define  : 0
% 3.32/1.58  #Split   : 1
% 3.32/1.58  #Chain   : 0
% 3.32/1.58  #Close   : 0
% 3.32/1.58  
% 3.32/1.58  Ordering : KBO
% 3.32/1.58  
% 3.32/1.58  Simplification rules
% 3.32/1.58  ----------------------
% 3.32/1.58  #Subsume      : 33
% 3.32/1.58  #Demod        : 158
% 3.32/1.58  #Tautology    : 123
% 3.32/1.58  #SimpNegUnit  : 0
% 3.32/1.58  #BackRed      : 2
% 3.32/1.58  
% 3.32/1.58  #Partial instantiations: 0
% 3.32/1.58  #Strategies tried      : 1
% 3.32/1.58  
% 3.32/1.58  Timing (in seconds)
% 3.32/1.58  ----------------------
% 3.32/1.58  Preprocessing        : 0.36
% 3.32/1.58  Parsing              : 0.20
% 3.32/1.58  CNF conversion       : 0.02
% 3.32/1.58  Main loop            : 0.40
% 3.32/1.58  Inferencing          : 0.16
% 3.32/1.58  Reduction            : 0.12
% 3.32/1.58  Demodulation         : 0.09
% 3.32/1.58  BG Simplification    : 0.03
% 3.32/1.58  Subsumption          : 0.08
% 3.32/1.58  Abstraction          : 0.03
% 3.32/1.58  MUC search           : 0.00
% 3.32/1.58  Cooper               : 0.00
% 3.32/1.58  Total                : 0.78
% 3.32/1.58  Index Insertion      : 0.00
% 3.32/1.58  Index Deletion       : 0.00
% 3.32/1.58  Index Matching       : 0.00
% 3.32/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
