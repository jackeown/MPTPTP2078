%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:29 EST 2020

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :   58 (  70 expanded)
%              Number of leaves         :   34 (  41 expanded)
%              Depth                    :    9
%              Number of atoms          :   59 (  79 expanded)
%              Number of equality atoms :   31 (  35 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_79,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => k9_relat_1(k8_relat_1(A,C),B) = k3_xboole_0(A,k9_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t126_funct_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_41,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_72,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_64,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k8_relat_1(A,B)) = k3_xboole_0(k2_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k9_relat_1(k5_relat_1(B,C),A) = k9_relat_1(C,k9_relat_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t159_relat_1)).

tff(c_40,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_tarski(B_2,A_1) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_94,plain,(
    ! [A_52,B_53] : k1_setfam_1(k2_tarski(A_52,B_53)) = k3_xboole_0(A_52,B_53) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_118,plain,(
    ! [B_56,A_57] : k1_setfam_1(k2_tarski(B_56,A_57)) = k3_xboole_0(A_57,B_56) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_94])).

tff(c_16,plain,(
    ! [A_30,B_31] : k1_setfam_1(k2_tarski(A_30,B_31)) = k3_xboole_0(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_124,plain,(
    ! [B_56,A_57] : k3_xboole_0(B_56,A_57) = k3_xboole_0(A_57,B_56) ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_16])).

tff(c_32,plain,(
    ! [A_45] : v1_relat_1(k6_relat_1(A_45)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_193,plain,(
    ! [A_65,B_66] :
      ( k5_relat_1(k6_relat_1(A_65),B_66) = k7_relat_1(B_66,A_65)
      | ~ v1_relat_1(B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_20,plain,(
    ! [B_35,A_34] :
      ( k5_relat_1(B_35,k6_relat_1(A_34)) = k8_relat_1(A_34,B_35)
      | ~ v1_relat_1(B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_200,plain,(
    ! [A_34,A_65] :
      ( k8_relat_1(A_34,k6_relat_1(A_65)) = k7_relat_1(k6_relat_1(A_34),A_65)
      | ~ v1_relat_1(k6_relat_1(A_65))
      | ~ v1_relat_1(k6_relat_1(A_34)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_193,c_20])).

tff(c_210,plain,(
    ! [A_34,A_65] : k8_relat_1(A_34,k6_relat_1(A_65)) = k7_relat_1(k6_relat_1(A_34),A_65) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_32,c_200])).

tff(c_28,plain,(
    ! [A_42] : k2_relat_1(k6_relat_1(A_42)) = A_42 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_233,plain,(
    ! [B_71,A_72] :
      ( k3_xboole_0(k2_relat_1(B_71),A_72) = k2_relat_1(k8_relat_1(A_72,B_71))
      | ~ v1_relat_1(B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_259,plain,(
    ! [A_72,A_42] :
      ( k2_relat_1(k8_relat_1(A_72,k6_relat_1(A_42))) = k3_xboole_0(A_42,A_72)
      | ~ v1_relat_1(k6_relat_1(A_42)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_233])).

tff(c_264,plain,(
    ! [A_73,A_74] : k2_relat_1(k7_relat_1(k6_relat_1(A_73),A_74)) = k3_xboole_0(A_74,A_73) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_210,c_259])).

tff(c_22,plain,(
    ! [B_37,A_36] :
      ( k2_relat_1(k7_relat_1(B_37,A_36)) = k9_relat_1(B_37,A_36)
      | ~ v1_relat_1(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_273,plain,(
    ! [A_73,A_74] :
      ( k9_relat_1(k6_relat_1(A_73),A_74) = k3_xboole_0(A_74,A_73)
      | ~ v1_relat_1(k6_relat_1(A_73)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_264,c_22])).

tff(c_283,plain,(
    ! [A_73,A_74] : k9_relat_1(k6_relat_1(A_73),A_74) = k3_xboole_0(A_74,A_73) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_273])).

tff(c_357,plain,(
    ! [B_88,C_89,A_90] :
      ( k9_relat_1(k5_relat_1(B_88,C_89),A_90) = k9_relat_1(C_89,k9_relat_1(B_88,A_90))
      | ~ v1_relat_1(C_89)
      | ~ v1_relat_1(B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_369,plain,(
    ! [A_34,B_35,A_90] :
      ( k9_relat_1(k6_relat_1(A_34),k9_relat_1(B_35,A_90)) = k9_relat_1(k8_relat_1(A_34,B_35),A_90)
      | ~ v1_relat_1(k6_relat_1(A_34))
      | ~ v1_relat_1(B_35)
      | ~ v1_relat_1(B_35) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_357])).

tff(c_385,plain,(
    ! [A_94,B_95,A_96] :
      ( k9_relat_1(k8_relat_1(A_94,B_95),A_96) = k3_xboole_0(k9_relat_1(B_95,A_96),A_94)
      | ~ v1_relat_1(B_95) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_283,c_369])).

tff(c_36,plain,(
    k9_relat_1(k8_relat_1('#skF_1','#skF_3'),'#skF_2') != k3_xboole_0('#skF_1',k9_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_391,plain,
    ( k3_xboole_0(k9_relat_1('#skF_3','#skF_2'),'#skF_1') != k3_xboole_0('#skF_1',k9_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_385,c_36])).

tff(c_401,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_124,c_391])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n001.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 21:09:15 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.18/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.30  
% 2.18/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.31  %$ v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.18/1.31  
% 2.18/1.31  %Foreground sorts:
% 2.18/1.31  
% 2.18/1.31  
% 2.18/1.31  %Background operators:
% 2.18/1.31  
% 2.18/1.31  
% 2.18/1.31  %Foreground operators:
% 2.18/1.31  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.18/1.31  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.18/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.18/1.31  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.18/1.31  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.18/1.31  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.18/1.31  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.18/1.31  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.18/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.18/1.31  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.18/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.18/1.31  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.18/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.18/1.31  tff('#skF_1', type, '#skF_1': $i).
% 2.18/1.31  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.18/1.31  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.18/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.18/1.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.18/1.31  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.18/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.18/1.31  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.18/1.31  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.18/1.31  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.18/1.31  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.18/1.31  
% 2.18/1.32  tff(f_79, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (k9_relat_1(k8_relat_1(A, C), B) = k3_xboole_0(A, k9_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t126_funct_1)).
% 2.18/1.32  tff(f_27, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.18/1.32  tff(f_41, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.18/1.32  tff(f_72, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.18/1.32  tff(f_68, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 2.18/1.32  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_relat_1)).
% 2.18/1.32  tff(f_64, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.18/1.32  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k8_relat_1(A, B)) = k3_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t119_relat_1)).
% 2.18/1.32  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 2.18/1.32  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k9_relat_1(k5_relat_1(B, C), A) = k9_relat_1(C, k9_relat_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t159_relat_1)).
% 2.18/1.32  tff(c_40, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.18/1.32  tff(c_2, plain, (![B_2, A_1]: (k2_tarski(B_2, A_1)=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.18/1.32  tff(c_94, plain, (![A_52, B_53]: (k1_setfam_1(k2_tarski(A_52, B_53))=k3_xboole_0(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.18/1.32  tff(c_118, plain, (![B_56, A_57]: (k1_setfam_1(k2_tarski(B_56, A_57))=k3_xboole_0(A_57, B_56))), inference(superposition, [status(thm), theory('equality')], [c_2, c_94])).
% 2.18/1.32  tff(c_16, plain, (![A_30, B_31]: (k1_setfam_1(k2_tarski(A_30, B_31))=k3_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.18/1.32  tff(c_124, plain, (![B_56, A_57]: (k3_xboole_0(B_56, A_57)=k3_xboole_0(A_57, B_56))), inference(superposition, [status(thm), theory('equality')], [c_118, c_16])).
% 2.18/1.32  tff(c_32, plain, (![A_45]: (v1_relat_1(k6_relat_1(A_45)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.18/1.32  tff(c_193, plain, (![A_65, B_66]: (k5_relat_1(k6_relat_1(A_65), B_66)=k7_relat_1(B_66, A_65) | ~v1_relat_1(B_66))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.18/1.32  tff(c_20, plain, (![B_35, A_34]: (k5_relat_1(B_35, k6_relat_1(A_34))=k8_relat_1(A_34, B_35) | ~v1_relat_1(B_35))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.18/1.32  tff(c_200, plain, (![A_34, A_65]: (k8_relat_1(A_34, k6_relat_1(A_65))=k7_relat_1(k6_relat_1(A_34), A_65) | ~v1_relat_1(k6_relat_1(A_65)) | ~v1_relat_1(k6_relat_1(A_34)))), inference(superposition, [status(thm), theory('equality')], [c_193, c_20])).
% 2.18/1.32  tff(c_210, plain, (![A_34, A_65]: (k8_relat_1(A_34, k6_relat_1(A_65))=k7_relat_1(k6_relat_1(A_34), A_65))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_32, c_200])).
% 2.18/1.32  tff(c_28, plain, (![A_42]: (k2_relat_1(k6_relat_1(A_42))=A_42)), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.18/1.32  tff(c_233, plain, (![B_71, A_72]: (k3_xboole_0(k2_relat_1(B_71), A_72)=k2_relat_1(k8_relat_1(A_72, B_71)) | ~v1_relat_1(B_71))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.18/1.32  tff(c_259, plain, (![A_72, A_42]: (k2_relat_1(k8_relat_1(A_72, k6_relat_1(A_42)))=k3_xboole_0(A_42, A_72) | ~v1_relat_1(k6_relat_1(A_42)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_233])).
% 2.18/1.32  tff(c_264, plain, (![A_73, A_74]: (k2_relat_1(k7_relat_1(k6_relat_1(A_73), A_74))=k3_xboole_0(A_74, A_73))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_210, c_259])).
% 2.18/1.32  tff(c_22, plain, (![B_37, A_36]: (k2_relat_1(k7_relat_1(B_37, A_36))=k9_relat_1(B_37, A_36) | ~v1_relat_1(B_37))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.18/1.32  tff(c_273, plain, (![A_73, A_74]: (k9_relat_1(k6_relat_1(A_73), A_74)=k3_xboole_0(A_74, A_73) | ~v1_relat_1(k6_relat_1(A_73)))), inference(superposition, [status(thm), theory('equality')], [c_264, c_22])).
% 2.18/1.32  tff(c_283, plain, (![A_73, A_74]: (k9_relat_1(k6_relat_1(A_73), A_74)=k3_xboole_0(A_74, A_73))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_273])).
% 2.18/1.32  tff(c_357, plain, (![B_88, C_89, A_90]: (k9_relat_1(k5_relat_1(B_88, C_89), A_90)=k9_relat_1(C_89, k9_relat_1(B_88, A_90)) | ~v1_relat_1(C_89) | ~v1_relat_1(B_88))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.18/1.32  tff(c_369, plain, (![A_34, B_35, A_90]: (k9_relat_1(k6_relat_1(A_34), k9_relat_1(B_35, A_90))=k9_relat_1(k8_relat_1(A_34, B_35), A_90) | ~v1_relat_1(k6_relat_1(A_34)) | ~v1_relat_1(B_35) | ~v1_relat_1(B_35))), inference(superposition, [status(thm), theory('equality')], [c_20, c_357])).
% 2.18/1.32  tff(c_385, plain, (![A_94, B_95, A_96]: (k9_relat_1(k8_relat_1(A_94, B_95), A_96)=k3_xboole_0(k9_relat_1(B_95, A_96), A_94) | ~v1_relat_1(B_95))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_283, c_369])).
% 2.18/1.32  tff(c_36, plain, (k9_relat_1(k8_relat_1('#skF_1', '#skF_3'), '#skF_2')!=k3_xboole_0('#skF_1', k9_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.18/1.32  tff(c_391, plain, (k3_xboole_0(k9_relat_1('#skF_3', '#skF_2'), '#skF_1')!=k3_xboole_0('#skF_1', k9_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_385, c_36])).
% 2.18/1.32  tff(c_401, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_124, c_391])).
% 2.18/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.32  
% 2.18/1.32  Inference rules
% 2.18/1.32  ----------------------
% 2.18/1.32  #Ref     : 0
% 2.18/1.32  #Sup     : 84
% 2.18/1.32  #Fact    : 0
% 2.18/1.32  #Define  : 0
% 2.18/1.32  #Split   : 0
% 2.18/1.32  #Chain   : 0
% 2.18/1.32  #Close   : 0
% 2.18/1.32  
% 2.18/1.32  Ordering : KBO
% 2.18/1.32  
% 2.18/1.32  Simplification rules
% 2.18/1.32  ----------------------
% 2.18/1.32  #Subsume      : 9
% 2.18/1.32  #Demod        : 22
% 2.18/1.32  #Tautology    : 58
% 2.18/1.32  #SimpNegUnit  : 0
% 2.18/1.32  #BackRed      : 0
% 2.18/1.32  
% 2.18/1.32  #Partial instantiations: 0
% 2.18/1.32  #Strategies tried      : 1
% 2.18/1.32  
% 2.18/1.32  Timing (in seconds)
% 2.18/1.32  ----------------------
% 2.18/1.32  Preprocessing        : 0.31
% 2.18/1.32  Parsing              : 0.16
% 2.18/1.32  CNF conversion       : 0.02
% 2.18/1.32  Main loop            : 0.20
% 2.18/1.32  Inferencing          : 0.08
% 2.18/1.32  Reduction            : 0.07
% 2.18/1.32  Demodulation         : 0.06
% 2.18/1.32  BG Simplification    : 0.02
% 2.18/1.32  Subsumption          : 0.03
% 2.18/1.32  Abstraction          : 0.01
% 2.18/1.32  MUC search           : 0.00
% 2.18/1.32  Cooper               : 0.00
% 2.18/1.32  Total                : 0.54
% 2.18/1.32  Index Insertion      : 0.00
% 2.18/1.32  Index Deletion       : 0.00
% 2.18/1.32  Index Matching       : 0.00
% 2.18/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
