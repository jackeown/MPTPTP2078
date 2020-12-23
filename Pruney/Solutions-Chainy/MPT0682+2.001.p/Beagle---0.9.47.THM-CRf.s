%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:28 EST 2020

% Result     : Theorem 2.31s
% Output     : CNFRefutation 2.55s
% Verified   : 
% Statistics : Number of formulae       :   60 (  71 expanded)
%              Number of leaves         :   35 (  42 expanded)
%              Depth                    :    9
%              Number of atoms          :   60 (  74 expanded)
%              Number of equality atoms :   32 (  35 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(f_29,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_43,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_45,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_68,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k8_relat_1(A,B)) = k3_xboole_0(k2_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k9_relat_1(k5_relat_1(B,C),A) = k9_relat_1(C,k9_relat_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t159_relat_1)).

tff(c_40,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_4,plain,(
    ! [B_4,A_3] : k2_tarski(B_4,A_3) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_93,plain,(
    ! [A_53,B_54] : k1_setfam_1(k2_tarski(A_53,B_54)) = k3_xboole_0(A_53,B_54) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_117,plain,(
    ! [B_57,A_58] : k1_setfam_1(k2_tarski(B_57,A_58)) = k3_xboole_0(A_58,B_57) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_93])).

tff(c_18,plain,(
    ! [A_32,B_33] : k1_setfam_1(k2_tarski(A_32,B_33)) = k3_xboole_0(A_32,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_123,plain,(
    ! [B_57,A_58] : k3_xboole_0(B_57,A_58) = k3_xboole_0(A_58,B_57) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_18])).

tff(c_20,plain,(
    ! [A_34] : v1_relat_1(k6_relat_1(A_34)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_207,plain,(
    ! [B_68,A_69] :
      ( k5_relat_1(B_68,k6_relat_1(A_69)) = k8_relat_1(A_69,B_68)
      | ~ v1_relat_1(B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_34,plain,(
    ! [A_46,B_47] :
      ( k5_relat_1(k6_relat_1(A_46),B_47) = k7_relat_1(B_47,A_46)
      | ~ v1_relat_1(B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_214,plain,(
    ! [A_69,A_46] :
      ( k8_relat_1(A_69,k6_relat_1(A_46)) = k7_relat_1(k6_relat_1(A_69),A_46)
      | ~ v1_relat_1(k6_relat_1(A_69))
      | ~ v1_relat_1(k6_relat_1(A_46)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_207,c_34])).

tff(c_224,plain,(
    ! [A_69,A_46] : k8_relat_1(A_69,k6_relat_1(A_46)) = k7_relat_1(k6_relat_1(A_69),A_46) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_20,c_214])).

tff(c_32,plain,(
    ! [A_45] : k2_relat_1(k6_relat_1(A_45)) = A_45 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_247,plain,(
    ! [B_74,A_75] :
      ( k3_xboole_0(k2_relat_1(B_74),A_75) = k2_relat_1(k8_relat_1(A_75,B_74))
      | ~ v1_relat_1(B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_273,plain,(
    ! [A_75,A_45] :
      ( k2_relat_1(k8_relat_1(A_75,k6_relat_1(A_45))) = k3_xboole_0(A_45,A_75)
      | ~ v1_relat_1(k6_relat_1(A_45)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_247])).

tff(c_278,plain,(
    ! [A_76,A_77] : k2_relat_1(k7_relat_1(k6_relat_1(A_76),A_77)) = k3_xboole_0(A_77,A_76) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_224,c_273])).

tff(c_26,plain,(
    ! [B_40,A_39] :
      ( k2_relat_1(k7_relat_1(B_40,A_39)) = k9_relat_1(B_40,A_39)
      | ~ v1_relat_1(B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_287,plain,(
    ! [A_76,A_77] :
      ( k9_relat_1(k6_relat_1(A_76),A_77) = k3_xboole_0(A_77,A_76)
      | ~ v1_relat_1(k6_relat_1(A_76)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_278,c_26])).

tff(c_297,plain,(
    ! [A_76,A_77] : k9_relat_1(k6_relat_1(A_76),A_77) = k3_xboole_0(A_77,A_76) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_287])).

tff(c_24,plain,(
    ! [B_38,A_37] :
      ( k5_relat_1(B_38,k6_relat_1(A_37)) = k8_relat_1(A_37,B_38)
      | ~ v1_relat_1(B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_473,plain,(
    ! [B_97,C_98,A_99] :
      ( k9_relat_1(k5_relat_1(B_97,C_98),A_99) = k9_relat_1(C_98,k9_relat_1(B_97,A_99))
      | ~ v1_relat_1(C_98)
      | ~ v1_relat_1(B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_482,plain,(
    ! [A_37,B_38,A_99] :
      ( k9_relat_1(k6_relat_1(A_37),k9_relat_1(B_38,A_99)) = k9_relat_1(k8_relat_1(A_37,B_38),A_99)
      | ~ v1_relat_1(k6_relat_1(A_37))
      | ~ v1_relat_1(B_38)
      | ~ v1_relat_1(B_38) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_473])).

tff(c_492,plain,(
    ! [A_100,B_101,A_102] :
      ( k9_relat_1(k8_relat_1(A_100,B_101),A_102) = k3_xboole_0(k9_relat_1(B_101,A_102),A_100)
      | ~ v1_relat_1(B_101) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_297,c_482])).

tff(c_36,plain,(
    k9_relat_1(k8_relat_1('#skF_1','#skF_3'),'#skF_2') != k3_xboole_0('#skF_1',k9_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_498,plain,
    ( k3_xboole_0(k9_relat_1('#skF_3','#skF_2'),'#skF_1') != k3_xboole_0('#skF_1',k9_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_492,c_36])).

tff(c_508,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_123,c_498])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.33  % Computer   : n017.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 11:18:31 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.31/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.31/1.30  
% 2.31/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.31/1.31  %$ v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.31/1.31  
% 2.31/1.31  %Foreground sorts:
% 2.31/1.31  
% 2.31/1.31  
% 2.31/1.31  %Background operators:
% 2.31/1.31  
% 2.31/1.31  
% 2.31/1.31  %Foreground operators:
% 2.31/1.31  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.31/1.31  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.31/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.31/1.31  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.31/1.31  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.31/1.31  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.31/1.31  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.31/1.31  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.31/1.31  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.31/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.31/1.31  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.31/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.31/1.31  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.31/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.31/1.31  tff('#skF_1', type, '#skF_1': $i).
% 2.31/1.31  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.31/1.31  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.31/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.31/1.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.31/1.31  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.31/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.31/1.31  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.31/1.31  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.31/1.31  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.31/1.31  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.31/1.31  
% 2.55/1.32  tff(f_79, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (k9_relat_1(k8_relat_1(A, C), B) = k3_xboole_0(A, k9_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t126_funct_1)).
% 2.55/1.32  tff(f_29, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.55/1.32  tff(f_43, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.55/1.32  tff(f_45, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.55/1.32  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_relat_1)).
% 2.55/1.32  tff(f_72, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 2.55/1.32  tff(f_68, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.55/1.32  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k8_relat_1(A, B)) = k3_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t119_relat_1)).
% 2.55/1.32  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 2.55/1.32  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k9_relat_1(k5_relat_1(B, C), A) = k9_relat_1(C, k9_relat_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t159_relat_1)).
% 2.55/1.32  tff(c_40, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.55/1.32  tff(c_4, plain, (![B_4, A_3]: (k2_tarski(B_4, A_3)=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.55/1.32  tff(c_93, plain, (![A_53, B_54]: (k1_setfam_1(k2_tarski(A_53, B_54))=k3_xboole_0(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.55/1.32  tff(c_117, plain, (![B_57, A_58]: (k1_setfam_1(k2_tarski(B_57, A_58))=k3_xboole_0(A_58, B_57))), inference(superposition, [status(thm), theory('equality')], [c_4, c_93])).
% 2.55/1.32  tff(c_18, plain, (![A_32, B_33]: (k1_setfam_1(k2_tarski(A_32, B_33))=k3_xboole_0(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.55/1.32  tff(c_123, plain, (![B_57, A_58]: (k3_xboole_0(B_57, A_58)=k3_xboole_0(A_58, B_57))), inference(superposition, [status(thm), theory('equality')], [c_117, c_18])).
% 2.55/1.32  tff(c_20, plain, (![A_34]: (v1_relat_1(k6_relat_1(A_34)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.55/1.32  tff(c_207, plain, (![B_68, A_69]: (k5_relat_1(B_68, k6_relat_1(A_69))=k8_relat_1(A_69, B_68) | ~v1_relat_1(B_68))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.55/1.32  tff(c_34, plain, (![A_46, B_47]: (k5_relat_1(k6_relat_1(A_46), B_47)=k7_relat_1(B_47, A_46) | ~v1_relat_1(B_47))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.55/1.32  tff(c_214, plain, (![A_69, A_46]: (k8_relat_1(A_69, k6_relat_1(A_46))=k7_relat_1(k6_relat_1(A_69), A_46) | ~v1_relat_1(k6_relat_1(A_69)) | ~v1_relat_1(k6_relat_1(A_46)))), inference(superposition, [status(thm), theory('equality')], [c_207, c_34])).
% 2.55/1.32  tff(c_224, plain, (![A_69, A_46]: (k8_relat_1(A_69, k6_relat_1(A_46))=k7_relat_1(k6_relat_1(A_69), A_46))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_20, c_214])).
% 2.55/1.32  tff(c_32, plain, (![A_45]: (k2_relat_1(k6_relat_1(A_45))=A_45)), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.55/1.32  tff(c_247, plain, (![B_74, A_75]: (k3_xboole_0(k2_relat_1(B_74), A_75)=k2_relat_1(k8_relat_1(A_75, B_74)) | ~v1_relat_1(B_74))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.55/1.32  tff(c_273, plain, (![A_75, A_45]: (k2_relat_1(k8_relat_1(A_75, k6_relat_1(A_45)))=k3_xboole_0(A_45, A_75) | ~v1_relat_1(k6_relat_1(A_45)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_247])).
% 2.55/1.32  tff(c_278, plain, (![A_76, A_77]: (k2_relat_1(k7_relat_1(k6_relat_1(A_76), A_77))=k3_xboole_0(A_77, A_76))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_224, c_273])).
% 2.55/1.32  tff(c_26, plain, (![B_40, A_39]: (k2_relat_1(k7_relat_1(B_40, A_39))=k9_relat_1(B_40, A_39) | ~v1_relat_1(B_40))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.55/1.32  tff(c_287, plain, (![A_76, A_77]: (k9_relat_1(k6_relat_1(A_76), A_77)=k3_xboole_0(A_77, A_76) | ~v1_relat_1(k6_relat_1(A_76)))), inference(superposition, [status(thm), theory('equality')], [c_278, c_26])).
% 2.55/1.32  tff(c_297, plain, (![A_76, A_77]: (k9_relat_1(k6_relat_1(A_76), A_77)=k3_xboole_0(A_77, A_76))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_287])).
% 2.55/1.32  tff(c_24, plain, (![B_38, A_37]: (k5_relat_1(B_38, k6_relat_1(A_37))=k8_relat_1(A_37, B_38) | ~v1_relat_1(B_38))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.55/1.32  tff(c_473, plain, (![B_97, C_98, A_99]: (k9_relat_1(k5_relat_1(B_97, C_98), A_99)=k9_relat_1(C_98, k9_relat_1(B_97, A_99)) | ~v1_relat_1(C_98) | ~v1_relat_1(B_97))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.55/1.32  tff(c_482, plain, (![A_37, B_38, A_99]: (k9_relat_1(k6_relat_1(A_37), k9_relat_1(B_38, A_99))=k9_relat_1(k8_relat_1(A_37, B_38), A_99) | ~v1_relat_1(k6_relat_1(A_37)) | ~v1_relat_1(B_38) | ~v1_relat_1(B_38))), inference(superposition, [status(thm), theory('equality')], [c_24, c_473])).
% 2.55/1.32  tff(c_492, plain, (![A_100, B_101, A_102]: (k9_relat_1(k8_relat_1(A_100, B_101), A_102)=k3_xboole_0(k9_relat_1(B_101, A_102), A_100) | ~v1_relat_1(B_101))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_297, c_482])).
% 2.55/1.32  tff(c_36, plain, (k9_relat_1(k8_relat_1('#skF_1', '#skF_3'), '#skF_2')!=k3_xboole_0('#skF_1', k9_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.55/1.32  tff(c_498, plain, (k3_xboole_0(k9_relat_1('#skF_3', '#skF_2'), '#skF_1')!=k3_xboole_0('#skF_1', k9_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_492, c_36])).
% 2.55/1.32  tff(c_508, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_123, c_498])).
% 2.55/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.55/1.32  
% 2.55/1.32  Inference rules
% 2.55/1.32  ----------------------
% 2.55/1.32  #Ref     : 0
% 2.55/1.32  #Sup     : 113
% 2.55/1.32  #Fact    : 0
% 2.55/1.32  #Define  : 0
% 2.55/1.32  #Split   : 0
% 2.55/1.32  #Chain   : 0
% 2.55/1.32  #Close   : 0
% 2.55/1.32  
% 2.55/1.32  Ordering : KBO
% 2.55/1.32  
% 2.55/1.32  Simplification rules
% 2.55/1.32  ----------------------
% 2.55/1.32  #Subsume      : 9
% 2.55/1.32  #Demod        : 28
% 2.55/1.32  #Tautology    : 72
% 2.55/1.32  #SimpNegUnit  : 0
% 2.55/1.32  #BackRed      : 0
% 2.55/1.32  
% 2.55/1.32  #Partial instantiations: 0
% 2.55/1.32  #Strategies tried      : 1
% 2.55/1.32  
% 2.55/1.32  Timing (in seconds)
% 2.55/1.32  ----------------------
% 2.55/1.32  Preprocessing        : 0.32
% 2.55/1.32  Parsing              : 0.17
% 2.55/1.32  CNF conversion       : 0.02
% 2.55/1.32  Main loop            : 0.23
% 2.55/1.32  Inferencing          : 0.09
% 2.55/1.32  Reduction            : 0.08
% 2.55/1.32  Demodulation         : 0.07
% 2.55/1.32  BG Simplification    : 0.02
% 2.55/1.32  Subsumption          : 0.03
% 2.55/1.32  Abstraction          : 0.01
% 2.55/1.32  MUC search           : 0.00
% 2.55/1.32  Cooper               : 0.00
% 2.55/1.32  Total                : 0.58
% 2.55/1.32  Index Insertion      : 0.00
% 2.55/1.32  Index Deletion       : 0.00
% 2.55/1.32  Index Matching       : 0.00
% 2.55/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
