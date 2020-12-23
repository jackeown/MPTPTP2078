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
% DateTime   : Thu Dec  3 10:04:29 EST 2020

% Result     : Theorem 2.28s
% Output     : CNFRefutation 2.28s
% Verified   : 
% Statistics : Number of formulae       :   56 (  70 expanded)
%              Number of leaves         :   33 (  41 expanded)
%              Depth                    :    8
%              Number of atoms          :   59 (  82 expanded)
%              Number of equality atoms :   29 (  36 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k8_relat_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(f_80,negated_conjecture,(
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

tff(f_73,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_69,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k8_relat_1(A,B)) = k3_xboole_0(k2_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k9_relat_1(k5_relat_1(B,C),A) = k9_relat_1(C,k9_relat_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t159_relat_1)).

tff(c_40,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_4,plain,(
    ! [B_4,A_3] : k2_tarski(B_4,A_3) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_94,plain,(
    ! [A_53,B_54] : k1_setfam_1(k2_tarski(A_53,B_54)) = k3_xboole_0(A_53,B_54) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_118,plain,(
    ! [B_57,A_58] : k1_setfam_1(k2_tarski(B_57,A_58)) = k3_xboole_0(A_58,B_57) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_94])).

tff(c_18,plain,(
    ! [A_32,B_33] : k1_setfam_1(k2_tarski(A_32,B_33)) = k3_xboole_0(A_32,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_124,plain,(
    ! [B_57,A_58] : k3_xboole_0(B_57,A_58) = k3_xboole_0(A_58,B_57) ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_18])).

tff(c_32,plain,(
    ! [A_46] : v1_relat_1(k6_relat_1(A_46)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_30,plain,(
    ! [A_45] : k2_relat_1(k6_relat_1(A_45)) = A_45 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_208,plain,(
    ! [B_68,A_69] :
      ( k3_xboole_0(k2_relat_1(B_68),A_69) = k2_relat_1(k8_relat_1(A_69,B_68))
      | ~ v1_relat_1(B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_231,plain,(
    ! [A_69,A_45] :
      ( k2_relat_1(k8_relat_1(A_69,k6_relat_1(A_45))) = k3_xboole_0(A_45,A_69)
      | ~ v1_relat_1(k6_relat_1(A_45)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_208])).

tff(c_235,plain,(
    ! [A_69,A_45] : k2_relat_1(k8_relat_1(A_69,k6_relat_1(A_45))) = k3_xboole_0(A_45,A_69) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_231])).

tff(c_22,plain,(
    ! [B_37,A_36] :
      ( k5_relat_1(B_37,k6_relat_1(A_36)) = k8_relat_1(A_36,B_37)
      | ~ v1_relat_1(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_321,plain,(
    ! [B_80,A_81] :
      ( k9_relat_1(B_80,k2_relat_1(A_81)) = k2_relat_1(k5_relat_1(A_81,B_80))
      | ~ v1_relat_1(B_80)
      | ~ v1_relat_1(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_333,plain,(
    ! [A_45,B_80] :
      ( k2_relat_1(k5_relat_1(k6_relat_1(A_45),B_80)) = k9_relat_1(B_80,A_45)
      | ~ v1_relat_1(B_80)
      | ~ v1_relat_1(k6_relat_1(A_45)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_321])).

tff(c_338,plain,(
    ! [A_82,B_83] :
      ( k2_relat_1(k5_relat_1(k6_relat_1(A_82),B_83)) = k9_relat_1(B_83,A_82)
      | ~ v1_relat_1(B_83) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_333])).

tff(c_357,plain,(
    ! [A_36,A_82] :
      ( k2_relat_1(k8_relat_1(A_36,k6_relat_1(A_82))) = k9_relat_1(k6_relat_1(A_36),A_82)
      | ~ v1_relat_1(k6_relat_1(A_36))
      | ~ v1_relat_1(k6_relat_1(A_82)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_338])).

tff(c_361,plain,(
    ! [A_36,A_82] : k9_relat_1(k6_relat_1(A_36),A_82) = k3_xboole_0(A_82,A_36) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_32,c_235,c_357])).

tff(c_502,plain,(
    ! [B_97,C_98,A_99] :
      ( k9_relat_1(k5_relat_1(B_97,C_98),A_99) = k9_relat_1(C_98,k9_relat_1(B_97,A_99))
      | ~ v1_relat_1(C_98)
      | ~ v1_relat_1(B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_519,plain,(
    ! [A_36,B_37,A_99] :
      ( k9_relat_1(k6_relat_1(A_36),k9_relat_1(B_37,A_99)) = k9_relat_1(k8_relat_1(A_36,B_37),A_99)
      | ~ v1_relat_1(k6_relat_1(A_36))
      | ~ v1_relat_1(B_37)
      | ~ v1_relat_1(B_37) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_502])).

tff(c_524,plain,(
    ! [A_100,B_101,A_102] :
      ( k9_relat_1(k8_relat_1(A_100,B_101),A_102) = k3_xboole_0(k9_relat_1(B_101,A_102),A_100)
      | ~ v1_relat_1(B_101) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_361,c_519])).

tff(c_36,plain,(
    k9_relat_1(k8_relat_1('#skF_1','#skF_3'),'#skF_2') != k3_xboole_0('#skF_1',k9_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_534,plain,
    ( k3_xboole_0(k9_relat_1('#skF_3','#skF_2'),'#skF_1') != k3_xboole_0('#skF_1',k9_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_524,c_36])).

tff(c_545,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_124,c_534])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:46:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.28/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.30  
% 2.28/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.30  %$ v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k8_relat_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.28/1.30  
% 2.28/1.30  %Foreground sorts:
% 2.28/1.30  
% 2.28/1.30  
% 2.28/1.30  %Background operators:
% 2.28/1.30  
% 2.28/1.30  
% 2.28/1.30  %Foreground operators:
% 2.28/1.30  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.28/1.30  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.28/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.28/1.30  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.28/1.30  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.28/1.30  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.28/1.30  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.28/1.30  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.28/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.28/1.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.28/1.30  tff('#skF_2', type, '#skF_2': $i).
% 2.28/1.30  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.28/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.28/1.30  tff('#skF_1', type, '#skF_1': $i).
% 2.28/1.30  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.28/1.30  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.28/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.28/1.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.28/1.30  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.28/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.28/1.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.28/1.30  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.28/1.30  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.28/1.30  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.28/1.30  
% 2.28/1.31  tff(f_80, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (k9_relat_1(k8_relat_1(A, C), B) = k3_xboole_0(A, k9_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t126_funct_1)).
% 2.28/1.31  tff(f_29, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.28/1.31  tff(f_43, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.28/1.31  tff(f_73, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.28/1.31  tff(f_69, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.28/1.31  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k8_relat_1(A, B)) = k3_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t119_relat_1)).
% 2.28/1.31  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_relat_1)).
% 2.28/1.31  tff(f_65, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t160_relat_1)).
% 2.28/1.31  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k9_relat_1(k5_relat_1(B, C), A) = k9_relat_1(C, k9_relat_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t159_relat_1)).
% 2.28/1.31  tff(c_40, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.28/1.31  tff(c_4, plain, (![B_4, A_3]: (k2_tarski(B_4, A_3)=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.28/1.31  tff(c_94, plain, (![A_53, B_54]: (k1_setfam_1(k2_tarski(A_53, B_54))=k3_xboole_0(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.28/1.31  tff(c_118, plain, (![B_57, A_58]: (k1_setfam_1(k2_tarski(B_57, A_58))=k3_xboole_0(A_58, B_57))), inference(superposition, [status(thm), theory('equality')], [c_4, c_94])).
% 2.28/1.31  tff(c_18, plain, (![A_32, B_33]: (k1_setfam_1(k2_tarski(A_32, B_33))=k3_xboole_0(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.28/1.31  tff(c_124, plain, (![B_57, A_58]: (k3_xboole_0(B_57, A_58)=k3_xboole_0(A_58, B_57))), inference(superposition, [status(thm), theory('equality')], [c_118, c_18])).
% 2.28/1.31  tff(c_32, plain, (![A_46]: (v1_relat_1(k6_relat_1(A_46)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.28/1.31  tff(c_30, plain, (![A_45]: (k2_relat_1(k6_relat_1(A_45))=A_45)), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.28/1.31  tff(c_208, plain, (![B_68, A_69]: (k3_xboole_0(k2_relat_1(B_68), A_69)=k2_relat_1(k8_relat_1(A_69, B_68)) | ~v1_relat_1(B_68))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.28/1.31  tff(c_231, plain, (![A_69, A_45]: (k2_relat_1(k8_relat_1(A_69, k6_relat_1(A_45)))=k3_xboole_0(A_45, A_69) | ~v1_relat_1(k6_relat_1(A_45)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_208])).
% 2.28/1.31  tff(c_235, plain, (![A_69, A_45]: (k2_relat_1(k8_relat_1(A_69, k6_relat_1(A_45)))=k3_xboole_0(A_45, A_69))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_231])).
% 2.28/1.31  tff(c_22, plain, (![B_37, A_36]: (k5_relat_1(B_37, k6_relat_1(A_36))=k8_relat_1(A_36, B_37) | ~v1_relat_1(B_37))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.28/1.31  tff(c_321, plain, (![B_80, A_81]: (k9_relat_1(B_80, k2_relat_1(A_81))=k2_relat_1(k5_relat_1(A_81, B_80)) | ~v1_relat_1(B_80) | ~v1_relat_1(A_81))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.28/1.31  tff(c_333, plain, (![A_45, B_80]: (k2_relat_1(k5_relat_1(k6_relat_1(A_45), B_80))=k9_relat_1(B_80, A_45) | ~v1_relat_1(B_80) | ~v1_relat_1(k6_relat_1(A_45)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_321])).
% 2.28/1.31  tff(c_338, plain, (![A_82, B_83]: (k2_relat_1(k5_relat_1(k6_relat_1(A_82), B_83))=k9_relat_1(B_83, A_82) | ~v1_relat_1(B_83))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_333])).
% 2.28/1.31  tff(c_357, plain, (![A_36, A_82]: (k2_relat_1(k8_relat_1(A_36, k6_relat_1(A_82)))=k9_relat_1(k6_relat_1(A_36), A_82) | ~v1_relat_1(k6_relat_1(A_36)) | ~v1_relat_1(k6_relat_1(A_82)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_338])).
% 2.28/1.31  tff(c_361, plain, (![A_36, A_82]: (k9_relat_1(k6_relat_1(A_36), A_82)=k3_xboole_0(A_82, A_36))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_32, c_235, c_357])).
% 2.28/1.31  tff(c_502, plain, (![B_97, C_98, A_99]: (k9_relat_1(k5_relat_1(B_97, C_98), A_99)=k9_relat_1(C_98, k9_relat_1(B_97, A_99)) | ~v1_relat_1(C_98) | ~v1_relat_1(B_97))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.28/1.31  tff(c_519, plain, (![A_36, B_37, A_99]: (k9_relat_1(k6_relat_1(A_36), k9_relat_1(B_37, A_99))=k9_relat_1(k8_relat_1(A_36, B_37), A_99) | ~v1_relat_1(k6_relat_1(A_36)) | ~v1_relat_1(B_37) | ~v1_relat_1(B_37))), inference(superposition, [status(thm), theory('equality')], [c_22, c_502])).
% 2.28/1.31  tff(c_524, plain, (![A_100, B_101, A_102]: (k9_relat_1(k8_relat_1(A_100, B_101), A_102)=k3_xboole_0(k9_relat_1(B_101, A_102), A_100) | ~v1_relat_1(B_101))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_361, c_519])).
% 2.28/1.31  tff(c_36, plain, (k9_relat_1(k8_relat_1('#skF_1', '#skF_3'), '#skF_2')!=k3_xboole_0('#skF_1', k9_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.28/1.31  tff(c_534, plain, (k3_xboole_0(k9_relat_1('#skF_3', '#skF_2'), '#skF_1')!=k3_xboole_0('#skF_1', k9_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_524, c_36])).
% 2.28/1.31  tff(c_545, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_124, c_534])).
% 2.28/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.31  
% 2.28/1.31  Inference rules
% 2.28/1.31  ----------------------
% 2.28/1.31  #Ref     : 0
% 2.28/1.31  #Sup     : 123
% 2.28/1.31  #Fact    : 0
% 2.28/1.31  #Define  : 0
% 2.28/1.31  #Split   : 0
% 2.28/1.31  #Chain   : 0
% 2.28/1.31  #Close   : 0
% 2.28/1.31  
% 2.28/1.31  Ordering : KBO
% 2.28/1.31  
% 2.28/1.31  Simplification rules
% 2.28/1.31  ----------------------
% 2.28/1.31  #Subsume      : 11
% 2.28/1.31  #Demod        : 30
% 2.28/1.31  #Tautology    : 72
% 2.28/1.31  #SimpNegUnit  : 0
% 2.28/1.31  #BackRed      : 0
% 2.28/1.31  
% 2.28/1.31  #Partial instantiations: 0
% 2.28/1.31  #Strategies tried      : 1
% 2.28/1.31  
% 2.28/1.31  Timing (in seconds)
% 2.28/1.31  ----------------------
% 2.58/1.31  Preprocessing        : 0.30
% 2.58/1.31  Parsing              : 0.16
% 2.58/1.31  CNF conversion       : 0.02
% 2.58/1.31  Main loop            : 0.25
% 2.58/1.32  Inferencing          : 0.09
% 2.58/1.32  Reduction            : 0.09
% 2.58/1.32  Demodulation         : 0.07
% 2.58/1.32  BG Simplification    : 0.02
% 2.58/1.32  Subsumption          : 0.04
% 2.58/1.32  Abstraction          : 0.02
% 2.58/1.32  MUC search           : 0.00
% 2.58/1.32  Cooper               : 0.00
% 2.58/1.32  Total                : 0.58
% 2.58/1.32  Index Insertion      : 0.00
% 2.58/1.32  Index Deletion       : 0.00
% 2.58/1.32  Index Matching       : 0.00
% 2.58/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
