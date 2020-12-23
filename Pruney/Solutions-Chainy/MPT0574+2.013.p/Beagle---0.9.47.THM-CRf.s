%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:52 EST 2020

% Result     : Theorem 4.52s
% Output     : CNFRefutation 4.52s
% Verified   : 
% Statistics : Number of formulae       :   72 (  80 expanded)
%              Number of leaves         :   34 (  40 expanded)
%              Depth                    :   10
%              Number of atoms          :   63 (  75 expanded)
%              Number of equality atoms :   41 (  47 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_relat_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k3_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_78,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_relat_1)).

tff(f_61,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_65,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_33,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_67,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_47,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_43,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_49,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_relat_1)).

tff(f_51,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(c_44,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_30,plain,(
    ! [B_26,A_25] : k2_tarski(B_26,A_25) = k2_tarski(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_246,plain,(
    ! [A_59,B_60] : k3_tarski(k2_tarski(A_59,B_60)) = k2_xboole_0(A_59,B_60) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_281,plain,(
    ! [A_65,B_66] : k3_tarski(k2_tarski(A_65,B_66)) = k2_xboole_0(B_66,A_65) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_246])).

tff(c_34,plain,(
    ! [A_29,B_30] : k3_tarski(k2_tarski(A_29,B_30)) = k2_xboole_0(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_287,plain,(
    ! [B_66,A_65] : k2_xboole_0(B_66,A_65) = k2_xboole_0(A_65,B_66) ),
    inference(superposition,[status(thm),theory(equality)],[c_281,c_34])).

tff(c_8,plain,(
    ! [A_7] : k2_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_261,plain,(
    ! [A_61,B_62] : k1_setfam_1(k2_tarski(A_61,B_62)) = k3_xboole_0(A_61,B_62) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_820,plain,(
    ! [B_95,A_96] : k1_setfam_1(k2_tarski(B_95,A_96)) = k3_xboole_0(A_96,B_95) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_261])).

tff(c_36,plain,(
    ! [A_31,B_32] : k1_setfam_1(k2_tarski(A_31,B_32)) = k3_xboole_0(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_843,plain,(
    ! [B_97,A_98] : k3_xboole_0(B_97,A_98) = k3_xboole_0(A_98,B_97) ),
    inference(superposition,[status(thm),theory(equality)],[c_820,c_36])).

tff(c_110,plain,(
    ! [A_44,B_45] : r1_tarski(k3_xboole_0(A_44,B_45),A_44) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_18,plain,(
    ! [A_15] :
      ( k1_xboole_0 = A_15
      | ~ r1_tarski(A_15,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_118,plain,(
    ! [B_45] : k3_xboole_0(k1_xboole_0,B_45) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_110,c_18])).

tff(c_873,plain,(
    ! [B_97] : k3_xboole_0(B_97,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_843,c_118])).

tff(c_16,plain,(
    ! [A_14] : k4_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_520,plain,(
    ! [A_82,B_83] : k4_xboole_0(A_82,k4_xboole_0(A_82,B_83)) = k3_xboole_0(A_82,B_83) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_555,plain,(
    ! [A_14] : k4_xboole_0(A_14,A_14) = k3_xboole_0(A_14,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_520])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_572,plain,(
    ! [A_85,B_86] : k5_xboole_0(A_85,k3_xboole_0(A_85,B_86)) = k4_xboole_0(A_85,B_86) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_590,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_572])).

tff(c_675,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k3_xboole_0(A_1,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_555,c_590])).

tff(c_42,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_188,plain,(
    ! [A_53,B_54] :
      ( k3_xboole_0(A_53,B_54) = A_53
      | ~ r1_tarski(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_209,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_42,c_188])).

tff(c_584,plain,(
    k5_xboole_0('#skF_1','#skF_1') = k4_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_209,c_572])).

tff(c_693,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_xboole_0('#skF_1',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_675,c_584])).

tff(c_913,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_873,c_693])).

tff(c_14,plain,(
    ! [A_12,B_13] : k2_xboole_0(A_12,k4_xboole_0(B_13,A_12)) = k2_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_977,plain,(
    k2_xboole_0('#skF_2',k1_xboole_0) = k2_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_913,c_14])).

tff(c_985,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_287,c_8,c_977])).

tff(c_602,plain,(
    ! [C_87,A_88,B_89] :
      ( k2_xboole_0(k10_relat_1(C_87,A_88),k10_relat_1(C_87,B_89)) = k10_relat_1(C_87,k2_xboole_0(A_88,B_89))
      | ~ v1_relat_1(C_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_22,plain,(
    ! [A_18,B_19] : r1_tarski(A_18,k2_xboole_0(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_3660,plain,(
    ! [C_160,A_161,B_162] :
      ( r1_tarski(k10_relat_1(C_160,A_161),k10_relat_1(C_160,k2_xboole_0(A_161,B_162)))
      | ~ v1_relat_1(C_160) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_602,c_22])).

tff(c_5469,plain,(
    ! [C_195] :
      ( r1_tarski(k10_relat_1(C_195,'#skF_1'),k10_relat_1(C_195,'#skF_2'))
      | ~ v1_relat_1(C_195) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_985,c_3660])).

tff(c_40,plain,(
    ~ r1_tarski(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_5475,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_5469,c_40])).

tff(c_5480,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_5475])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:09:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.52/1.84  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.52/1.84  
% 4.52/1.84  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.52/1.85  %$ r1_xboole_0 > r1_tarski > v1_relat_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k3_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.52/1.85  
% 4.52/1.85  %Foreground sorts:
% 4.52/1.85  
% 4.52/1.85  
% 4.52/1.85  %Background operators:
% 4.52/1.85  
% 4.52/1.85  
% 4.52/1.85  %Foreground operators:
% 4.52/1.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.52/1.85  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.52/1.85  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.52/1.85  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.52/1.85  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.52/1.85  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.52/1.85  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.52/1.85  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.52/1.85  tff('#skF_2', type, '#skF_2': $i).
% 4.52/1.85  tff('#skF_3', type, '#skF_3': $i).
% 4.52/1.85  tff('#skF_1', type, '#skF_1': $i).
% 4.52/1.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.52/1.85  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.52/1.85  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.52/1.85  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.52/1.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.52/1.85  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.52/1.85  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.52/1.85  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.52/1.85  
% 4.52/1.86  tff(f_78, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t178_relat_1)).
% 4.52/1.86  tff(f_61, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 4.52/1.86  tff(f_65, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 4.52/1.86  tff(f_33, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 4.52/1.86  tff(f_67, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 4.52/1.86  tff(f_31, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 4.52/1.86  tff(f_47, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 4.52/1.86  tff(f_43, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 4.52/1.86  tff(f_49, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.52/1.86  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 4.52/1.86  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.52/1.86  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.52/1.86  tff(f_41, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 4.52/1.86  tff(f_71, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_relat_1)).
% 4.52/1.86  tff(f_51, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 4.52/1.86  tff(c_44, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.52/1.86  tff(c_30, plain, (![B_26, A_25]: (k2_tarski(B_26, A_25)=k2_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.52/1.86  tff(c_246, plain, (![A_59, B_60]: (k3_tarski(k2_tarski(A_59, B_60))=k2_xboole_0(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.52/1.86  tff(c_281, plain, (![A_65, B_66]: (k3_tarski(k2_tarski(A_65, B_66))=k2_xboole_0(B_66, A_65))), inference(superposition, [status(thm), theory('equality')], [c_30, c_246])).
% 4.52/1.86  tff(c_34, plain, (![A_29, B_30]: (k3_tarski(k2_tarski(A_29, B_30))=k2_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.52/1.86  tff(c_287, plain, (![B_66, A_65]: (k2_xboole_0(B_66, A_65)=k2_xboole_0(A_65, B_66))), inference(superposition, [status(thm), theory('equality')], [c_281, c_34])).
% 4.52/1.86  tff(c_8, plain, (![A_7]: (k2_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.52/1.86  tff(c_261, plain, (![A_61, B_62]: (k1_setfam_1(k2_tarski(A_61, B_62))=k3_xboole_0(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.52/1.86  tff(c_820, plain, (![B_95, A_96]: (k1_setfam_1(k2_tarski(B_95, A_96))=k3_xboole_0(A_96, B_95))), inference(superposition, [status(thm), theory('equality')], [c_30, c_261])).
% 4.52/1.86  tff(c_36, plain, (![A_31, B_32]: (k1_setfam_1(k2_tarski(A_31, B_32))=k3_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.52/1.86  tff(c_843, plain, (![B_97, A_98]: (k3_xboole_0(B_97, A_98)=k3_xboole_0(A_98, B_97))), inference(superposition, [status(thm), theory('equality')], [c_820, c_36])).
% 4.52/1.86  tff(c_110, plain, (![A_44, B_45]: (r1_tarski(k3_xboole_0(A_44, B_45), A_44))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.52/1.86  tff(c_18, plain, (![A_15]: (k1_xboole_0=A_15 | ~r1_tarski(A_15, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.52/1.86  tff(c_118, plain, (![B_45]: (k3_xboole_0(k1_xboole_0, B_45)=k1_xboole_0)), inference(resolution, [status(thm)], [c_110, c_18])).
% 4.52/1.86  tff(c_873, plain, (![B_97]: (k3_xboole_0(B_97, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_843, c_118])).
% 4.52/1.86  tff(c_16, plain, (![A_14]: (k4_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.52/1.86  tff(c_520, plain, (![A_82, B_83]: (k4_xboole_0(A_82, k4_xboole_0(A_82, B_83))=k3_xboole_0(A_82, B_83))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.52/1.86  tff(c_555, plain, (![A_14]: (k4_xboole_0(A_14, A_14)=k3_xboole_0(A_14, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_520])).
% 4.52/1.86  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.52/1.86  tff(c_572, plain, (![A_85, B_86]: (k5_xboole_0(A_85, k3_xboole_0(A_85, B_86))=k4_xboole_0(A_85, B_86))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.52/1.86  tff(c_590, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_572])).
% 4.52/1.86  tff(c_675, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k3_xboole_0(A_1, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_555, c_590])).
% 4.52/1.86  tff(c_42, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.52/1.86  tff(c_188, plain, (![A_53, B_54]: (k3_xboole_0(A_53, B_54)=A_53 | ~r1_tarski(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.52/1.86  tff(c_209, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_42, c_188])).
% 4.52/1.86  tff(c_584, plain, (k5_xboole_0('#skF_1', '#skF_1')=k4_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_209, c_572])).
% 4.52/1.86  tff(c_693, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_xboole_0('#skF_1', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_675, c_584])).
% 4.52/1.86  tff(c_913, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_873, c_693])).
% 4.52/1.86  tff(c_14, plain, (![A_12, B_13]: (k2_xboole_0(A_12, k4_xboole_0(B_13, A_12))=k2_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.52/1.86  tff(c_977, plain, (k2_xboole_0('#skF_2', k1_xboole_0)=k2_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_913, c_14])).
% 4.52/1.86  tff(c_985, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_287, c_8, c_977])).
% 4.52/1.86  tff(c_602, plain, (![C_87, A_88, B_89]: (k2_xboole_0(k10_relat_1(C_87, A_88), k10_relat_1(C_87, B_89))=k10_relat_1(C_87, k2_xboole_0(A_88, B_89)) | ~v1_relat_1(C_87))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.52/1.86  tff(c_22, plain, (![A_18, B_19]: (r1_tarski(A_18, k2_xboole_0(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.52/1.86  tff(c_3660, plain, (![C_160, A_161, B_162]: (r1_tarski(k10_relat_1(C_160, A_161), k10_relat_1(C_160, k2_xboole_0(A_161, B_162))) | ~v1_relat_1(C_160))), inference(superposition, [status(thm), theory('equality')], [c_602, c_22])).
% 4.52/1.86  tff(c_5469, plain, (![C_195]: (r1_tarski(k10_relat_1(C_195, '#skF_1'), k10_relat_1(C_195, '#skF_2')) | ~v1_relat_1(C_195))), inference(superposition, [status(thm), theory('equality')], [c_985, c_3660])).
% 4.52/1.86  tff(c_40, plain, (~r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.52/1.86  tff(c_5475, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_5469, c_40])).
% 4.52/1.86  tff(c_5480, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_5475])).
% 4.52/1.86  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.52/1.86  
% 4.52/1.86  Inference rules
% 4.52/1.86  ----------------------
% 4.52/1.86  #Ref     : 0
% 4.52/1.86  #Sup     : 1347
% 4.52/1.86  #Fact    : 0
% 4.52/1.86  #Define  : 0
% 4.52/1.86  #Split   : 0
% 4.52/1.86  #Chain   : 0
% 4.52/1.86  #Close   : 0
% 4.52/1.86  
% 4.52/1.86  Ordering : KBO
% 4.52/1.86  
% 4.52/1.86  Simplification rules
% 4.52/1.86  ----------------------
% 4.52/1.86  #Subsume      : 59
% 4.52/1.86  #Demod        : 1343
% 4.52/1.86  #Tautology    : 1050
% 4.52/1.86  #SimpNegUnit  : 0
% 4.52/1.86  #BackRed      : 4
% 4.52/1.86  
% 4.52/1.86  #Partial instantiations: 0
% 4.52/1.86  #Strategies tried      : 1
% 4.52/1.86  
% 4.52/1.86  Timing (in seconds)
% 4.52/1.86  ----------------------
% 4.52/1.86  Preprocessing        : 0.29
% 4.52/1.86  Parsing              : 0.15
% 4.52/1.86  CNF conversion       : 0.02
% 4.52/1.86  Main loop            : 0.80
% 4.52/1.86  Inferencing          : 0.25
% 4.52/1.86  Reduction            : 0.37
% 4.52/1.86  Demodulation         : 0.30
% 4.52/1.86  BG Simplification    : 0.03
% 4.52/1.86  Subsumption          : 0.11
% 4.52/1.86  Abstraction          : 0.04
% 4.52/1.86  MUC search           : 0.00
% 4.52/1.86  Cooper               : 0.00
% 4.52/1.86  Total                : 1.12
% 4.52/1.86  Index Insertion      : 0.00
% 4.52/1.86  Index Deletion       : 0.00
% 4.52/1.86  Index Matching       : 0.00
% 4.52/1.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
