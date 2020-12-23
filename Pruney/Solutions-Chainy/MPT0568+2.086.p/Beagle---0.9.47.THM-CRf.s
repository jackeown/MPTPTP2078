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
% DateTime   : Thu Dec  3 10:01:31 EST 2020

% Result     : Theorem 2.66s
% Output     : CNFRefutation 2.86s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 121 expanded)
%              Number of leaves         :   40 (  58 expanded)
%              Depth                    :   10
%              Number of atoms          :   74 ( 134 expanded)
%              Number of equality atoms :   45 (  75 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k3_tarski > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_66,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_89,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_74,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_relat_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_85,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_82,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_28,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_46,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_30,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_34,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_44,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k10_relat_1(B,A) = k10_relat_1(B,k3_xboole_0(k2_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).

tff(f_92,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_36,plain,(
    ! [A_47] : v1_relat_1(k6_relat_1(A_47)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_48,plain,(
    ! [A_52] : k1_relat_1(k6_relat_1(A_52)) = A_52 ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_131,plain,(
    ! [A_65] :
      ( ~ v1_xboole_0(k1_relat_1(A_65))
      | ~ v1_relat_1(A_65)
      | v1_xboole_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_134,plain,(
    ! [A_52] :
      ( ~ v1_xboole_0(A_52)
      | ~ v1_relat_1(k6_relat_1(A_52))
      | v1_xboole_0(k6_relat_1(A_52)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_131])).

tff(c_151,plain,(
    ! [A_68] :
      ( ~ v1_xboole_0(A_68)
      | v1_xboole_0(k6_relat_1(A_68)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_134])).

tff(c_112,plain,(
    ! [B_60,A_61] :
      ( ~ v1_xboole_0(B_60)
      | B_60 = A_61
      | ~ v1_xboole_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_115,plain,(
    ! [A_61] :
      ( k1_xboole_0 = A_61
      | ~ v1_xboole_0(A_61) ) ),
    inference(resolution,[status(thm)],[c_2,c_112])).

tff(c_159,plain,(
    ! [A_69] :
      ( k6_relat_1(A_69) = k1_xboole_0
      | ~ v1_xboole_0(A_69) ) ),
    inference(resolution,[status(thm)],[c_151,c_115])).

tff(c_167,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_159])).

tff(c_179,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_36])).

tff(c_46,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_44,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_240,plain,(
    ! [A_75] :
      ( k10_relat_1(A_75,k2_relat_1(A_75)) = k1_relat_1(A_75)
      | ~ v1_relat_1(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_252,plain,
    ( k10_relat_1(k1_xboole_0,k1_xboole_0) = k1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_240])).

tff(c_258,plain,(
    k10_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_46,c_252])).

tff(c_4,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_16,plain,(
    ! [A_13] : k5_xboole_0(A_13,A_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_6,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_263,plain,(
    ! [A_76,B_77] : k5_xboole_0(A_76,k3_xboole_0(A_76,B_77)) = k4_xboole_0(A_76,B_77) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_272,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k4_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_263])).

tff(c_275,plain,(
    ! [A_3] : k4_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_272])).

tff(c_307,plain,(
    ! [A_80,B_81] : k5_xboole_0(A_80,k4_xboole_0(B_81,A_80)) = k2_xboole_0(A_80,B_81) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_316,plain,(
    ! [A_3] : k5_xboole_0(A_3,k1_xboole_0) = k2_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_275,c_307])).

tff(c_322,plain,(
    ! [A_3] : k5_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_316])).

tff(c_10,plain,(
    ! [A_7] : k4_xboole_0(k1_xboole_0,A_7) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_8,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_403,plain,(
    ! [A_92,B_93,C_94] : k5_xboole_0(k5_xboole_0(A_92,B_93),C_94) = k5_xboole_0(A_92,k5_xboole_0(B_93,C_94)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_466,plain,(
    ! [A_95,B_96] : k5_xboole_0(A_95,k5_xboole_0(B_96,k5_xboole_0(A_95,B_96))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_403,c_16])).

tff(c_515,plain,(
    ! [A_97] : k5_xboole_0(A_97,k5_xboole_0(k1_xboole_0,A_97)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_322,c_466])).

tff(c_560,plain,(
    ! [B_6] : k5_xboole_0(k3_xboole_0(k1_xboole_0,B_6),k4_xboole_0(k1_xboole_0,B_6)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_515])).

tff(c_574,plain,(
    ! [B_6] : k3_xboole_0(k1_xboole_0,B_6) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_322,c_10,c_560])).

tff(c_886,plain,(
    ! [B_109,A_110] :
      ( k10_relat_1(B_109,k3_xboole_0(k2_relat_1(B_109),A_110)) = k10_relat_1(B_109,A_110)
      | ~ v1_relat_1(B_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_902,plain,(
    ! [A_110] :
      ( k10_relat_1(k1_xboole_0,k3_xboole_0(k1_xboole_0,A_110)) = k10_relat_1(k1_xboole_0,A_110)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_886])).

tff(c_909,plain,(
    ! [A_110] : k10_relat_1(k1_xboole_0,A_110) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_258,c_574,c_902])).

tff(c_52,plain,(
    k10_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_914,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_909,c_52])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:05:35 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.66/1.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.66/1.37  
% 2.66/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.66/1.37  %$ v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k3_tarski > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 2.66/1.37  
% 2.66/1.37  %Foreground sorts:
% 2.66/1.37  
% 2.66/1.37  
% 2.66/1.37  %Background operators:
% 2.66/1.37  
% 2.66/1.37  
% 2.66/1.37  %Foreground operators:
% 2.66/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.66/1.37  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.66/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.66/1.37  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.66/1.37  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.66/1.37  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.66/1.37  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.66/1.37  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.66/1.37  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.66/1.37  tff('#skF_1', type, '#skF_1': $i).
% 2.66/1.37  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.66/1.37  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.66/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.66/1.37  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.66/1.37  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.66/1.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.66/1.37  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.66/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.66/1.37  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.66/1.37  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.66/1.37  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.66/1.37  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.66/1.37  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.66/1.37  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.66/1.37  
% 2.86/1.39  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.86/1.39  tff(f_66, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.86/1.39  tff(f_89, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.86/1.39  tff(f_74, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc8_relat_1)).
% 2.86/1.39  tff(f_42, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 2.86/1.39  tff(f_85, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.86/1.39  tff(f_82, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 2.86/1.39  tff(f_28, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 2.86/1.39  tff(f_46, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.86/1.39  tff(f_30, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.86/1.39  tff(f_32, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.86/1.39  tff(f_48, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.86/1.39  tff(f_34, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 2.86/1.39  tff(f_44, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 2.86/1.39  tff(f_78, axiom, (![A, B]: (v1_relat_1(B) => (k10_relat_1(B, A) = k10_relat_1(B, k3_xboole_0(k2_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t168_relat_1)).
% 2.86/1.39  tff(f_92, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_relat_1)).
% 2.86/1.39  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.86/1.39  tff(c_36, plain, (![A_47]: (v1_relat_1(k6_relat_1(A_47)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.86/1.39  tff(c_48, plain, (![A_52]: (k1_relat_1(k6_relat_1(A_52))=A_52)), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.86/1.39  tff(c_131, plain, (![A_65]: (~v1_xboole_0(k1_relat_1(A_65)) | ~v1_relat_1(A_65) | v1_xboole_0(A_65))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.86/1.39  tff(c_134, plain, (![A_52]: (~v1_xboole_0(A_52) | ~v1_relat_1(k6_relat_1(A_52)) | v1_xboole_0(k6_relat_1(A_52)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_131])).
% 2.86/1.39  tff(c_151, plain, (![A_68]: (~v1_xboole_0(A_68) | v1_xboole_0(k6_relat_1(A_68)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_134])).
% 2.86/1.39  tff(c_112, plain, (![B_60, A_61]: (~v1_xboole_0(B_60) | B_60=A_61 | ~v1_xboole_0(A_61))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.86/1.39  tff(c_115, plain, (![A_61]: (k1_xboole_0=A_61 | ~v1_xboole_0(A_61))), inference(resolution, [status(thm)], [c_2, c_112])).
% 2.86/1.39  tff(c_159, plain, (![A_69]: (k6_relat_1(A_69)=k1_xboole_0 | ~v1_xboole_0(A_69))), inference(resolution, [status(thm)], [c_151, c_115])).
% 2.86/1.39  tff(c_167, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_159])).
% 2.86/1.39  tff(c_179, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_167, c_36])).
% 2.86/1.39  tff(c_46, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.86/1.39  tff(c_44, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.86/1.39  tff(c_240, plain, (![A_75]: (k10_relat_1(A_75, k2_relat_1(A_75))=k1_relat_1(A_75) | ~v1_relat_1(A_75))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.86/1.39  tff(c_252, plain, (k10_relat_1(k1_xboole_0, k1_xboole_0)=k1_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_44, c_240])).
% 2.86/1.39  tff(c_258, plain, (k10_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_179, c_46, c_252])).
% 2.86/1.39  tff(c_4, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_28])).
% 2.86/1.39  tff(c_16, plain, (![A_13]: (k5_xboole_0(A_13, A_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.86/1.39  tff(c_6, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.86/1.39  tff(c_263, plain, (![A_76, B_77]: (k5_xboole_0(A_76, k3_xboole_0(A_76, B_77))=k4_xboole_0(A_76, B_77))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.86/1.39  tff(c_272, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k4_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_6, c_263])).
% 2.86/1.39  tff(c_275, plain, (![A_3]: (k4_xboole_0(A_3, A_3)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_272])).
% 2.86/1.39  tff(c_307, plain, (![A_80, B_81]: (k5_xboole_0(A_80, k4_xboole_0(B_81, A_80))=k2_xboole_0(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.86/1.39  tff(c_316, plain, (![A_3]: (k5_xboole_0(A_3, k1_xboole_0)=k2_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_275, c_307])).
% 2.86/1.39  tff(c_322, plain, (![A_3]: (k5_xboole_0(A_3, k1_xboole_0)=A_3)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_316])).
% 2.86/1.39  tff(c_10, plain, (![A_7]: (k4_xboole_0(k1_xboole_0, A_7)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.86/1.39  tff(c_8, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.86/1.39  tff(c_403, plain, (![A_92, B_93, C_94]: (k5_xboole_0(k5_xboole_0(A_92, B_93), C_94)=k5_xboole_0(A_92, k5_xboole_0(B_93, C_94)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.86/1.39  tff(c_466, plain, (![A_95, B_96]: (k5_xboole_0(A_95, k5_xboole_0(B_96, k5_xboole_0(A_95, B_96)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_403, c_16])).
% 2.86/1.39  tff(c_515, plain, (![A_97]: (k5_xboole_0(A_97, k5_xboole_0(k1_xboole_0, A_97))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_322, c_466])).
% 2.86/1.39  tff(c_560, plain, (![B_6]: (k5_xboole_0(k3_xboole_0(k1_xboole_0, B_6), k4_xboole_0(k1_xboole_0, B_6))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8, c_515])).
% 2.86/1.39  tff(c_574, plain, (![B_6]: (k3_xboole_0(k1_xboole_0, B_6)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_322, c_10, c_560])).
% 2.86/1.39  tff(c_886, plain, (![B_109, A_110]: (k10_relat_1(B_109, k3_xboole_0(k2_relat_1(B_109), A_110))=k10_relat_1(B_109, A_110) | ~v1_relat_1(B_109))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.86/1.39  tff(c_902, plain, (![A_110]: (k10_relat_1(k1_xboole_0, k3_xboole_0(k1_xboole_0, A_110))=k10_relat_1(k1_xboole_0, A_110) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_44, c_886])).
% 2.86/1.39  tff(c_909, plain, (![A_110]: (k10_relat_1(k1_xboole_0, A_110)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_179, c_258, c_574, c_902])).
% 2.86/1.39  tff(c_52, plain, (k10_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.86/1.39  tff(c_914, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_909, c_52])).
% 2.86/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.86/1.39  
% 2.86/1.39  Inference rules
% 2.86/1.39  ----------------------
% 2.86/1.39  #Ref     : 0
% 2.86/1.39  #Sup     : 204
% 2.86/1.39  #Fact    : 0
% 2.86/1.39  #Define  : 0
% 2.86/1.39  #Split   : 0
% 2.86/1.39  #Chain   : 0
% 2.86/1.39  #Close   : 0
% 2.86/1.39  
% 2.86/1.39  Ordering : KBO
% 2.86/1.39  
% 2.86/1.39  Simplification rules
% 2.86/1.39  ----------------------
% 2.86/1.39  #Subsume      : 9
% 2.86/1.39  #Demod        : 131
% 2.86/1.39  #Tautology    : 140
% 2.86/1.39  #SimpNegUnit  : 0
% 2.86/1.39  #BackRed      : 4
% 2.86/1.39  
% 2.86/1.39  #Partial instantiations: 0
% 2.86/1.39  #Strategies tried      : 1
% 2.86/1.39  
% 2.86/1.39  Timing (in seconds)
% 2.86/1.39  ----------------------
% 2.86/1.39  Preprocessing        : 0.32
% 2.86/1.39  Parsing              : 0.18
% 2.86/1.39  CNF conversion       : 0.02
% 2.86/1.39  Main loop            : 0.30
% 2.86/1.39  Inferencing          : 0.12
% 2.86/1.39  Reduction            : 0.10
% 2.86/1.39  Demodulation         : 0.07
% 2.86/1.39  BG Simplification    : 0.02
% 2.86/1.39  Subsumption          : 0.05
% 2.86/1.39  Abstraction          : 0.02
% 2.86/1.39  MUC search           : 0.00
% 2.86/1.39  Cooper               : 0.00
% 2.86/1.39  Total                : 0.65
% 2.86/1.39  Index Insertion      : 0.00
% 2.86/1.39  Index Deletion       : 0.00
% 2.86/1.39  Index Matching       : 0.00
% 2.86/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
