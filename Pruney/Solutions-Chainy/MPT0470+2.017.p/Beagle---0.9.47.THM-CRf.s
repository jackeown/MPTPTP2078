%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:03 EST 2020

% Result     : Theorem 6.84s
% Output     : CNFRefutation 6.84s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 539 expanded)
%              Number of leaves         :   44 ( 201 expanded)
%              Depth                    :   23
%              Number of atoms          :  257 ( 821 expanded)
%              Number of equality atoms :   92 ( 411 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k6_subset_1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k4_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

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

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_115,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_70,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_42,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_28,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_36,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_60,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_91,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k4_relat_1(k6_subset_1(A,B)) = k6_subset_1(k4_relat_1(A),k4_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_relat_1)).

tff(f_105,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k4_relat_1(k5_relat_1(A,B)) = k5_relat_1(k4_relat_1(B),k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_38,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k4_xboole_0(A,B),C) = k4_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
      & k2_zfmisc_1(C,k4_xboole_0(A,B)) = k4_xboole_0(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_zfmisc_1)).

tff(f_108,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_98,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k5_relat_1(A,B)),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_84,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_xboole_0(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relat_1)).

tff(f_80,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k4_relat_1(k4_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

tff(c_60,plain,
    ( k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_106,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_62,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_42,plain,(
    ! [A_45] :
      ( v1_relat_1(k4_relat_1(A_45))
      | ~ v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_101,plain,(
    ! [A_63] :
      ( v1_relat_1(A_63)
      | ~ v1_xboole_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_105,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_101])).

tff(c_18,plain,(
    ! [A_9] : k5_xboole_0(A_9,A_9) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_4,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_172,plain,(
    ! [A_75,B_76] : k5_xboole_0(A_75,k3_xboole_0(A_75,B_76)) = k4_xboole_0(A_75,B_76) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_184,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_172])).

tff(c_187,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_184])).

tff(c_36,plain,(
    ! [A_40,B_41] : k6_subset_1(A_40,B_41) = k4_xboole_0(A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_50,plain,(
    ! [A_50,B_52] :
      ( k6_subset_1(k4_relat_1(A_50),k4_relat_1(B_52)) = k4_relat_1(k6_subset_1(A_50,B_52))
      | ~ v1_relat_1(B_52)
      | ~ v1_relat_1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_500,plain,(
    ! [A_107,B_108] :
      ( k4_xboole_0(k4_relat_1(A_107),k4_relat_1(B_108)) = k4_relat_1(k4_xboole_0(A_107,B_108))
      | ~ v1_relat_1(B_108)
      | ~ v1_relat_1(A_107) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_36,c_50])).

tff(c_507,plain,(
    ! [B_108] :
      ( k4_relat_1(k4_xboole_0(B_108,B_108)) = k1_xboole_0
      | ~ v1_relat_1(B_108)
      | ~ v1_relat_1(B_108) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_500,c_187])).

tff(c_522,plain,(
    ! [B_108] :
      ( k4_relat_1(k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(B_108)
      | ~ v1_relat_1(B_108) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_187,c_507])).

tff(c_526,plain,(
    ! [B_109] :
      ( ~ v1_relat_1(B_109)
      | ~ v1_relat_1(B_109) ) ),
    inference(splitLeft,[status(thm)],[c_522])).

tff(c_532,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_105,c_526])).

tff(c_540,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_532])).

tff(c_541,plain,(
    k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_522])).

tff(c_566,plain,(
    ! [B_110,A_111] :
      ( k5_relat_1(k4_relat_1(B_110),k4_relat_1(A_111)) = k4_relat_1(k5_relat_1(A_111,B_110))
      | ~ v1_relat_1(B_110)
      | ~ v1_relat_1(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_44,plain,(
    ! [A_46,B_47] :
      ( v1_relat_1(k5_relat_1(A_46,B_47))
      | ~ v1_relat_1(B_47)
      | ~ v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_575,plain,(
    ! [A_111,B_110] :
      ( v1_relat_1(k4_relat_1(k5_relat_1(A_111,B_110)))
      | ~ v1_relat_1(k4_relat_1(A_111))
      | ~ v1_relat_1(k4_relat_1(B_110))
      | ~ v1_relat_1(B_110)
      | ~ v1_relat_1(A_111) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_566,c_44])).

tff(c_14,plain,(
    ! [A_7] : k3_xboole_0(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_347,plain,(
    ! [C_95,A_96,B_97] : k4_xboole_0(k2_zfmisc_1(C_95,A_96),k2_zfmisc_1(C_95,B_97)) = k2_zfmisc_1(C_95,k4_xboole_0(A_96,B_97)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_354,plain,(
    ! [C_95,B_97] : k2_zfmisc_1(C_95,k4_xboole_0(B_97,B_97)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_347,c_187])).

tff(c_363,plain,(
    ! [C_95] : k2_zfmisc_1(C_95,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_187,c_354])).

tff(c_409,plain,(
    ! [A_101,C_102,B_103] : k4_xboole_0(k2_zfmisc_1(A_101,C_102),k2_zfmisc_1(B_103,C_102)) = k2_zfmisc_1(k4_xboole_0(A_101,B_103),C_102) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_34,plain,(
    ! [C_39,A_37,B_38] : k4_xboole_0(k2_zfmisc_1(C_39,A_37),k2_zfmisc_1(C_39,B_38)) = k2_zfmisc_1(C_39,k4_xboole_0(A_37,B_38)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_416,plain,(
    ! [B_103,C_102] : k2_zfmisc_1(k4_xboole_0(B_103,B_103),C_102) = k2_zfmisc_1(B_103,k4_xboole_0(C_102,C_102)) ),
    inference(superposition,[status(thm),theory(equality)],[c_409,c_34])).

tff(c_439,plain,(
    ! [C_102] : k2_zfmisc_1(k1_xboole_0,C_102) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_363,c_187,c_187,c_416])).

tff(c_581,plain,(
    ! [A_111] :
      ( k5_relat_1(k1_xboole_0,k4_relat_1(A_111)) = k4_relat_1(k5_relat_1(A_111,k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_111) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_541,c_566])).

tff(c_615,plain,(
    ! [A_113] :
      ( k5_relat_1(k1_xboole_0,k4_relat_1(A_113)) = k4_relat_1(k5_relat_1(A_113,k1_xboole_0))
      | ~ v1_relat_1(A_113) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_581])).

tff(c_58,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_273,plain,(
    ! [A_86,B_87] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_86,B_87)),k1_relat_1(A_86))
      | ~ v1_relat_1(B_87)
      | ~ v1_relat_1(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_278,plain,(
    ! [B_87] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_87)),k1_xboole_0)
      | ~ v1_relat_1(B_87)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_273])).

tff(c_282,plain,(
    ! [B_88] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_88)),k1_xboole_0)
      | ~ v1_relat_1(B_88) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_278])).

tff(c_16,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_162,plain,(
    ! [B_73,A_74] :
      ( B_73 = A_74
      | ~ r1_tarski(B_73,A_74)
      | ~ r1_tarski(A_74,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_171,plain,(
    ! [A_8] :
      ( k1_xboole_0 = A_8
      | ~ r1_tarski(A_8,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_16,c_162])).

tff(c_288,plain,(
    ! [B_88] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_88)) = k1_xboole_0
      | ~ v1_relat_1(B_88) ) ),
    inference(resolution,[status(thm)],[c_282,c_171])).

tff(c_884,plain,(
    ! [A_133] :
      ( k1_relat_1(k4_relat_1(k5_relat_1(A_133,k1_xboole_0))) = k1_xboole_0
      | ~ v1_relat_1(k4_relat_1(A_133))
      | ~ v1_relat_1(A_133) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_615,c_288])).

tff(c_48,plain,(
    ! [A_49] :
      ( k3_xboole_0(A_49,k2_zfmisc_1(k1_relat_1(A_49),k2_relat_1(A_49))) = A_49
      | ~ v1_relat_1(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_896,plain,(
    ! [A_133] :
      ( k3_xboole_0(k4_relat_1(k5_relat_1(A_133,k1_xboole_0)),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k4_relat_1(k5_relat_1(A_133,k1_xboole_0))))) = k4_relat_1(k5_relat_1(A_133,k1_xboole_0))
      | ~ v1_relat_1(k4_relat_1(k5_relat_1(A_133,k1_xboole_0)))
      | ~ v1_relat_1(k4_relat_1(A_133))
      | ~ v1_relat_1(A_133) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_884,c_48])).

tff(c_2858,plain,(
    ! [A_180] :
      ( k4_relat_1(k5_relat_1(A_180,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(k4_relat_1(k5_relat_1(A_180,k1_xboole_0)))
      | ~ v1_relat_1(k4_relat_1(A_180))
      | ~ v1_relat_1(A_180) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_439,c_896])).

tff(c_2866,plain,(
    ! [A_111] :
      ( k4_relat_1(k5_relat_1(A_111,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(k4_relat_1(A_111))
      | ~ v1_relat_1(k4_relat_1(k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_111) ) ),
    inference(resolution,[status(thm)],[c_575,c_2858])).

tff(c_2898,plain,(
    ! [A_181] :
      ( k4_relat_1(k5_relat_1(A_181,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(k4_relat_1(A_181))
      | ~ v1_relat_1(A_181) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_105,c_541,c_2866])).

tff(c_3122,plain,(
    ! [A_184] :
      ( k4_relat_1(k5_relat_1(A_184,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(A_184) ) ),
    inference(resolution,[status(thm)],[c_42,c_2898])).

tff(c_46,plain,(
    ! [A_48] :
      ( k4_relat_1(k4_relat_1(A_48)) = A_48
      | ~ v1_relat_1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_590,plain,(
    ! [A_48,B_110] :
      ( k4_relat_1(k5_relat_1(k4_relat_1(A_48),B_110)) = k5_relat_1(k4_relat_1(B_110),A_48)
      | ~ v1_relat_1(B_110)
      | ~ v1_relat_1(k4_relat_1(A_48))
      | ~ v1_relat_1(A_48) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_566])).

tff(c_3164,plain,(
    ! [A_48] :
      ( k5_relat_1(k4_relat_1(k1_xboole_0),A_48) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k4_relat_1(A_48))
      | ~ v1_relat_1(A_48)
      | ~ v1_relat_1(k4_relat_1(A_48)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3122,c_590])).

tff(c_3288,plain,(
    ! [A_185] :
      ( k5_relat_1(k1_xboole_0,A_185) = k1_xboole_0
      | ~ v1_relat_1(A_185)
      | ~ v1_relat_1(k4_relat_1(A_185)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_541,c_3164])).

tff(c_3359,plain,(
    ! [A_186] :
      ( k5_relat_1(k1_xboole_0,A_186) = k1_xboole_0
      | ~ v1_relat_1(A_186) ) ),
    inference(resolution,[status(thm)],[c_42,c_3288])).

tff(c_3392,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_62,c_3359])).

tff(c_3407,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_3392])).

tff(c_3408,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_3498,plain,(
    ! [A_201,B_202] : k5_xboole_0(A_201,k3_xboole_0(A_201,B_202)) = k4_xboole_0(A_201,B_202) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_3510,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_3498])).

tff(c_3513,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_3510])).

tff(c_4018,plain,(
    ! [A_245,B_246] :
      ( k4_xboole_0(k4_relat_1(A_245),k4_relat_1(B_246)) = k4_relat_1(k4_xboole_0(A_245,B_246))
      | ~ v1_relat_1(B_246)
      | ~ v1_relat_1(A_245) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_36,c_50])).

tff(c_4025,plain,(
    ! [B_246] :
      ( k4_relat_1(k4_xboole_0(B_246,B_246)) = k1_xboole_0
      | ~ v1_relat_1(B_246)
      | ~ v1_relat_1(B_246) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4018,c_3513])).

tff(c_4040,plain,(
    ! [B_246] :
      ( k4_relat_1(k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(B_246)
      | ~ v1_relat_1(B_246) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3513,c_4025])).

tff(c_4044,plain,(
    ! [B_247] :
      ( ~ v1_relat_1(B_247)
      | ~ v1_relat_1(B_247) ) ),
    inference(splitLeft,[status(thm)],[c_4040])).

tff(c_4050,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_105,c_4044])).

tff(c_4058,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_4050])).

tff(c_4059,plain,(
    k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_4040])).

tff(c_3938,plain,(
    ! [B_241,A_242] :
      ( k5_relat_1(k4_relat_1(B_241),k4_relat_1(A_242)) = k4_relat_1(k5_relat_1(A_242,B_241))
      | ~ v1_relat_1(B_241)
      | ~ v1_relat_1(A_242) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_3947,plain,(
    ! [A_242,B_241] :
      ( v1_relat_1(k4_relat_1(k5_relat_1(A_242,B_241)))
      | ~ v1_relat_1(k4_relat_1(A_242))
      | ~ v1_relat_1(k4_relat_1(B_241))
      | ~ v1_relat_1(B_241)
      | ~ v1_relat_1(A_242) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3938,c_44])).

tff(c_3674,plain,(
    ! [A_218,C_219,B_220] : k4_xboole_0(k2_zfmisc_1(A_218,C_219),k2_zfmisc_1(B_220,C_219)) = k2_zfmisc_1(k4_xboole_0(A_218,B_220),C_219) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_3681,plain,(
    ! [B_220,C_219] : k2_zfmisc_1(k4_xboole_0(B_220,B_220),C_219) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_3674,c_3513])).

tff(c_3690,plain,(
    ! [C_219] : k2_zfmisc_1(k1_xboole_0,C_219) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3513,c_3681])).

tff(c_54,plain,(
    ! [B_58,A_56] :
      ( k5_relat_1(k4_relat_1(B_58),k4_relat_1(A_56)) = k4_relat_1(k5_relat_1(A_56,B_58))
      | ~ v1_relat_1(B_58)
      | ~ v1_relat_1(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_4069,plain,(
    ! [A_56] :
      ( k5_relat_1(k1_xboole_0,k4_relat_1(A_56)) = k4_relat_1(k5_relat_1(A_56,k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_56) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4059,c_54])).

tff(c_4166,plain,(
    ! [A_262] :
      ( k5_relat_1(k1_xboole_0,k4_relat_1(A_262)) = k4_relat_1(k5_relat_1(A_262,k1_xboole_0))
      | ~ v1_relat_1(A_262) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_4069])).

tff(c_3585,plain,(
    ! [A_209,B_210] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_209,B_210)),k1_relat_1(A_209))
      | ~ v1_relat_1(B_210)
      | ~ v1_relat_1(A_209) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_3593,plain,(
    ! [B_210] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_210)),k1_xboole_0)
      | ~ v1_relat_1(B_210)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_3585])).

tff(c_3599,plain,(
    ! [B_211] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_211)),k1_xboole_0)
      | ~ v1_relat_1(B_211) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_3593])).

tff(c_3469,plain,(
    ! [B_196,A_197] :
      ( B_196 = A_197
      | ~ r1_tarski(B_196,A_197)
      | ~ r1_tarski(A_197,B_196) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_3478,plain,(
    ! [A_8] :
      ( k1_xboole_0 = A_8
      | ~ r1_tarski(A_8,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_16,c_3469])).

tff(c_3608,plain,(
    ! [B_211] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_211)) = k1_xboole_0
      | ~ v1_relat_1(B_211) ) ),
    inference(resolution,[status(thm)],[c_3599,c_3478])).

tff(c_4295,plain,(
    ! [A_269] :
      ( k1_relat_1(k4_relat_1(k5_relat_1(A_269,k1_xboole_0))) = k1_xboole_0
      | ~ v1_relat_1(k4_relat_1(A_269))
      | ~ v1_relat_1(A_269) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4166,c_3608])).

tff(c_4307,plain,(
    ! [A_269] :
      ( k3_xboole_0(k4_relat_1(k5_relat_1(A_269,k1_xboole_0)),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k4_relat_1(k5_relat_1(A_269,k1_xboole_0))))) = k4_relat_1(k5_relat_1(A_269,k1_xboole_0))
      | ~ v1_relat_1(k4_relat_1(k5_relat_1(A_269,k1_xboole_0)))
      | ~ v1_relat_1(k4_relat_1(A_269))
      | ~ v1_relat_1(A_269) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4295,c_48])).

tff(c_6835,plain,(
    ! [A_316] :
      ( k4_relat_1(k5_relat_1(A_316,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(k4_relat_1(k5_relat_1(A_316,k1_xboole_0)))
      | ~ v1_relat_1(k4_relat_1(A_316))
      | ~ v1_relat_1(A_316) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_3690,c_4307])).

tff(c_6853,plain,(
    ! [A_242] :
      ( k4_relat_1(k5_relat_1(A_242,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(k4_relat_1(A_242))
      | ~ v1_relat_1(k4_relat_1(k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_242) ) ),
    inference(resolution,[status(thm)],[c_3947,c_6835])).

tff(c_6875,plain,(
    ! [A_317] :
      ( k4_relat_1(k5_relat_1(A_317,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(k4_relat_1(A_317))
      | ~ v1_relat_1(A_317) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_105,c_4059,c_6853])).

tff(c_6996,plain,(
    ! [A_320] :
      ( k4_relat_1(k5_relat_1(A_320,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(A_320) ) ),
    inference(resolution,[status(thm)],[c_42,c_6875])).

tff(c_3956,plain,(
    ! [A_48,B_241] :
      ( k4_relat_1(k5_relat_1(k4_relat_1(A_48),B_241)) = k5_relat_1(k4_relat_1(B_241),A_48)
      | ~ v1_relat_1(B_241)
      | ~ v1_relat_1(k4_relat_1(A_48))
      | ~ v1_relat_1(A_48) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_3938])).

tff(c_7045,plain,(
    ! [A_48] :
      ( k5_relat_1(k4_relat_1(k1_xboole_0),A_48) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k4_relat_1(A_48))
      | ~ v1_relat_1(A_48)
      | ~ v1_relat_1(k4_relat_1(A_48)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6996,c_3956])).

tff(c_7166,plain,(
    ! [A_321] :
      ( k5_relat_1(k1_xboole_0,A_321) = k1_xboole_0
      | ~ v1_relat_1(A_321)
      | ~ v1_relat_1(k4_relat_1(A_321)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_4059,c_7045])).

tff(c_7240,plain,(
    ! [A_322] :
      ( k5_relat_1(k1_xboole_0,A_322) = k1_xboole_0
      | ~ v1_relat_1(A_322) ) ),
    inference(resolution,[status(thm)],[c_42,c_7166])).

tff(c_7287,plain,(
    ! [A_323] :
      ( k5_relat_1(k1_xboole_0,k4_relat_1(A_323)) = k1_xboole_0
      | ~ v1_relat_1(A_323) ) ),
    inference(resolution,[status(thm)],[c_42,c_7240])).

tff(c_3953,plain,(
    ! [A_242,A_48] :
      ( k4_relat_1(k5_relat_1(A_242,k4_relat_1(A_48))) = k5_relat_1(A_48,k4_relat_1(A_242))
      | ~ v1_relat_1(k4_relat_1(A_48))
      | ~ v1_relat_1(A_242)
      | ~ v1_relat_1(A_48) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_3938])).

tff(c_7305,plain,(
    ! [A_323] :
      ( k5_relat_1(A_323,k4_relat_1(k1_xboole_0)) = k4_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k4_relat_1(A_323))
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_323)
      | ~ v1_relat_1(A_323) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7287,c_3953])).

tff(c_7413,plain,(
    ! [A_324] :
      ( k5_relat_1(A_324,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k4_relat_1(A_324))
      | ~ v1_relat_1(A_324) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_4059,c_4059,c_7305])).

tff(c_7487,plain,(
    ! [A_325] :
      ( k5_relat_1(A_325,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_325) ) ),
    inference(resolution,[status(thm)],[c_42,c_7413])).

tff(c_7520,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_62,c_7487])).

tff(c_7535,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3408,c_7520])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:01:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.84/2.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.84/2.46  
% 6.84/2.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.84/2.46  %$ r1_tarski > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k6_subset_1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k4_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 6.84/2.46  
% 6.84/2.46  %Foreground sorts:
% 6.84/2.46  
% 6.84/2.46  
% 6.84/2.46  %Background operators:
% 6.84/2.46  
% 6.84/2.46  
% 6.84/2.46  %Foreground operators:
% 6.84/2.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.84/2.46  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.84/2.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.84/2.46  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 6.84/2.46  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.84/2.46  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.84/2.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.84/2.46  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.84/2.46  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.84/2.46  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.84/2.46  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.84/2.46  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 6.84/2.46  tff('#skF_1', type, '#skF_1': $i).
% 6.84/2.46  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.84/2.46  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.84/2.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.84/2.46  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.84/2.46  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.84/2.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.84/2.46  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.84/2.46  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.84/2.46  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.84/2.46  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.84/2.46  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 6.84/2.46  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 6.84/2.46  
% 6.84/2.48  tff(f_115, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_relat_1)).
% 6.84/2.48  tff(f_70, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 6.84/2.48  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 6.84/2.48  tff(f_66, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 6.84/2.48  tff(f_42, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 6.84/2.48  tff(f_28, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 6.84/2.48  tff(f_36, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 6.84/2.48  tff(f_60, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 6.84/2.48  tff(f_91, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k4_relat_1(k6_subset_1(A, B)) = k6_subset_1(k4_relat_1(A), k4_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_relat_1)).
% 6.84/2.48  tff(f_105, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k4_relat_1(k5_relat_1(A, B)) = k5_relat_1(k4_relat_1(B), k4_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_relat_1)).
% 6.84/2.48  tff(f_76, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 6.84/2.48  tff(f_38, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 6.84/2.48  tff(f_58, axiom, (![A, B, C]: ((k2_zfmisc_1(k4_xboole_0(A, B), C) = k4_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C))) & (k2_zfmisc_1(C, k4_xboole_0(A, B)) = k4_xboole_0(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_zfmisc_1)).
% 6.84/2.48  tff(f_108, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 6.84/2.48  tff(f_98, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k5_relat_1(A, B)), k1_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_relat_1)).
% 6.84/2.48  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 6.84/2.48  tff(f_34, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.84/2.48  tff(f_84, axiom, (![A]: (v1_relat_1(A) => (k3_xboole_0(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_relat_1)).
% 6.84/2.48  tff(f_80, axiom, (![A]: (v1_relat_1(A) => (k4_relat_1(k4_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k4_relat_1)).
% 6.84/2.48  tff(c_60, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_115])).
% 6.84/2.48  tff(c_106, plain, (k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_60])).
% 6.84/2.48  tff(c_62, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_115])).
% 6.84/2.48  tff(c_42, plain, (![A_45]: (v1_relat_1(k4_relat_1(A_45)) | ~v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.84/2.48  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 6.84/2.48  tff(c_101, plain, (![A_63]: (v1_relat_1(A_63) | ~v1_xboole_0(A_63))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.84/2.48  tff(c_105, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_101])).
% 6.84/2.48  tff(c_18, plain, (![A_9]: (k5_xboole_0(A_9, A_9)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.84/2.48  tff(c_4, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_28])).
% 6.84/2.48  tff(c_172, plain, (![A_75, B_76]: (k5_xboole_0(A_75, k3_xboole_0(A_75, B_76))=k4_xboole_0(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_36])).
% 6.84/2.48  tff(c_184, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_4, c_172])).
% 6.84/2.48  tff(c_187, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_184])).
% 6.84/2.48  tff(c_36, plain, (![A_40, B_41]: (k6_subset_1(A_40, B_41)=k4_xboole_0(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.84/2.48  tff(c_50, plain, (![A_50, B_52]: (k6_subset_1(k4_relat_1(A_50), k4_relat_1(B_52))=k4_relat_1(k6_subset_1(A_50, B_52)) | ~v1_relat_1(B_52) | ~v1_relat_1(A_50))), inference(cnfTransformation, [status(thm)], [f_91])).
% 6.84/2.48  tff(c_500, plain, (![A_107, B_108]: (k4_xboole_0(k4_relat_1(A_107), k4_relat_1(B_108))=k4_relat_1(k4_xboole_0(A_107, B_108)) | ~v1_relat_1(B_108) | ~v1_relat_1(A_107))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_36, c_50])).
% 6.84/2.48  tff(c_507, plain, (![B_108]: (k4_relat_1(k4_xboole_0(B_108, B_108))=k1_xboole_0 | ~v1_relat_1(B_108) | ~v1_relat_1(B_108))), inference(superposition, [status(thm), theory('equality')], [c_500, c_187])).
% 6.84/2.48  tff(c_522, plain, (![B_108]: (k4_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(B_108) | ~v1_relat_1(B_108))), inference(demodulation, [status(thm), theory('equality')], [c_187, c_507])).
% 6.84/2.48  tff(c_526, plain, (![B_109]: (~v1_relat_1(B_109) | ~v1_relat_1(B_109))), inference(splitLeft, [status(thm)], [c_522])).
% 6.84/2.48  tff(c_532, plain, (~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_105, c_526])).
% 6.84/2.48  tff(c_540, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_105, c_532])).
% 6.84/2.48  tff(c_541, plain, (k4_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_522])).
% 6.84/2.48  tff(c_566, plain, (![B_110, A_111]: (k5_relat_1(k4_relat_1(B_110), k4_relat_1(A_111))=k4_relat_1(k5_relat_1(A_111, B_110)) | ~v1_relat_1(B_110) | ~v1_relat_1(A_111))), inference(cnfTransformation, [status(thm)], [f_105])).
% 6.84/2.48  tff(c_44, plain, (![A_46, B_47]: (v1_relat_1(k5_relat_1(A_46, B_47)) | ~v1_relat_1(B_47) | ~v1_relat_1(A_46))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.84/2.48  tff(c_575, plain, (![A_111, B_110]: (v1_relat_1(k4_relat_1(k5_relat_1(A_111, B_110))) | ~v1_relat_1(k4_relat_1(A_111)) | ~v1_relat_1(k4_relat_1(B_110)) | ~v1_relat_1(B_110) | ~v1_relat_1(A_111))), inference(superposition, [status(thm), theory('equality')], [c_566, c_44])).
% 6.84/2.48  tff(c_14, plain, (![A_7]: (k3_xboole_0(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.84/2.48  tff(c_347, plain, (![C_95, A_96, B_97]: (k4_xboole_0(k2_zfmisc_1(C_95, A_96), k2_zfmisc_1(C_95, B_97))=k2_zfmisc_1(C_95, k4_xboole_0(A_96, B_97)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.84/2.48  tff(c_354, plain, (![C_95, B_97]: (k2_zfmisc_1(C_95, k4_xboole_0(B_97, B_97))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_347, c_187])).
% 6.84/2.48  tff(c_363, plain, (![C_95]: (k2_zfmisc_1(C_95, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_187, c_354])).
% 6.84/2.48  tff(c_409, plain, (![A_101, C_102, B_103]: (k4_xboole_0(k2_zfmisc_1(A_101, C_102), k2_zfmisc_1(B_103, C_102))=k2_zfmisc_1(k4_xboole_0(A_101, B_103), C_102))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.84/2.48  tff(c_34, plain, (![C_39, A_37, B_38]: (k4_xboole_0(k2_zfmisc_1(C_39, A_37), k2_zfmisc_1(C_39, B_38))=k2_zfmisc_1(C_39, k4_xboole_0(A_37, B_38)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.84/2.48  tff(c_416, plain, (![B_103, C_102]: (k2_zfmisc_1(k4_xboole_0(B_103, B_103), C_102)=k2_zfmisc_1(B_103, k4_xboole_0(C_102, C_102)))), inference(superposition, [status(thm), theory('equality')], [c_409, c_34])).
% 6.84/2.48  tff(c_439, plain, (![C_102]: (k2_zfmisc_1(k1_xboole_0, C_102)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_363, c_187, c_187, c_416])).
% 6.84/2.48  tff(c_581, plain, (![A_111]: (k5_relat_1(k1_xboole_0, k4_relat_1(A_111))=k4_relat_1(k5_relat_1(A_111, k1_xboole_0)) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_111))), inference(superposition, [status(thm), theory('equality')], [c_541, c_566])).
% 6.84/2.48  tff(c_615, plain, (![A_113]: (k5_relat_1(k1_xboole_0, k4_relat_1(A_113))=k4_relat_1(k5_relat_1(A_113, k1_xboole_0)) | ~v1_relat_1(A_113))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_581])).
% 6.84/2.48  tff(c_58, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_108])).
% 6.84/2.48  tff(c_273, plain, (![A_86, B_87]: (r1_tarski(k1_relat_1(k5_relat_1(A_86, B_87)), k1_relat_1(A_86)) | ~v1_relat_1(B_87) | ~v1_relat_1(A_86))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.84/2.48  tff(c_278, plain, (![B_87]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_87)), k1_xboole_0) | ~v1_relat_1(B_87) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_58, c_273])).
% 6.84/2.48  tff(c_282, plain, (![B_88]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_88)), k1_xboole_0) | ~v1_relat_1(B_88))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_278])).
% 6.84/2.48  tff(c_16, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.84/2.48  tff(c_162, plain, (![B_73, A_74]: (B_73=A_74 | ~r1_tarski(B_73, A_74) | ~r1_tarski(A_74, B_73))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.84/2.48  tff(c_171, plain, (![A_8]: (k1_xboole_0=A_8 | ~r1_tarski(A_8, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_162])).
% 6.84/2.48  tff(c_288, plain, (![B_88]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_88))=k1_xboole_0 | ~v1_relat_1(B_88))), inference(resolution, [status(thm)], [c_282, c_171])).
% 6.84/2.48  tff(c_884, plain, (![A_133]: (k1_relat_1(k4_relat_1(k5_relat_1(A_133, k1_xboole_0)))=k1_xboole_0 | ~v1_relat_1(k4_relat_1(A_133)) | ~v1_relat_1(A_133))), inference(superposition, [status(thm), theory('equality')], [c_615, c_288])).
% 6.84/2.48  tff(c_48, plain, (![A_49]: (k3_xboole_0(A_49, k2_zfmisc_1(k1_relat_1(A_49), k2_relat_1(A_49)))=A_49 | ~v1_relat_1(A_49))), inference(cnfTransformation, [status(thm)], [f_84])).
% 6.84/2.48  tff(c_896, plain, (![A_133]: (k3_xboole_0(k4_relat_1(k5_relat_1(A_133, k1_xboole_0)), k2_zfmisc_1(k1_xboole_0, k2_relat_1(k4_relat_1(k5_relat_1(A_133, k1_xboole_0)))))=k4_relat_1(k5_relat_1(A_133, k1_xboole_0)) | ~v1_relat_1(k4_relat_1(k5_relat_1(A_133, k1_xboole_0))) | ~v1_relat_1(k4_relat_1(A_133)) | ~v1_relat_1(A_133))), inference(superposition, [status(thm), theory('equality')], [c_884, c_48])).
% 6.84/2.48  tff(c_2858, plain, (![A_180]: (k4_relat_1(k5_relat_1(A_180, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(k4_relat_1(k5_relat_1(A_180, k1_xboole_0))) | ~v1_relat_1(k4_relat_1(A_180)) | ~v1_relat_1(A_180))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_439, c_896])).
% 6.84/2.48  tff(c_2866, plain, (![A_111]: (k4_relat_1(k5_relat_1(A_111, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(k4_relat_1(A_111)) | ~v1_relat_1(k4_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_111))), inference(resolution, [status(thm)], [c_575, c_2858])).
% 6.84/2.48  tff(c_2898, plain, (![A_181]: (k4_relat_1(k5_relat_1(A_181, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(k4_relat_1(A_181)) | ~v1_relat_1(A_181))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_105, c_541, c_2866])).
% 6.84/2.48  tff(c_3122, plain, (![A_184]: (k4_relat_1(k5_relat_1(A_184, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(A_184))), inference(resolution, [status(thm)], [c_42, c_2898])).
% 6.84/2.48  tff(c_46, plain, (![A_48]: (k4_relat_1(k4_relat_1(A_48))=A_48 | ~v1_relat_1(A_48))), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.84/2.48  tff(c_590, plain, (![A_48, B_110]: (k4_relat_1(k5_relat_1(k4_relat_1(A_48), B_110))=k5_relat_1(k4_relat_1(B_110), A_48) | ~v1_relat_1(B_110) | ~v1_relat_1(k4_relat_1(A_48)) | ~v1_relat_1(A_48))), inference(superposition, [status(thm), theory('equality')], [c_46, c_566])).
% 6.84/2.48  tff(c_3164, plain, (![A_48]: (k5_relat_1(k4_relat_1(k1_xboole_0), A_48)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(k4_relat_1(A_48)) | ~v1_relat_1(A_48) | ~v1_relat_1(k4_relat_1(A_48)))), inference(superposition, [status(thm), theory('equality')], [c_3122, c_590])).
% 6.84/2.48  tff(c_3288, plain, (![A_185]: (k5_relat_1(k1_xboole_0, A_185)=k1_xboole_0 | ~v1_relat_1(A_185) | ~v1_relat_1(k4_relat_1(A_185)))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_541, c_3164])).
% 6.84/2.48  tff(c_3359, plain, (![A_186]: (k5_relat_1(k1_xboole_0, A_186)=k1_xboole_0 | ~v1_relat_1(A_186))), inference(resolution, [status(thm)], [c_42, c_3288])).
% 6.84/2.48  tff(c_3392, plain, (k5_relat_1(k1_xboole_0, '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_62, c_3359])).
% 6.84/2.48  tff(c_3407, plain, $false, inference(negUnitSimplification, [status(thm)], [c_106, c_3392])).
% 6.84/2.48  tff(c_3408, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_60])).
% 6.84/2.48  tff(c_3498, plain, (![A_201, B_202]: (k5_xboole_0(A_201, k3_xboole_0(A_201, B_202))=k4_xboole_0(A_201, B_202))), inference(cnfTransformation, [status(thm)], [f_36])).
% 6.84/2.48  tff(c_3510, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_4, c_3498])).
% 6.84/2.48  tff(c_3513, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_3510])).
% 6.84/2.48  tff(c_4018, plain, (![A_245, B_246]: (k4_xboole_0(k4_relat_1(A_245), k4_relat_1(B_246))=k4_relat_1(k4_xboole_0(A_245, B_246)) | ~v1_relat_1(B_246) | ~v1_relat_1(A_245))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_36, c_50])).
% 6.84/2.48  tff(c_4025, plain, (![B_246]: (k4_relat_1(k4_xboole_0(B_246, B_246))=k1_xboole_0 | ~v1_relat_1(B_246) | ~v1_relat_1(B_246))), inference(superposition, [status(thm), theory('equality')], [c_4018, c_3513])).
% 6.84/2.48  tff(c_4040, plain, (![B_246]: (k4_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(B_246) | ~v1_relat_1(B_246))), inference(demodulation, [status(thm), theory('equality')], [c_3513, c_4025])).
% 6.84/2.48  tff(c_4044, plain, (![B_247]: (~v1_relat_1(B_247) | ~v1_relat_1(B_247))), inference(splitLeft, [status(thm)], [c_4040])).
% 6.84/2.48  tff(c_4050, plain, (~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_105, c_4044])).
% 6.84/2.48  tff(c_4058, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_105, c_4050])).
% 6.84/2.48  tff(c_4059, plain, (k4_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_4040])).
% 6.84/2.48  tff(c_3938, plain, (![B_241, A_242]: (k5_relat_1(k4_relat_1(B_241), k4_relat_1(A_242))=k4_relat_1(k5_relat_1(A_242, B_241)) | ~v1_relat_1(B_241) | ~v1_relat_1(A_242))), inference(cnfTransformation, [status(thm)], [f_105])).
% 6.84/2.48  tff(c_3947, plain, (![A_242, B_241]: (v1_relat_1(k4_relat_1(k5_relat_1(A_242, B_241))) | ~v1_relat_1(k4_relat_1(A_242)) | ~v1_relat_1(k4_relat_1(B_241)) | ~v1_relat_1(B_241) | ~v1_relat_1(A_242))), inference(superposition, [status(thm), theory('equality')], [c_3938, c_44])).
% 6.84/2.48  tff(c_3674, plain, (![A_218, C_219, B_220]: (k4_xboole_0(k2_zfmisc_1(A_218, C_219), k2_zfmisc_1(B_220, C_219))=k2_zfmisc_1(k4_xboole_0(A_218, B_220), C_219))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.84/2.48  tff(c_3681, plain, (![B_220, C_219]: (k2_zfmisc_1(k4_xboole_0(B_220, B_220), C_219)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3674, c_3513])).
% 6.84/2.48  tff(c_3690, plain, (![C_219]: (k2_zfmisc_1(k1_xboole_0, C_219)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_3513, c_3681])).
% 6.84/2.48  tff(c_54, plain, (![B_58, A_56]: (k5_relat_1(k4_relat_1(B_58), k4_relat_1(A_56))=k4_relat_1(k5_relat_1(A_56, B_58)) | ~v1_relat_1(B_58) | ~v1_relat_1(A_56))), inference(cnfTransformation, [status(thm)], [f_105])).
% 6.84/2.48  tff(c_4069, plain, (![A_56]: (k5_relat_1(k1_xboole_0, k4_relat_1(A_56))=k4_relat_1(k5_relat_1(A_56, k1_xboole_0)) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_56))), inference(superposition, [status(thm), theory('equality')], [c_4059, c_54])).
% 6.84/2.48  tff(c_4166, plain, (![A_262]: (k5_relat_1(k1_xboole_0, k4_relat_1(A_262))=k4_relat_1(k5_relat_1(A_262, k1_xboole_0)) | ~v1_relat_1(A_262))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_4069])).
% 6.84/2.48  tff(c_3585, plain, (![A_209, B_210]: (r1_tarski(k1_relat_1(k5_relat_1(A_209, B_210)), k1_relat_1(A_209)) | ~v1_relat_1(B_210) | ~v1_relat_1(A_209))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.84/2.48  tff(c_3593, plain, (![B_210]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_210)), k1_xboole_0) | ~v1_relat_1(B_210) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_58, c_3585])).
% 6.84/2.48  tff(c_3599, plain, (![B_211]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_211)), k1_xboole_0) | ~v1_relat_1(B_211))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_3593])).
% 6.84/2.48  tff(c_3469, plain, (![B_196, A_197]: (B_196=A_197 | ~r1_tarski(B_196, A_197) | ~r1_tarski(A_197, B_196))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.84/2.48  tff(c_3478, plain, (![A_8]: (k1_xboole_0=A_8 | ~r1_tarski(A_8, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_3469])).
% 6.84/2.48  tff(c_3608, plain, (![B_211]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_211))=k1_xboole_0 | ~v1_relat_1(B_211))), inference(resolution, [status(thm)], [c_3599, c_3478])).
% 6.84/2.48  tff(c_4295, plain, (![A_269]: (k1_relat_1(k4_relat_1(k5_relat_1(A_269, k1_xboole_0)))=k1_xboole_0 | ~v1_relat_1(k4_relat_1(A_269)) | ~v1_relat_1(A_269))), inference(superposition, [status(thm), theory('equality')], [c_4166, c_3608])).
% 6.84/2.48  tff(c_4307, plain, (![A_269]: (k3_xboole_0(k4_relat_1(k5_relat_1(A_269, k1_xboole_0)), k2_zfmisc_1(k1_xboole_0, k2_relat_1(k4_relat_1(k5_relat_1(A_269, k1_xboole_0)))))=k4_relat_1(k5_relat_1(A_269, k1_xboole_0)) | ~v1_relat_1(k4_relat_1(k5_relat_1(A_269, k1_xboole_0))) | ~v1_relat_1(k4_relat_1(A_269)) | ~v1_relat_1(A_269))), inference(superposition, [status(thm), theory('equality')], [c_4295, c_48])).
% 6.84/2.48  tff(c_6835, plain, (![A_316]: (k4_relat_1(k5_relat_1(A_316, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(k4_relat_1(k5_relat_1(A_316, k1_xboole_0))) | ~v1_relat_1(k4_relat_1(A_316)) | ~v1_relat_1(A_316))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_3690, c_4307])).
% 6.84/2.48  tff(c_6853, plain, (![A_242]: (k4_relat_1(k5_relat_1(A_242, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(k4_relat_1(A_242)) | ~v1_relat_1(k4_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_242))), inference(resolution, [status(thm)], [c_3947, c_6835])).
% 6.84/2.48  tff(c_6875, plain, (![A_317]: (k4_relat_1(k5_relat_1(A_317, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(k4_relat_1(A_317)) | ~v1_relat_1(A_317))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_105, c_4059, c_6853])).
% 6.84/2.48  tff(c_6996, plain, (![A_320]: (k4_relat_1(k5_relat_1(A_320, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(A_320))), inference(resolution, [status(thm)], [c_42, c_6875])).
% 6.84/2.48  tff(c_3956, plain, (![A_48, B_241]: (k4_relat_1(k5_relat_1(k4_relat_1(A_48), B_241))=k5_relat_1(k4_relat_1(B_241), A_48) | ~v1_relat_1(B_241) | ~v1_relat_1(k4_relat_1(A_48)) | ~v1_relat_1(A_48))), inference(superposition, [status(thm), theory('equality')], [c_46, c_3938])).
% 6.84/2.48  tff(c_7045, plain, (![A_48]: (k5_relat_1(k4_relat_1(k1_xboole_0), A_48)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(k4_relat_1(A_48)) | ~v1_relat_1(A_48) | ~v1_relat_1(k4_relat_1(A_48)))), inference(superposition, [status(thm), theory('equality')], [c_6996, c_3956])).
% 6.84/2.48  tff(c_7166, plain, (![A_321]: (k5_relat_1(k1_xboole_0, A_321)=k1_xboole_0 | ~v1_relat_1(A_321) | ~v1_relat_1(k4_relat_1(A_321)))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_4059, c_7045])).
% 6.84/2.48  tff(c_7240, plain, (![A_322]: (k5_relat_1(k1_xboole_0, A_322)=k1_xboole_0 | ~v1_relat_1(A_322))), inference(resolution, [status(thm)], [c_42, c_7166])).
% 6.84/2.48  tff(c_7287, plain, (![A_323]: (k5_relat_1(k1_xboole_0, k4_relat_1(A_323))=k1_xboole_0 | ~v1_relat_1(A_323))), inference(resolution, [status(thm)], [c_42, c_7240])).
% 6.84/2.48  tff(c_3953, plain, (![A_242, A_48]: (k4_relat_1(k5_relat_1(A_242, k4_relat_1(A_48)))=k5_relat_1(A_48, k4_relat_1(A_242)) | ~v1_relat_1(k4_relat_1(A_48)) | ~v1_relat_1(A_242) | ~v1_relat_1(A_48))), inference(superposition, [status(thm), theory('equality')], [c_46, c_3938])).
% 6.84/2.48  tff(c_7305, plain, (![A_323]: (k5_relat_1(A_323, k4_relat_1(k1_xboole_0))=k4_relat_1(k1_xboole_0) | ~v1_relat_1(k4_relat_1(A_323)) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_323) | ~v1_relat_1(A_323))), inference(superposition, [status(thm), theory('equality')], [c_7287, c_3953])).
% 6.84/2.48  tff(c_7413, plain, (![A_324]: (k5_relat_1(A_324, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k4_relat_1(A_324)) | ~v1_relat_1(A_324))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_4059, c_4059, c_7305])).
% 6.84/2.48  tff(c_7487, plain, (![A_325]: (k5_relat_1(A_325, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_325))), inference(resolution, [status(thm)], [c_42, c_7413])).
% 6.84/2.48  tff(c_7520, plain, (k5_relat_1('#skF_1', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_62, c_7487])).
% 6.84/2.48  tff(c_7535, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3408, c_7520])).
% 6.84/2.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.84/2.48  
% 6.84/2.48  Inference rules
% 6.84/2.48  ----------------------
% 6.84/2.48  #Ref     : 0
% 6.84/2.48  #Sup     : 1908
% 6.84/2.48  #Fact    : 0
% 6.84/2.48  #Define  : 0
% 6.84/2.48  #Split   : 3
% 6.84/2.48  #Chain   : 0
% 6.84/2.48  #Close   : 0
% 6.84/2.48  
% 6.84/2.48  Ordering : KBO
% 6.84/2.48  
% 6.84/2.48  Simplification rules
% 6.84/2.48  ----------------------
% 6.84/2.48  #Subsume      : 142
% 6.84/2.48  #Demod        : 2098
% 6.84/2.48  #Tautology    : 688
% 6.84/2.48  #SimpNegUnit  : 2
% 6.84/2.48  #BackRed      : 12
% 6.84/2.48  
% 6.84/2.48  #Partial instantiations: 0
% 6.84/2.48  #Strategies tried      : 1
% 6.84/2.48  
% 6.84/2.48  Timing (in seconds)
% 6.84/2.48  ----------------------
% 6.84/2.49  Preprocessing        : 0.33
% 6.84/2.49  Parsing              : 0.18
% 6.84/2.49  CNF conversion       : 0.02
% 6.84/2.49  Main loop            : 1.36
% 6.84/2.49  Inferencing          : 0.44
% 6.84/2.49  Reduction            : 0.50
% 6.84/2.49  Demodulation         : 0.39
% 6.84/2.49  BG Simplification    : 0.07
% 6.84/2.49  Subsumption          : 0.27
% 6.84/2.49  Abstraction          : 0.08
% 6.84/2.49  MUC search           : 0.00
% 6.84/2.49  Cooper               : 0.00
% 6.84/2.49  Total                : 1.74
% 6.84/2.49  Index Insertion      : 0.00
% 6.84/2.49  Index Deletion       : 0.00
% 6.84/2.49  Index Matching       : 0.00
% 6.84/2.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
