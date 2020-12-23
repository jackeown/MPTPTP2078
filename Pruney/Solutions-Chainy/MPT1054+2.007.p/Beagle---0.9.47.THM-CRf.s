%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:12 EST 2020

% Result     : Theorem 2.63s
% Output     : CNFRefutation 2.88s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 174 expanded)
%              Number of leaves         :   47 (  81 expanded)
%              Depth                    :   11
%              Number of atoms          :  114 ( 202 expanded)
%              Number of equality atoms :   48 ( 109 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_103,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k8_relset_1(A,A,k6_partfun1(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_2)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_98,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_60,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_78,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_88,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_70,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v4_relat_1(k6_relat_1(A),A)
      & v5_relat_1(k6_relat_1(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc24_relat_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ! [C] :
          ( ( v1_relat_1(C)
            & v4_relat_1(C,A) )
         => v4_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t217_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_33,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_90,axiom,(
    ! [A] : k2_funct_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k10_relat_1(B,A) = k9_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).

tff(f_96,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_94,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(c_54,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_167,plain,(
    ! [A_53,B_54] :
      ( r1_tarski(A_53,B_54)
      | ~ m1_subset_1(A_53,k1_zfmisc_1(B_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_175,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_167])).

tff(c_50,plain,(
    ! [A_36] : k6_relat_1(A_36) = k6_partfun1(A_36) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_22,plain,(
    ! [A_20] : k2_relat_1(k6_relat_1(A_20)) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_66,plain,(
    ! [A_20] : k2_relat_1(k6_partfun1(A_20)) = A_20 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_22])).

tff(c_36,plain,(
    ! [A_25] : v1_relat_1(k6_relat_1(A_25)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_59,plain,(
    ! [A_25] : v1_relat_1(k6_partfun1(A_25)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_36])).

tff(c_24,plain,(
    ! [A_21,B_22] :
      ( k5_relat_1(k6_relat_1(A_21),B_22) = k7_relat_1(B_22,A_21)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_257,plain,(
    ! [A_66,B_67] :
      ( k5_relat_1(k6_partfun1(A_66),B_67) = k7_relat_1(B_67,A_66)
      | ~ v1_relat_1(B_67) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_24])).

tff(c_42,plain,(
    ! [B_29,A_28] : k5_relat_1(k6_relat_1(B_29),k6_relat_1(A_28)) = k6_relat_1(k3_xboole_0(A_28,B_29)) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_57,plain,(
    ! [B_29,A_28] : k5_relat_1(k6_partfun1(B_29),k6_partfun1(A_28)) = k6_partfun1(k3_xboole_0(A_28,B_29)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_50,c_50,c_42])).

tff(c_264,plain,(
    ! [A_28,A_66] :
      ( k7_relat_1(k6_partfun1(A_28),A_66) = k6_partfun1(k3_xboole_0(A_28,A_66))
      | ~ v1_relat_1(k6_partfun1(A_28)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_257,c_57])).

tff(c_273,plain,(
    ! [A_28,A_66] : k7_relat_1(k6_partfun1(A_28),A_66) = k6_partfun1(k3_xboole_0(A_28,A_66)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_264])).

tff(c_28,plain,(
    ! [A_23] : v4_relat_1(k6_relat_1(A_23),A_23) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_63,plain,(
    ! [A_23] : v4_relat_1(k6_partfun1(A_23),A_23) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_28])).

tff(c_394,plain,(
    ! [C_79,B_80,A_81] :
      ( v4_relat_1(C_79,B_80)
      | ~ v4_relat_1(C_79,A_81)
      | ~ v1_relat_1(C_79)
      | ~ r1_tarski(A_81,B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_396,plain,(
    ! [A_23,B_80] :
      ( v4_relat_1(k6_partfun1(A_23),B_80)
      | ~ v1_relat_1(k6_partfun1(A_23))
      | ~ r1_tarski(A_23,B_80) ) ),
    inference(resolution,[status(thm)],[c_63,c_394])).

tff(c_400,plain,(
    ! [A_82,B_83] :
      ( v4_relat_1(k6_partfun1(A_82),B_83)
      | ~ r1_tarski(A_82,B_83) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_396])).

tff(c_16,plain,(
    ! [B_15,A_14] :
      ( k7_relat_1(B_15,A_14) = B_15
      | ~ v4_relat_1(B_15,A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_405,plain,(
    ! [A_82,B_83] :
      ( k7_relat_1(k6_partfun1(A_82),B_83) = k6_partfun1(A_82)
      | ~ v1_relat_1(k6_partfun1(A_82))
      | ~ r1_tarski(A_82,B_83) ) ),
    inference(resolution,[status(thm)],[c_400,c_16])).

tff(c_412,plain,(
    ! [A_84,B_85] :
      ( k6_partfun1(k3_xboole_0(A_84,B_85)) = k6_partfun1(A_84)
      | ~ r1_tarski(A_84,B_85) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_273,c_405])).

tff(c_451,plain,(
    ! [A_84,B_85] :
      ( k3_xboole_0(A_84,B_85) = k2_relat_1(k6_partfun1(A_84))
      | ~ r1_tarski(A_84,B_85) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_412,c_66])).

tff(c_486,plain,(
    ! [A_86,B_87] :
      ( k3_xboole_0(A_86,B_87) = A_86
      | ~ r1_tarski(A_86,B_87) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_451])).

tff(c_494,plain,(
    k3_xboole_0('#skF_2','#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_175,c_486])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_tarski(B_2,A_1) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_143,plain,(
    ! [A_49,B_50] : k1_setfam_1(k2_tarski(A_49,B_50)) = k3_xboole_0(A_49,B_50) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_191,plain,(
    ! [A_60,B_61] : k1_setfam_1(k2_tarski(A_60,B_61)) = k3_xboole_0(B_61,A_60) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_143])).

tff(c_8,plain,(
    ! [A_8,B_9] : k1_setfam_1(k2_tarski(A_8,B_9)) = k3_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_197,plain,(
    ! [B_61,A_60] : k3_xboole_0(B_61,A_60) = k3_xboole_0(A_60,B_61) ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_8])).

tff(c_501,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_494,c_197])).

tff(c_34,plain,(
    ! [A_24] : v1_funct_1(k6_relat_1(A_24)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_60,plain,(
    ! [A_24] : v1_funct_1(k6_partfun1(A_24)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_34])).

tff(c_38,plain,(
    ! [A_25] : v2_funct_1(k6_relat_1(A_25)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_58,plain,(
    ! [A_25] : v2_funct_1(k6_partfun1(A_25)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_38])).

tff(c_277,plain,(
    ! [A_68,A_69] : k7_relat_1(k6_partfun1(A_68),A_69) = k6_partfun1(k3_xboole_0(A_68,A_69)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_264])).

tff(c_14,plain,(
    ! [B_13,A_12] :
      ( k2_relat_1(k7_relat_1(B_13,A_12)) = k9_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_283,plain,(
    ! [A_68,A_69] :
      ( k2_relat_1(k6_partfun1(k3_xboole_0(A_68,A_69))) = k9_relat_1(k6_partfun1(A_68),A_69)
      | ~ v1_relat_1(k6_partfun1(A_68)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_277,c_14])).

tff(c_289,plain,(
    ! [A_68,A_69] : k9_relat_1(k6_partfun1(A_68),A_69) = k3_xboole_0(A_68,A_69) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_66,c_283])).

tff(c_44,plain,(
    ! [A_30] : k2_funct_1(k6_relat_1(A_30)) = k6_relat_1(A_30) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_56,plain,(
    ! [A_30] : k2_funct_1(k6_partfun1(A_30)) = k6_partfun1(A_30) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_50,c_44])).

tff(c_524,plain,(
    ! [B_88,A_89] :
      ( k9_relat_1(k2_funct_1(B_88),A_89) = k10_relat_1(B_88,A_89)
      | ~ v2_funct_1(B_88)
      | ~ v1_funct_1(B_88)
      | ~ v1_relat_1(B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_533,plain,(
    ! [A_30,A_89] :
      ( k9_relat_1(k6_partfun1(A_30),A_89) = k10_relat_1(k6_partfun1(A_30),A_89)
      | ~ v2_funct_1(k6_partfun1(A_30))
      | ~ v1_funct_1(k6_partfun1(A_30))
      | ~ v1_relat_1(k6_partfun1(A_30)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_524])).

tff(c_537,plain,(
    ! [A_30,A_89] : k10_relat_1(k6_partfun1(A_30),A_89) = k3_xboole_0(A_30,A_89) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_60,c_58,c_289,c_533])).

tff(c_48,plain,(
    ! [A_35] : m1_subset_1(k6_relat_1(A_35),k1_zfmisc_1(k2_zfmisc_1(A_35,A_35))) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_55,plain,(
    ! [A_35] : m1_subset_1(k6_partfun1(A_35),k1_zfmisc_1(k2_zfmisc_1(A_35,A_35))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48])).

tff(c_611,plain,(
    ! [A_95,B_96,C_97,D_98] :
      ( k8_relset_1(A_95,B_96,C_97,D_98) = k10_relat_1(C_97,D_98)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_616,plain,(
    ! [A_35,D_98] : k8_relset_1(A_35,A_35,k6_partfun1(A_35),D_98) = k10_relat_1(k6_partfun1(A_35),D_98) ),
    inference(resolution,[status(thm)],[c_55,c_611])).

tff(c_619,plain,(
    ! [A_35,D_98] : k8_relset_1(A_35,A_35,k6_partfun1(A_35),D_98) = k3_xboole_0(A_35,D_98) ),
    inference(demodulation,[status(thm),theory(equality)],[c_537,c_616])).

tff(c_52,plain,(
    k8_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_620,plain,(
    k3_xboole_0('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_619,c_52])).

tff(c_623,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_501,c_620])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:21:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.63/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.63/1.37  
% 2.63/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.63/1.38  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.63/1.38  
% 2.63/1.38  %Foreground sorts:
% 2.63/1.38  
% 2.63/1.38  
% 2.63/1.38  %Background operators:
% 2.63/1.38  
% 2.63/1.38  
% 2.63/1.38  %Foreground operators:
% 2.63/1.38  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.63/1.38  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.63/1.38  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.63/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.63/1.38  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.63/1.38  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.63/1.38  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.63/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.63/1.38  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.63/1.38  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.63/1.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.63/1.38  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.63/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.63/1.38  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.63/1.38  tff('#skF_1', type, '#skF_1': $i).
% 2.63/1.38  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.63/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.63/1.38  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.63/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.63/1.38  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.63/1.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.63/1.38  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.63/1.38  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.63/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.63/1.38  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.63/1.38  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.63/1.38  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.63/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.63/1.38  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.63/1.38  
% 2.88/1.40  tff(f_103, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k8_relset_1(A, A, k6_partfun1(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t171_funct_2)).
% 2.88/1.40  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.88/1.40  tff(f_98, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.88/1.40  tff(f_60, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 2.88/1.40  tff(f_78, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 2.88/1.40  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 2.88/1.40  tff(f_88, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 2.88/1.40  tff(f_70, axiom, (![A]: ((v1_relat_1(k6_relat_1(A)) & v4_relat_1(k6_relat_1(A), A)) & v5_relat_1(k6_relat_1(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc24_relat_1)).
% 2.88/1.40  tff(f_56, axiom, (![A, B]: (r1_tarski(A, B) => (![C]: ((v1_relat_1(C) & v4_relat_1(C, A)) => v4_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t217_relat_1)).
% 2.88/1.40  tff(f_47, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 2.88/1.40  tff(f_27, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.88/1.40  tff(f_33, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.88/1.40  tff(f_74, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.88/1.40  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 2.88/1.40  tff(f_90, axiom, (![A]: (k2_funct_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_funct_1)).
% 2.88/1.40  tff(f_86, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k10_relat_1(B, A) = k9_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t155_funct_1)).
% 2.88/1.40  tff(f_96, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 2.88/1.40  tff(f_94, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.88/1.40  tff(c_54, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.88/1.40  tff(c_167, plain, (![A_53, B_54]: (r1_tarski(A_53, B_54) | ~m1_subset_1(A_53, k1_zfmisc_1(B_54)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.88/1.40  tff(c_175, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_54, c_167])).
% 2.88/1.40  tff(c_50, plain, (![A_36]: (k6_relat_1(A_36)=k6_partfun1(A_36))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.88/1.40  tff(c_22, plain, (![A_20]: (k2_relat_1(k6_relat_1(A_20))=A_20)), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.88/1.40  tff(c_66, plain, (![A_20]: (k2_relat_1(k6_partfun1(A_20))=A_20)), inference(demodulation, [status(thm), theory('equality')], [c_50, c_22])).
% 2.88/1.40  tff(c_36, plain, (![A_25]: (v1_relat_1(k6_relat_1(A_25)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.88/1.40  tff(c_59, plain, (![A_25]: (v1_relat_1(k6_partfun1(A_25)))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_36])).
% 2.88/1.40  tff(c_24, plain, (![A_21, B_22]: (k5_relat_1(k6_relat_1(A_21), B_22)=k7_relat_1(B_22, A_21) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.88/1.40  tff(c_257, plain, (![A_66, B_67]: (k5_relat_1(k6_partfun1(A_66), B_67)=k7_relat_1(B_67, A_66) | ~v1_relat_1(B_67))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_24])).
% 2.88/1.40  tff(c_42, plain, (![B_29, A_28]: (k5_relat_1(k6_relat_1(B_29), k6_relat_1(A_28))=k6_relat_1(k3_xboole_0(A_28, B_29)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.88/1.40  tff(c_57, plain, (![B_29, A_28]: (k5_relat_1(k6_partfun1(B_29), k6_partfun1(A_28))=k6_partfun1(k3_xboole_0(A_28, B_29)))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_50, c_50, c_42])).
% 2.88/1.40  tff(c_264, plain, (![A_28, A_66]: (k7_relat_1(k6_partfun1(A_28), A_66)=k6_partfun1(k3_xboole_0(A_28, A_66)) | ~v1_relat_1(k6_partfun1(A_28)))), inference(superposition, [status(thm), theory('equality')], [c_257, c_57])).
% 2.88/1.40  tff(c_273, plain, (![A_28, A_66]: (k7_relat_1(k6_partfun1(A_28), A_66)=k6_partfun1(k3_xboole_0(A_28, A_66)))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_264])).
% 2.88/1.40  tff(c_28, plain, (![A_23]: (v4_relat_1(k6_relat_1(A_23), A_23))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.88/1.40  tff(c_63, plain, (![A_23]: (v4_relat_1(k6_partfun1(A_23), A_23))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_28])).
% 2.88/1.40  tff(c_394, plain, (![C_79, B_80, A_81]: (v4_relat_1(C_79, B_80) | ~v4_relat_1(C_79, A_81) | ~v1_relat_1(C_79) | ~r1_tarski(A_81, B_80))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.88/1.40  tff(c_396, plain, (![A_23, B_80]: (v4_relat_1(k6_partfun1(A_23), B_80) | ~v1_relat_1(k6_partfun1(A_23)) | ~r1_tarski(A_23, B_80))), inference(resolution, [status(thm)], [c_63, c_394])).
% 2.88/1.40  tff(c_400, plain, (![A_82, B_83]: (v4_relat_1(k6_partfun1(A_82), B_83) | ~r1_tarski(A_82, B_83))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_396])).
% 2.88/1.40  tff(c_16, plain, (![B_15, A_14]: (k7_relat_1(B_15, A_14)=B_15 | ~v4_relat_1(B_15, A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.88/1.40  tff(c_405, plain, (![A_82, B_83]: (k7_relat_1(k6_partfun1(A_82), B_83)=k6_partfun1(A_82) | ~v1_relat_1(k6_partfun1(A_82)) | ~r1_tarski(A_82, B_83))), inference(resolution, [status(thm)], [c_400, c_16])).
% 2.88/1.40  tff(c_412, plain, (![A_84, B_85]: (k6_partfun1(k3_xboole_0(A_84, B_85))=k6_partfun1(A_84) | ~r1_tarski(A_84, B_85))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_273, c_405])).
% 2.88/1.40  tff(c_451, plain, (![A_84, B_85]: (k3_xboole_0(A_84, B_85)=k2_relat_1(k6_partfun1(A_84)) | ~r1_tarski(A_84, B_85))), inference(superposition, [status(thm), theory('equality')], [c_412, c_66])).
% 2.88/1.40  tff(c_486, plain, (![A_86, B_87]: (k3_xboole_0(A_86, B_87)=A_86 | ~r1_tarski(A_86, B_87))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_451])).
% 2.88/1.40  tff(c_494, plain, (k3_xboole_0('#skF_2', '#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_175, c_486])).
% 2.88/1.40  tff(c_2, plain, (![B_2, A_1]: (k2_tarski(B_2, A_1)=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.88/1.40  tff(c_143, plain, (![A_49, B_50]: (k1_setfam_1(k2_tarski(A_49, B_50))=k3_xboole_0(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.88/1.40  tff(c_191, plain, (![A_60, B_61]: (k1_setfam_1(k2_tarski(A_60, B_61))=k3_xboole_0(B_61, A_60))), inference(superposition, [status(thm), theory('equality')], [c_2, c_143])).
% 2.88/1.40  tff(c_8, plain, (![A_8, B_9]: (k1_setfam_1(k2_tarski(A_8, B_9))=k3_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.88/1.40  tff(c_197, plain, (![B_61, A_60]: (k3_xboole_0(B_61, A_60)=k3_xboole_0(A_60, B_61))), inference(superposition, [status(thm), theory('equality')], [c_191, c_8])).
% 2.88/1.40  tff(c_501, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_494, c_197])).
% 2.88/1.40  tff(c_34, plain, (![A_24]: (v1_funct_1(k6_relat_1(A_24)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.88/1.40  tff(c_60, plain, (![A_24]: (v1_funct_1(k6_partfun1(A_24)))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_34])).
% 2.88/1.40  tff(c_38, plain, (![A_25]: (v2_funct_1(k6_relat_1(A_25)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.88/1.40  tff(c_58, plain, (![A_25]: (v2_funct_1(k6_partfun1(A_25)))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_38])).
% 2.88/1.40  tff(c_277, plain, (![A_68, A_69]: (k7_relat_1(k6_partfun1(A_68), A_69)=k6_partfun1(k3_xboole_0(A_68, A_69)))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_264])).
% 2.88/1.40  tff(c_14, plain, (![B_13, A_12]: (k2_relat_1(k7_relat_1(B_13, A_12))=k9_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.88/1.40  tff(c_283, plain, (![A_68, A_69]: (k2_relat_1(k6_partfun1(k3_xboole_0(A_68, A_69)))=k9_relat_1(k6_partfun1(A_68), A_69) | ~v1_relat_1(k6_partfun1(A_68)))), inference(superposition, [status(thm), theory('equality')], [c_277, c_14])).
% 2.88/1.40  tff(c_289, plain, (![A_68, A_69]: (k9_relat_1(k6_partfun1(A_68), A_69)=k3_xboole_0(A_68, A_69))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_66, c_283])).
% 2.88/1.40  tff(c_44, plain, (![A_30]: (k2_funct_1(k6_relat_1(A_30))=k6_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.88/1.40  tff(c_56, plain, (![A_30]: (k2_funct_1(k6_partfun1(A_30))=k6_partfun1(A_30))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_50, c_44])).
% 2.88/1.40  tff(c_524, plain, (![B_88, A_89]: (k9_relat_1(k2_funct_1(B_88), A_89)=k10_relat_1(B_88, A_89) | ~v2_funct_1(B_88) | ~v1_funct_1(B_88) | ~v1_relat_1(B_88))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.88/1.40  tff(c_533, plain, (![A_30, A_89]: (k9_relat_1(k6_partfun1(A_30), A_89)=k10_relat_1(k6_partfun1(A_30), A_89) | ~v2_funct_1(k6_partfun1(A_30)) | ~v1_funct_1(k6_partfun1(A_30)) | ~v1_relat_1(k6_partfun1(A_30)))), inference(superposition, [status(thm), theory('equality')], [c_56, c_524])).
% 2.88/1.40  tff(c_537, plain, (![A_30, A_89]: (k10_relat_1(k6_partfun1(A_30), A_89)=k3_xboole_0(A_30, A_89))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_60, c_58, c_289, c_533])).
% 2.88/1.40  tff(c_48, plain, (![A_35]: (m1_subset_1(k6_relat_1(A_35), k1_zfmisc_1(k2_zfmisc_1(A_35, A_35))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.88/1.40  tff(c_55, plain, (![A_35]: (m1_subset_1(k6_partfun1(A_35), k1_zfmisc_1(k2_zfmisc_1(A_35, A_35))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48])).
% 2.88/1.40  tff(c_611, plain, (![A_95, B_96, C_97, D_98]: (k8_relset_1(A_95, B_96, C_97, D_98)=k10_relat_1(C_97, D_98) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.88/1.40  tff(c_616, plain, (![A_35, D_98]: (k8_relset_1(A_35, A_35, k6_partfun1(A_35), D_98)=k10_relat_1(k6_partfun1(A_35), D_98))), inference(resolution, [status(thm)], [c_55, c_611])).
% 2.88/1.40  tff(c_619, plain, (![A_35, D_98]: (k8_relset_1(A_35, A_35, k6_partfun1(A_35), D_98)=k3_xboole_0(A_35, D_98))), inference(demodulation, [status(thm), theory('equality')], [c_537, c_616])).
% 2.88/1.40  tff(c_52, plain, (k8_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.88/1.40  tff(c_620, plain, (k3_xboole_0('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_619, c_52])).
% 2.88/1.40  tff(c_623, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_501, c_620])).
% 2.88/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.88/1.40  
% 2.88/1.40  Inference rules
% 2.88/1.40  ----------------------
% 2.88/1.40  #Ref     : 0
% 2.88/1.40  #Sup     : 131
% 2.88/1.40  #Fact    : 0
% 2.88/1.40  #Define  : 0
% 2.88/1.40  #Split   : 1
% 2.88/1.40  #Chain   : 0
% 2.88/1.40  #Close   : 0
% 2.88/1.40  
% 2.88/1.40  Ordering : KBO
% 2.88/1.40  
% 2.88/1.40  Simplification rules
% 2.88/1.40  ----------------------
% 2.88/1.40  #Subsume      : 4
% 2.88/1.40  #Demod        : 83
% 2.88/1.40  #Tautology    : 88
% 2.88/1.40  #SimpNegUnit  : 0
% 2.88/1.40  #BackRed      : 1
% 2.88/1.40  
% 2.88/1.40  #Partial instantiations: 0
% 2.88/1.40  #Strategies tried      : 1
% 2.88/1.40  
% 2.88/1.40  Timing (in seconds)
% 2.88/1.40  ----------------------
% 2.88/1.41  Preprocessing        : 0.34
% 2.88/1.41  Parsing              : 0.18
% 2.88/1.41  CNF conversion       : 0.02
% 2.88/1.41  Main loop            : 0.29
% 2.88/1.41  Inferencing          : 0.10
% 2.88/1.41  Reduction            : 0.11
% 2.88/1.41  Demodulation         : 0.09
% 2.88/1.41  BG Simplification    : 0.02
% 2.88/1.41  Subsumption          : 0.04
% 2.88/1.41  Abstraction          : 0.02
% 2.88/1.41  MUC search           : 0.00
% 2.88/1.41  Cooper               : 0.00
% 2.88/1.41  Total                : 0.68
% 2.88/1.41  Index Insertion      : 0.00
% 2.88/1.41  Index Deletion       : 0.00
% 2.88/1.41  Index Matching       : 0.00
% 2.88/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
