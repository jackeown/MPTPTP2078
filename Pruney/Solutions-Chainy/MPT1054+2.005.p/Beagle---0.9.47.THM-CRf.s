%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:12 EST 2020

% Result     : Theorem 2.61s
% Output     : CNFRefutation 2.61s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 177 expanded)
%              Number of leaves         :   46 (  81 expanded)
%              Depth                    :   14
%              Number of atoms          :  123 ( 217 expanded)
%              Number of equality atoms :   50 ( 110 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

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

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

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

tff(f_98,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_94,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_105,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k8_relset_1(A,A,k6_partfun1(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_2)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_100,axiom,(
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

tff(f_90,axiom,(
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

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( ( r1_tarski(A,k1_relat_1(B))
          & v2_funct_1(B) )
       => k10_relat_1(B,k9_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).

tff(c_48,plain,(
    ! [A_34] : m1_subset_1(k6_partfun1(A_34),k1_zfmisc_1(k2_zfmisc_1(A_34,A_34))) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_421,plain,(
    ! [A_83,B_84,C_85,D_86] :
      ( k8_relset_1(A_83,B_84,C_85,D_86) = k10_relat_1(C_85,D_86)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_428,plain,(
    ! [A_34,D_86] : k8_relset_1(A_34,A_34,k6_partfun1(A_34),D_86) = k10_relat_1(k6_partfun1(A_34),D_86) ),
    inference(resolution,[status(thm)],[c_48,c_421])).

tff(c_52,plain,(
    k8_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_459,plain,(
    k10_relat_1(k6_partfun1('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_428,c_52])).

tff(c_54,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_134,plain,(
    ! [A_50,B_51] :
      ( r1_tarski(A_50,B_51)
      | ~ m1_subset_1(A_50,k1_zfmisc_1(B_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_146,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_134])).

tff(c_50,plain,(
    ! [A_35] : k6_relat_1(A_35) = k6_partfun1(A_35) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_22,plain,(
    ! [A_20] : k2_relat_1(k6_relat_1(A_20)) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_64,plain,(
    ! [A_20] : k2_relat_1(k6_partfun1(A_20)) = A_20 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_22])).

tff(c_36,plain,(
    ! [A_25] : v1_relat_1(k6_relat_1(A_25)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_57,plain,(
    ! [A_25] : v1_relat_1(k6_partfun1(A_25)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_36])).

tff(c_24,plain,(
    ! [A_21,B_22] :
      ( k5_relat_1(k6_relat_1(A_21),B_22) = k7_relat_1(B_22,A_21)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_304,plain,(
    ! [A_77,B_78] :
      ( k5_relat_1(k6_partfun1(A_77),B_78) = k7_relat_1(B_78,A_77)
      | ~ v1_relat_1(B_78) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_24])).

tff(c_42,plain,(
    ! [B_29,A_28] : k5_relat_1(k6_relat_1(B_29),k6_relat_1(A_28)) = k6_relat_1(k3_xboole_0(A_28,B_29)) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_55,plain,(
    ! [B_29,A_28] : k5_relat_1(k6_partfun1(B_29),k6_partfun1(A_28)) = k6_partfun1(k3_xboole_0(A_28,B_29)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_50,c_50,c_42])).

tff(c_311,plain,(
    ! [A_28,A_77] :
      ( k7_relat_1(k6_partfun1(A_28),A_77) = k6_partfun1(k3_xboole_0(A_28,A_77))
      | ~ v1_relat_1(k6_partfun1(A_28)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_304,c_55])).

tff(c_320,plain,(
    ! [A_28,A_77] : k7_relat_1(k6_partfun1(A_28),A_77) = k6_partfun1(k3_xboole_0(A_28,A_77)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_311])).

tff(c_28,plain,(
    ! [A_23] : v4_relat_1(k6_relat_1(A_23),A_23) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_61,plain,(
    ! [A_23] : v4_relat_1(k6_partfun1(A_23),A_23) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_28])).

tff(c_286,plain,(
    ! [C_72,B_73,A_74] :
      ( v4_relat_1(C_72,B_73)
      | ~ v4_relat_1(C_72,A_74)
      | ~ v1_relat_1(C_72)
      | ~ r1_tarski(A_74,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_288,plain,(
    ! [A_23,B_73] :
      ( v4_relat_1(k6_partfun1(A_23),B_73)
      | ~ v1_relat_1(k6_partfun1(A_23))
      | ~ r1_tarski(A_23,B_73) ) ),
    inference(resolution,[status(thm)],[c_61,c_286])).

tff(c_292,plain,(
    ! [A_75,B_76] :
      ( v4_relat_1(k6_partfun1(A_75),B_76)
      | ~ r1_tarski(A_75,B_76) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_288])).

tff(c_16,plain,(
    ! [B_15,A_14] :
      ( k7_relat_1(B_15,A_14) = B_15
      | ~ v4_relat_1(B_15,A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_297,plain,(
    ! [A_75,B_76] :
      ( k7_relat_1(k6_partfun1(A_75),B_76) = k6_partfun1(A_75)
      | ~ v1_relat_1(k6_partfun1(A_75))
      | ~ r1_tarski(A_75,B_76) ) ),
    inference(resolution,[status(thm)],[c_292,c_16])).

tff(c_303,plain,(
    ! [A_75,B_76] :
      ( k7_relat_1(k6_partfun1(A_75),B_76) = k6_partfun1(A_75)
      | ~ r1_tarski(A_75,B_76) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_297])).

tff(c_470,plain,(
    ! [A_93,B_94] :
      ( k6_partfun1(k3_xboole_0(A_93,B_94)) = k6_partfun1(A_93)
      | ~ r1_tarski(A_93,B_94) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_320,c_303])).

tff(c_515,plain,(
    ! [A_93,B_94] :
      ( k3_xboole_0(A_93,B_94) = k2_relat_1(k6_partfun1(A_93))
      | ~ r1_tarski(A_93,B_94) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_470,c_64])).

tff(c_554,plain,(
    ! [A_95,B_96] :
      ( k3_xboole_0(A_95,B_96) = A_95
      | ~ r1_tarski(A_95,B_96) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_515])).

tff(c_562,plain,(
    k3_xboole_0('#skF_2','#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_146,c_554])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_tarski(B_2,A_1) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_157,plain,(
    ! [A_55,B_56] : k1_setfam_1(k2_tarski(A_55,B_56)) = k3_xboole_0(A_55,B_56) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_181,plain,(
    ! [B_59,A_60] : k1_setfam_1(k2_tarski(B_59,A_60)) = k3_xboole_0(A_60,B_59) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_157])).

tff(c_8,plain,(
    ! [A_8,B_9] : k1_setfam_1(k2_tarski(A_8,B_9)) = k3_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_187,plain,(
    ! [B_59,A_60] : k3_xboole_0(B_59,A_60) = k3_xboole_0(A_60,B_59) ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_8])).

tff(c_569,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_562,c_187])).

tff(c_324,plain,(
    ! [A_79,A_80] : k7_relat_1(k6_partfun1(A_79),A_80) = k6_partfun1(k3_xboole_0(A_79,A_80)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_311])).

tff(c_14,plain,(
    ! [B_13,A_12] :
      ( k2_relat_1(k7_relat_1(B_13,A_12)) = k9_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_334,plain,(
    ! [A_79,A_80] :
      ( k2_relat_1(k6_partfun1(k3_xboole_0(A_79,A_80))) = k9_relat_1(k6_partfun1(A_79),A_80)
      | ~ v1_relat_1(k6_partfun1(A_79)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_324,c_14])).

tff(c_343,plain,(
    ! [A_79,A_80] : k9_relat_1(k6_partfun1(A_79),A_80) = k3_xboole_0(A_79,A_80) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_64,c_334])).

tff(c_34,plain,(
    ! [A_24] : v1_funct_1(k6_relat_1(A_24)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_58,plain,(
    ! [A_24] : v1_funct_1(k6_partfun1(A_24)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_34])).

tff(c_38,plain,(
    ! [A_25] : v2_funct_1(k6_relat_1(A_25)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_56,plain,(
    ! [A_25] : v2_funct_1(k6_partfun1(A_25)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_38])).

tff(c_20,plain,(
    ! [A_20] : k1_relat_1(k6_relat_1(A_20)) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_65,plain,(
    ! [A_20] : k1_relat_1(k6_partfun1(A_20)) = A_20 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_20])).

tff(c_432,plain,(
    ! [B_87,A_88] :
      ( k10_relat_1(B_87,k9_relat_1(B_87,A_88)) = A_88
      | ~ v2_funct_1(B_87)
      | ~ r1_tarski(A_88,k1_relat_1(B_87))
      | ~ v1_funct_1(B_87)
      | ~ v1_relat_1(B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_434,plain,(
    ! [A_20,A_88] :
      ( k10_relat_1(k6_partfun1(A_20),k9_relat_1(k6_partfun1(A_20),A_88)) = A_88
      | ~ v2_funct_1(k6_partfun1(A_20))
      | ~ r1_tarski(A_88,A_20)
      | ~ v1_funct_1(k6_partfun1(A_20))
      | ~ v1_relat_1(k6_partfun1(A_20)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_432])).

tff(c_436,plain,(
    ! [A_20,A_88] :
      ( k10_relat_1(k6_partfun1(A_20),k9_relat_1(k6_partfun1(A_20),A_88)) = A_88
      | ~ r1_tarski(A_88,A_20) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_58,c_56,c_434])).

tff(c_596,plain,(
    ! [A_97,A_98] :
      ( k10_relat_1(k6_partfun1(A_97),k3_xboole_0(A_97,A_98)) = A_98
      | ~ r1_tarski(A_98,A_97) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_343,c_436])).

tff(c_605,plain,
    ( k10_relat_1(k6_partfun1('#skF_1'),'#skF_2') = '#skF_2'
    | ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_569,c_596])).

tff(c_624,plain,(
    k10_relat_1(k6_partfun1('#skF_1'),'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_605])).

tff(c_626,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_459,c_624])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:02:20 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.61/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.61/1.36  
% 2.61/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.61/1.36  %$ v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.61/1.36  
% 2.61/1.36  %Foreground sorts:
% 2.61/1.36  
% 2.61/1.36  
% 2.61/1.36  %Background operators:
% 2.61/1.36  
% 2.61/1.36  
% 2.61/1.36  %Foreground operators:
% 2.61/1.36  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.61/1.36  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.61/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.61/1.36  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.61/1.36  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.61/1.36  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.61/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.61/1.36  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.61/1.36  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.61/1.36  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.61/1.36  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.61/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.61/1.36  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.61/1.36  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.61/1.36  tff('#skF_1', type, '#skF_1': $i).
% 2.61/1.36  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.61/1.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.61/1.36  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.61/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.61/1.36  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.61/1.36  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.61/1.36  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.61/1.36  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.61/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.61/1.36  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.61/1.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.61/1.36  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.61/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.61/1.36  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.61/1.36  
% 2.61/1.38  tff(f_98, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 2.61/1.38  tff(f_94, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.61/1.38  tff(f_105, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k8_relset_1(A, A, k6_partfun1(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t171_funct_2)).
% 2.61/1.38  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.61/1.38  tff(f_100, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.61/1.38  tff(f_60, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 2.61/1.38  tff(f_78, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 2.61/1.38  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 2.61/1.38  tff(f_90, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 2.61/1.38  tff(f_70, axiom, (![A]: ((v1_relat_1(k6_relat_1(A)) & v4_relat_1(k6_relat_1(A), A)) & v5_relat_1(k6_relat_1(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc24_relat_1)).
% 2.61/1.38  tff(f_56, axiom, (![A, B]: (r1_tarski(A, B) => (![C]: ((v1_relat_1(C) & v4_relat_1(C, A)) => v4_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t217_relat_1)).
% 2.61/1.38  tff(f_47, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 2.61/1.38  tff(f_27, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.61/1.38  tff(f_33, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.61/1.38  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 2.61/1.38  tff(f_74, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.61/1.38  tff(f_88, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((r1_tarski(A, k1_relat_1(B)) & v2_funct_1(B)) => (k10_relat_1(B, k9_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t164_funct_1)).
% 2.61/1.38  tff(c_48, plain, (![A_34]: (m1_subset_1(k6_partfun1(A_34), k1_zfmisc_1(k2_zfmisc_1(A_34, A_34))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.61/1.38  tff(c_421, plain, (![A_83, B_84, C_85, D_86]: (k8_relset_1(A_83, B_84, C_85, D_86)=k10_relat_1(C_85, D_86) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.61/1.38  tff(c_428, plain, (![A_34, D_86]: (k8_relset_1(A_34, A_34, k6_partfun1(A_34), D_86)=k10_relat_1(k6_partfun1(A_34), D_86))), inference(resolution, [status(thm)], [c_48, c_421])).
% 2.61/1.38  tff(c_52, plain, (k8_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.61/1.38  tff(c_459, plain, (k10_relat_1(k6_partfun1('#skF_1'), '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_428, c_52])).
% 2.61/1.38  tff(c_54, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.61/1.38  tff(c_134, plain, (![A_50, B_51]: (r1_tarski(A_50, B_51) | ~m1_subset_1(A_50, k1_zfmisc_1(B_51)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.61/1.38  tff(c_146, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_54, c_134])).
% 2.61/1.38  tff(c_50, plain, (![A_35]: (k6_relat_1(A_35)=k6_partfun1(A_35))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.61/1.38  tff(c_22, plain, (![A_20]: (k2_relat_1(k6_relat_1(A_20))=A_20)), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.61/1.38  tff(c_64, plain, (![A_20]: (k2_relat_1(k6_partfun1(A_20))=A_20)), inference(demodulation, [status(thm), theory('equality')], [c_50, c_22])).
% 2.61/1.38  tff(c_36, plain, (![A_25]: (v1_relat_1(k6_relat_1(A_25)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.61/1.38  tff(c_57, plain, (![A_25]: (v1_relat_1(k6_partfun1(A_25)))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_36])).
% 2.61/1.38  tff(c_24, plain, (![A_21, B_22]: (k5_relat_1(k6_relat_1(A_21), B_22)=k7_relat_1(B_22, A_21) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.61/1.38  tff(c_304, plain, (![A_77, B_78]: (k5_relat_1(k6_partfun1(A_77), B_78)=k7_relat_1(B_78, A_77) | ~v1_relat_1(B_78))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_24])).
% 2.61/1.38  tff(c_42, plain, (![B_29, A_28]: (k5_relat_1(k6_relat_1(B_29), k6_relat_1(A_28))=k6_relat_1(k3_xboole_0(A_28, B_29)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.61/1.38  tff(c_55, plain, (![B_29, A_28]: (k5_relat_1(k6_partfun1(B_29), k6_partfun1(A_28))=k6_partfun1(k3_xboole_0(A_28, B_29)))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_50, c_50, c_42])).
% 2.61/1.38  tff(c_311, plain, (![A_28, A_77]: (k7_relat_1(k6_partfun1(A_28), A_77)=k6_partfun1(k3_xboole_0(A_28, A_77)) | ~v1_relat_1(k6_partfun1(A_28)))), inference(superposition, [status(thm), theory('equality')], [c_304, c_55])).
% 2.61/1.38  tff(c_320, plain, (![A_28, A_77]: (k7_relat_1(k6_partfun1(A_28), A_77)=k6_partfun1(k3_xboole_0(A_28, A_77)))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_311])).
% 2.61/1.38  tff(c_28, plain, (![A_23]: (v4_relat_1(k6_relat_1(A_23), A_23))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.61/1.38  tff(c_61, plain, (![A_23]: (v4_relat_1(k6_partfun1(A_23), A_23))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_28])).
% 2.61/1.38  tff(c_286, plain, (![C_72, B_73, A_74]: (v4_relat_1(C_72, B_73) | ~v4_relat_1(C_72, A_74) | ~v1_relat_1(C_72) | ~r1_tarski(A_74, B_73))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.61/1.38  tff(c_288, plain, (![A_23, B_73]: (v4_relat_1(k6_partfun1(A_23), B_73) | ~v1_relat_1(k6_partfun1(A_23)) | ~r1_tarski(A_23, B_73))), inference(resolution, [status(thm)], [c_61, c_286])).
% 2.61/1.38  tff(c_292, plain, (![A_75, B_76]: (v4_relat_1(k6_partfun1(A_75), B_76) | ~r1_tarski(A_75, B_76))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_288])).
% 2.61/1.38  tff(c_16, plain, (![B_15, A_14]: (k7_relat_1(B_15, A_14)=B_15 | ~v4_relat_1(B_15, A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.61/1.38  tff(c_297, plain, (![A_75, B_76]: (k7_relat_1(k6_partfun1(A_75), B_76)=k6_partfun1(A_75) | ~v1_relat_1(k6_partfun1(A_75)) | ~r1_tarski(A_75, B_76))), inference(resolution, [status(thm)], [c_292, c_16])).
% 2.61/1.38  tff(c_303, plain, (![A_75, B_76]: (k7_relat_1(k6_partfun1(A_75), B_76)=k6_partfun1(A_75) | ~r1_tarski(A_75, B_76))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_297])).
% 2.61/1.38  tff(c_470, plain, (![A_93, B_94]: (k6_partfun1(k3_xboole_0(A_93, B_94))=k6_partfun1(A_93) | ~r1_tarski(A_93, B_94))), inference(demodulation, [status(thm), theory('equality')], [c_320, c_303])).
% 2.61/1.38  tff(c_515, plain, (![A_93, B_94]: (k3_xboole_0(A_93, B_94)=k2_relat_1(k6_partfun1(A_93)) | ~r1_tarski(A_93, B_94))), inference(superposition, [status(thm), theory('equality')], [c_470, c_64])).
% 2.61/1.38  tff(c_554, plain, (![A_95, B_96]: (k3_xboole_0(A_95, B_96)=A_95 | ~r1_tarski(A_95, B_96))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_515])).
% 2.61/1.38  tff(c_562, plain, (k3_xboole_0('#skF_2', '#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_146, c_554])).
% 2.61/1.38  tff(c_2, plain, (![B_2, A_1]: (k2_tarski(B_2, A_1)=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.61/1.38  tff(c_157, plain, (![A_55, B_56]: (k1_setfam_1(k2_tarski(A_55, B_56))=k3_xboole_0(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.61/1.38  tff(c_181, plain, (![B_59, A_60]: (k1_setfam_1(k2_tarski(B_59, A_60))=k3_xboole_0(A_60, B_59))), inference(superposition, [status(thm), theory('equality')], [c_2, c_157])).
% 2.61/1.38  tff(c_8, plain, (![A_8, B_9]: (k1_setfam_1(k2_tarski(A_8, B_9))=k3_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.61/1.38  tff(c_187, plain, (![B_59, A_60]: (k3_xboole_0(B_59, A_60)=k3_xboole_0(A_60, B_59))), inference(superposition, [status(thm), theory('equality')], [c_181, c_8])).
% 2.61/1.38  tff(c_569, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_562, c_187])).
% 2.61/1.38  tff(c_324, plain, (![A_79, A_80]: (k7_relat_1(k6_partfun1(A_79), A_80)=k6_partfun1(k3_xboole_0(A_79, A_80)))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_311])).
% 2.61/1.38  tff(c_14, plain, (![B_13, A_12]: (k2_relat_1(k7_relat_1(B_13, A_12))=k9_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.61/1.38  tff(c_334, plain, (![A_79, A_80]: (k2_relat_1(k6_partfun1(k3_xboole_0(A_79, A_80)))=k9_relat_1(k6_partfun1(A_79), A_80) | ~v1_relat_1(k6_partfun1(A_79)))), inference(superposition, [status(thm), theory('equality')], [c_324, c_14])).
% 2.61/1.38  tff(c_343, plain, (![A_79, A_80]: (k9_relat_1(k6_partfun1(A_79), A_80)=k3_xboole_0(A_79, A_80))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_64, c_334])).
% 2.61/1.38  tff(c_34, plain, (![A_24]: (v1_funct_1(k6_relat_1(A_24)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.61/1.38  tff(c_58, plain, (![A_24]: (v1_funct_1(k6_partfun1(A_24)))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_34])).
% 2.61/1.38  tff(c_38, plain, (![A_25]: (v2_funct_1(k6_relat_1(A_25)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.61/1.38  tff(c_56, plain, (![A_25]: (v2_funct_1(k6_partfun1(A_25)))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_38])).
% 2.61/1.38  tff(c_20, plain, (![A_20]: (k1_relat_1(k6_relat_1(A_20))=A_20)), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.61/1.38  tff(c_65, plain, (![A_20]: (k1_relat_1(k6_partfun1(A_20))=A_20)), inference(demodulation, [status(thm), theory('equality')], [c_50, c_20])).
% 2.61/1.38  tff(c_432, plain, (![B_87, A_88]: (k10_relat_1(B_87, k9_relat_1(B_87, A_88))=A_88 | ~v2_funct_1(B_87) | ~r1_tarski(A_88, k1_relat_1(B_87)) | ~v1_funct_1(B_87) | ~v1_relat_1(B_87))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.61/1.38  tff(c_434, plain, (![A_20, A_88]: (k10_relat_1(k6_partfun1(A_20), k9_relat_1(k6_partfun1(A_20), A_88))=A_88 | ~v2_funct_1(k6_partfun1(A_20)) | ~r1_tarski(A_88, A_20) | ~v1_funct_1(k6_partfun1(A_20)) | ~v1_relat_1(k6_partfun1(A_20)))), inference(superposition, [status(thm), theory('equality')], [c_65, c_432])).
% 2.61/1.38  tff(c_436, plain, (![A_20, A_88]: (k10_relat_1(k6_partfun1(A_20), k9_relat_1(k6_partfun1(A_20), A_88))=A_88 | ~r1_tarski(A_88, A_20))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_58, c_56, c_434])).
% 2.61/1.38  tff(c_596, plain, (![A_97, A_98]: (k10_relat_1(k6_partfun1(A_97), k3_xboole_0(A_97, A_98))=A_98 | ~r1_tarski(A_98, A_97))), inference(demodulation, [status(thm), theory('equality')], [c_343, c_436])).
% 2.61/1.38  tff(c_605, plain, (k10_relat_1(k6_partfun1('#skF_1'), '#skF_2')='#skF_2' | ~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_569, c_596])).
% 2.61/1.38  tff(c_624, plain, (k10_relat_1(k6_partfun1('#skF_1'), '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_146, c_605])).
% 2.61/1.38  tff(c_626, plain, $false, inference(negUnitSimplification, [status(thm)], [c_459, c_624])).
% 2.61/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.61/1.38  
% 2.61/1.38  Inference rules
% 2.61/1.38  ----------------------
% 2.61/1.38  #Ref     : 0
% 2.61/1.38  #Sup     : 135
% 2.61/1.38  #Fact    : 0
% 2.61/1.38  #Define  : 0
% 2.61/1.38  #Split   : 0
% 2.61/1.38  #Chain   : 0
% 2.61/1.38  #Close   : 0
% 2.61/1.38  
% 2.61/1.38  Ordering : KBO
% 2.61/1.38  
% 2.61/1.38  Simplification rules
% 2.61/1.38  ----------------------
% 2.61/1.38  #Subsume      : 2
% 2.61/1.38  #Demod        : 73
% 2.61/1.38  #Tautology    : 85
% 2.61/1.38  #SimpNegUnit  : 1
% 2.61/1.38  #BackRed      : 1
% 2.61/1.38  
% 2.61/1.38  #Partial instantiations: 0
% 2.61/1.38  #Strategies tried      : 1
% 2.61/1.38  
% 2.61/1.38  Timing (in seconds)
% 2.61/1.38  ----------------------
% 2.61/1.39  Preprocessing        : 0.33
% 2.61/1.39  Parsing              : 0.18
% 2.61/1.39  CNF conversion       : 0.02
% 2.61/1.39  Main loop            : 0.28
% 2.61/1.39  Inferencing          : 0.10
% 2.61/1.39  Reduction            : 0.10
% 2.61/1.39  Demodulation         : 0.08
% 2.61/1.39  BG Simplification    : 0.02
% 2.61/1.39  Subsumption          : 0.04
% 2.61/1.39  Abstraction          : 0.02
% 2.61/1.39  MUC search           : 0.00
% 2.61/1.39  Cooper               : 0.00
% 2.61/1.39  Total                : 0.65
% 2.61/1.39  Index Insertion      : 0.00
% 2.61/1.39  Index Deletion       : 0.00
% 2.61/1.39  Index Matching       : 0.00
% 2.61/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
