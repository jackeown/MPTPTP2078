%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:12 EST 2020

% Result     : Theorem 3.36s
% Output     : CNFRefutation 3.36s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 177 expanded)
%              Number of leaves         :   45 (  81 expanded)
%              Depth                    :   13
%              Number of atoms          :  118 ( 215 expanded)
%              Number of equality atoms :   47 ( 110 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

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
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_96,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_94,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

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

tff(f_90,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

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

tff(f_88,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( ( r1_tarski(A,k1_relat_1(B))
          & v2_funct_1(B) )
       => k10_relat_1(B,k9_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).

tff(c_48,plain,(
    ! [A_35] : k6_relat_1(A_35) = k6_partfun1(A_35) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_46,plain,(
    ! [A_34] : m1_subset_1(k6_relat_1(A_34),k1_zfmisc_1(k2_zfmisc_1(A_34,A_34))) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_53,plain,(
    ! [A_34] : m1_subset_1(k6_partfun1(A_34),k1_zfmisc_1(k2_zfmisc_1(A_34,A_34))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46])).

tff(c_550,plain,(
    ! [A_88,B_89,C_90,D_91] :
      ( k8_relset_1(A_88,B_89,C_90,D_91) = k10_relat_1(C_90,D_91)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_556,plain,(
    ! [A_34,D_91] : k8_relset_1(A_34,A_34,k6_partfun1(A_34),D_91) = k10_relat_1(k6_partfun1(A_34),D_91) ),
    inference(resolution,[status(thm)],[c_53,c_550])).

tff(c_50,plain,(
    k8_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_769,plain,(
    k10_relat_1(k6_partfun1('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_556,c_50])).

tff(c_52,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_140,plain,(
    ! [A_50,B_51] :
      ( r1_tarski(A_50,B_51)
      | ~ m1_subset_1(A_50,k1_zfmisc_1(B_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_148,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_140])).

tff(c_22,plain,(
    ! [A_20] : k2_relat_1(k6_relat_1(A_20)) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_63,plain,(
    ! [A_20] : k2_relat_1(k6_partfun1(A_20)) = A_20 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_22])).

tff(c_36,plain,(
    ! [A_25] : v1_relat_1(k6_relat_1(A_25)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_56,plain,(
    ! [A_25] : v1_relat_1(k6_partfun1(A_25)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_36])).

tff(c_42,plain,(
    ! [B_29,A_28] : k5_relat_1(k6_relat_1(B_29),k6_relat_1(A_28)) = k6_relat_1(k3_xboole_0(A_28,B_29)) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_252,plain,(
    ! [B_65,A_66] : k5_relat_1(k6_partfun1(B_65),k6_partfun1(A_66)) = k6_partfun1(k3_xboole_0(A_66,B_65)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_48,c_48,c_42])).

tff(c_24,plain,(
    ! [A_21,B_22] :
      ( k5_relat_1(k6_relat_1(A_21),B_22) = k7_relat_1(B_22,A_21)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_62,plain,(
    ! [A_21,B_22] :
      ( k5_relat_1(k6_partfun1(A_21),B_22) = k7_relat_1(B_22,A_21)
      | ~ v1_relat_1(B_22) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_24])).

tff(c_258,plain,(
    ! [A_66,B_65] :
      ( k7_relat_1(k6_partfun1(A_66),B_65) = k6_partfun1(k3_xboole_0(A_66,B_65))
      | ~ v1_relat_1(k6_partfun1(A_66)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_252,c_62])).

tff(c_268,plain,(
    ! [A_66,B_65] : k7_relat_1(k6_partfun1(A_66),B_65) = k6_partfun1(k3_xboole_0(A_66,B_65)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_258])).

tff(c_28,plain,(
    ! [A_23] : v4_relat_1(k6_relat_1(A_23),A_23) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_60,plain,(
    ! [A_23] : v4_relat_1(k6_partfun1(A_23),A_23) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_28])).

tff(c_416,plain,(
    ! [C_79,B_80,A_81] :
      ( v4_relat_1(C_79,B_80)
      | ~ v4_relat_1(C_79,A_81)
      | ~ v1_relat_1(C_79)
      | ~ r1_tarski(A_81,B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_418,plain,(
    ! [A_23,B_80] :
      ( v4_relat_1(k6_partfun1(A_23),B_80)
      | ~ v1_relat_1(k6_partfun1(A_23))
      | ~ r1_tarski(A_23,B_80) ) ),
    inference(resolution,[status(thm)],[c_60,c_416])).

tff(c_422,plain,(
    ! [A_82,B_83] :
      ( v4_relat_1(k6_partfun1(A_82),B_83)
      | ~ r1_tarski(A_82,B_83) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_418])).

tff(c_16,plain,(
    ! [B_15,A_14] :
      ( k7_relat_1(B_15,A_14) = B_15
      | ~ v4_relat_1(B_15,A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_427,plain,(
    ! [A_82,B_83] :
      ( k7_relat_1(k6_partfun1(A_82),B_83) = k6_partfun1(A_82)
      | ~ v1_relat_1(k6_partfun1(A_82))
      | ~ r1_tarski(A_82,B_83) ) ),
    inference(resolution,[status(thm)],[c_422,c_16])).

tff(c_434,plain,(
    ! [A_84,B_85] :
      ( k6_partfun1(k3_xboole_0(A_84,B_85)) = k6_partfun1(A_84)
      | ~ r1_tarski(A_84,B_85) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_268,c_427])).

tff(c_473,plain,(
    ! [A_84,B_85] :
      ( k3_xboole_0(A_84,B_85) = k2_relat_1(k6_partfun1(A_84))
      | ~ r1_tarski(A_84,B_85) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_434,c_63])).

tff(c_512,plain,(
    ! [A_86,B_87] :
      ( k3_xboole_0(A_86,B_87) = A_86
      | ~ r1_tarski(A_86,B_87) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_473])).

tff(c_520,plain,(
    k3_xboole_0('#skF_2','#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_148,c_512])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_tarski(B_2,A_1) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_149,plain,(
    ! [A_52,B_53] : k1_setfam_1(k2_tarski(A_52,B_53)) = k3_xboole_0(A_52,B_53) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_170,plain,(
    ! [B_56,A_57] : k1_setfam_1(k2_tarski(B_56,A_57)) = k3_xboole_0(A_57,B_56) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_149])).

tff(c_8,plain,(
    ! [A_8,B_9] : k1_setfam_1(k2_tarski(A_8,B_9)) = k3_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_176,plain,(
    ! [B_56,A_57] : k3_xboole_0(B_56,A_57) = k3_xboole_0(A_57,B_56) ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_8])).

tff(c_527,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_520,c_176])).

tff(c_34,plain,(
    ! [A_24] : v1_funct_1(k6_relat_1(A_24)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_57,plain,(
    ! [A_24] : v1_funct_1(k6_partfun1(A_24)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_34])).

tff(c_38,plain,(
    ! [A_25] : v2_funct_1(k6_relat_1(A_25)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_55,plain,(
    ! [A_25] : v2_funct_1(k6_partfun1(A_25)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_38])).

tff(c_369,plain,(
    ! [B_74,A_75] :
      ( k2_relat_1(k7_relat_1(B_74,A_75)) = k9_relat_1(B_74,A_75)
      | ~ v1_relat_1(B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_378,plain,(
    ! [A_66,B_65] :
      ( k2_relat_1(k6_partfun1(k3_xboole_0(A_66,B_65))) = k9_relat_1(k6_partfun1(A_66),B_65)
      | ~ v1_relat_1(k6_partfun1(A_66)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_268,c_369])).

tff(c_385,plain,(
    ! [A_66,B_65] : k9_relat_1(k6_partfun1(A_66),B_65) = k3_xboole_0(A_66,B_65) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_63,c_378])).

tff(c_20,plain,(
    ! [A_20] : k1_relat_1(k6_relat_1(A_20)) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_64,plain,(
    ! [A_20] : k1_relat_1(k6_partfun1(A_20)) = A_20 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_20])).

tff(c_709,plain,(
    ! [B_97,A_98] :
      ( k10_relat_1(B_97,k9_relat_1(B_97,A_98)) = A_98
      | ~ v2_funct_1(B_97)
      | ~ r1_tarski(A_98,k1_relat_1(B_97))
      | ~ v1_funct_1(B_97)
      | ~ v1_relat_1(B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_711,plain,(
    ! [A_20,A_98] :
      ( k10_relat_1(k6_partfun1(A_20),k9_relat_1(k6_partfun1(A_20),A_98)) = A_98
      | ~ v2_funct_1(k6_partfun1(A_20))
      | ~ r1_tarski(A_98,A_20)
      | ~ v1_funct_1(k6_partfun1(A_20))
      | ~ v1_relat_1(k6_partfun1(A_20)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_709])).

tff(c_1062,plain,(
    ! [A_120,A_121] :
      ( k10_relat_1(k6_partfun1(A_120),k3_xboole_0(A_120,A_121)) = A_121
      | ~ r1_tarski(A_121,A_120) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_57,c_55,c_385,c_711])).

tff(c_1083,plain,
    ( k10_relat_1(k6_partfun1('#skF_1'),'#skF_2') = '#skF_2'
    | ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_527,c_1062])).

tff(c_1104,plain,(
    k10_relat_1(k6_partfun1('#skF_1'),'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_1083])).

tff(c_1106,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_769,c_1104])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:49:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.36/1.78  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.36/1.79  
% 3.36/1.79  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.36/1.79  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 3.36/1.79  
% 3.36/1.79  %Foreground sorts:
% 3.36/1.79  
% 3.36/1.79  
% 3.36/1.79  %Background operators:
% 3.36/1.79  
% 3.36/1.79  
% 3.36/1.79  %Foreground operators:
% 3.36/1.79  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.36/1.79  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.36/1.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.36/1.79  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.36/1.79  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.36/1.79  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.36/1.79  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.36/1.79  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.36/1.79  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.36/1.79  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.36/1.79  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.36/1.79  tff('#skF_2', type, '#skF_2': $i).
% 3.36/1.79  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.36/1.79  tff('#skF_1', type, '#skF_1': $i).
% 3.36/1.79  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.36/1.79  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.36/1.79  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 3.36/1.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.36/1.79  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.36/1.79  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.36/1.79  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.36/1.79  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.36/1.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.36/1.79  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.36/1.79  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.36/1.79  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.36/1.79  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.36/1.79  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.36/1.79  
% 3.36/1.81  tff(f_98, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 3.36/1.81  tff(f_96, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 3.36/1.81  tff(f_94, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.36/1.81  tff(f_103, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k8_relset_1(A, A, k6_partfun1(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t171_funct_2)).
% 3.36/1.81  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.36/1.81  tff(f_60, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 3.36/1.81  tff(f_78, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 3.36/1.81  tff(f_90, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 3.36/1.81  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 3.36/1.81  tff(f_70, axiom, (![A]: ((v1_relat_1(k6_relat_1(A)) & v4_relat_1(k6_relat_1(A), A)) & v5_relat_1(k6_relat_1(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc24_relat_1)).
% 3.36/1.81  tff(f_56, axiom, (![A, B]: (r1_tarski(A, B) => (![C]: ((v1_relat_1(C) & v4_relat_1(C, A)) => v4_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t217_relat_1)).
% 3.36/1.81  tff(f_47, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 3.36/1.81  tff(f_27, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.36/1.81  tff(f_33, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.36/1.81  tff(f_74, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 3.36/1.81  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 3.36/1.81  tff(f_88, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((r1_tarski(A, k1_relat_1(B)) & v2_funct_1(B)) => (k10_relat_1(B, k9_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t164_funct_1)).
% 3.36/1.81  tff(c_48, plain, (![A_35]: (k6_relat_1(A_35)=k6_partfun1(A_35))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.36/1.81  tff(c_46, plain, (![A_34]: (m1_subset_1(k6_relat_1(A_34), k1_zfmisc_1(k2_zfmisc_1(A_34, A_34))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.36/1.81  tff(c_53, plain, (![A_34]: (m1_subset_1(k6_partfun1(A_34), k1_zfmisc_1(k2_zfmisc_1(A_34, A_34))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46])).
% 3.36/1.81  tff(c_550, plain, (![A_88, B_89, C_90, D_91]: (k8_relset_1(A_88, B_89, C_90, D_91)=k10_relat_1(C_90, D_91) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.36/1.81  tff(c_556, plain, (![A_34, D_91]: (k8_relset_1(A_34, A_34, k6_partfun1(A_34), D_91)=k10_relat_1(k6_partfun1(A_34), D_91))), inference(resolution, [status(thm)], [c_53, c_550])).
% 3.36/1.81  tff(c_50, plain, (k8_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.36/1.81  tff(c_769, plain, (k10_relat_1(k6_partfun1('#skF_1'), '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_556, c_50])).
% 3.36/1.81  tff(c_52, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.36/1.81  tff(c_140, plain, (![A_50, B_51]: (r1_tarski(A_50, B_51) | ~m1_subset_1(A_50, k1_zfmisc_1(B_51)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.36/1.81  tff(c_148, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_52, c_140])).
% 3.36/1.81  tff(c_22, plain, (![A_20]: (k2_relat_1(k6_relat_1(A_20))=A_20)), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.36/1.81  tff(c_63, plain, (![A_20]: (k2_relat_1(k6_partfun1(A_20))=A_20)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_22])).
% 3.36/1.81  tff(c_36, plain, (![A_25]: (v1_relat_1(k6_relat_1(A_25)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.36/1.81  tff(c_56, plain, (![A_25]: (v1_relat_1(k6_partfun1(A_25)))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_36])).
% 3.36/1.81  tff(c_42, plain, (![B_29, A_28]: (k5_relat_1(k6_relat_1(B_29), k6_relat_1(A_28))=k6_relat_1(k3_xboole_0(A_28, B_29)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.36/1.81  tff(c_252, plain, (![B_65, A_66]: (k5_relat_1(k6_partfun1(B_65), k6_partfun1(A_66))=k6_partfun1(k3_xboole_0(A_66, B_65)))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_48, c_48, c_42])).
% 3.36/1.81  tff(c_24, plain, (![A_21, B_22]: (k5_relat_1(k6_relat_1(A_21), B_22)=k7_relat_1(B_22, A_21) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.36/1.81  tff(c_62, plain, (![A_21, B_22]: (k5_relat_1(k6_partfun1(A_21), B_22)=k7_relat_1(B_22, A_21) | ~v1_relat_1(B_22))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_24])).
% 3.36/1.81  tff(c_258, plain, (![A_66, B_65]: (k7_relat_1(k6_partfun1(A_66), B_65)=k6_partfun1(k3_xboole_0(A_66, B_65)) | ~v1_relat_1(k6_partfun1(A_66)))), inference(superposition, [status(thm), theory('equality')], [c_252, c_62])).
% 3.36/1.81  tff(c_268, plain, (![A_66, B_65]: (k7_relat_1(k6_partfun1(A_66), B_65)=k6_partfun1(k3_xboole_0(A_66, B_65)))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_258])).
% 3.36/1.81  tff(c_28, plain, (![A_23]: (v4_relat_1(k6_relat_1(A_23), A_23))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.36/1.81  tff(c_60, plain, (![A_23]: (v4_relat_1(k6_partfun1(A_23), A_23))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_28])).
% 3.36/1.81  tff(c_416, plain, (![C_79, B_80, A_81]: (v4_relat_1(C_79, B_80) | ~v4_relat_1(C_79, A_81) | ~v1_relat_1(C_79) | ~r1_tarski(A_81, B_80))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.36/1.81  tff(c_418, plain, (![A_23, B_80]: (v4_relat_1(k6_partfun1(A_23), B_80) | ~v1_relat_1(k6_partfun1(A_23)) | ~r1_tarski(A_23, B_80))), inference(resolution, [status(thm)], [c_60, c_416])).
% 3.36/1.81  tff(c_422, plain, (![A_82, B_83]: (v4_relat_1(k6_partfun1(A_82), B_83) | ~r1_tarski(A_82, B_83))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_418])).
% 3.36/1.81  tff(c_16, plain, (![B_15, A_14]: (k7_relat_1(B_15, A_14)=B_15 | ~v4_relat_1(B_15, A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.36/1.81  tff(c_427, plain, (![A_82, B_83]: (k7_relat_1(k6_partfun1(A_82), B_83)=k6_partfun1(A_82) | ~v1_relat_1(k6_partfun1(A_82)) | ~r1_tarski(A_82, B_83))), inference(resolution, [status(thm)], [c_422, c_16])).
% 3.36/1.81  tff(c_434, plain, (![A_84, B_85]: (k6_partfun1(k3_xboole_0(A_84, B_85))=k6_partfun1(A_84) | ~r1_tarski(A_84, B_85))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_268, c_427])).
% 3.36/1.81  tff(c_473, plain, (![A_84, B_85]: (k3_xboole_0(A_84, B_85)=k2_relat_1(k6_partfun1(A_84)) | ~r1_tarski(A_84, B_85))), inference(superposition, [status(thm), theory('equality')], [c_434, c_63])).
% 3.36/1.81  tff(c_512, plain, (![A_86, B_87]: (k3_xboole_0(A_86, B_87)=A_86 | ~r1_tarski(A_86, B_87))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_473])).
% 3.36/1.81  tff(c_520, plain, (k3_xboole_0('#skF_2', '#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_148, c_512])).
% 3.36/1.81  tff(c_2, plain, (![B_2, A_1]: (k2_tarski(B_2, A_1)=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.36/1.81  tff(c_149, plain, (![A_52, B_53]: (k1_setfam_1(k2_tarski(A_52, B_53))=k3_xboole_0(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.36/1.81  tff(c_170, plain, (![B_56, A_57]: (k1_setfam_1(k2_tarski(B_56, A_57))=k3_xboole_0(A_57, B_56))), inference(superposition, [status(thm), theory('equality')], [c_2, c_149])).
% 3.36/1.81  tff(c_8, plain, (![A_8, B_9]: (k1_setfam_1(k2_tarski(A_8, B_9))=k3_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.36/1.81  tff(c_176, plain, (![B_56, A_57]: (k3_xboole_0(B_56, A_57)=k3_xboole_0(A_57, B_56))), inference(superposition, [status(thm), theory('equality')], [c_170, c_8])).
% 3.36/1.81  tff(c_527, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_520, c_176])).
% 3.36/1.81  tff(c_34, plain, (![A_24]: (v1_funct_1(k6_relat_1(A_24)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.36/1.81  tff(c_57, plain, (![A_24]: (v1_funct_1(k6_partfun1(A_24)))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_34])).
% 3.36/1.81  tff(c_38, plain, (![A_25]: (v2_funct_1(k6_relat_1(A_25)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.36/1.81  tff(c_55, plain, (![A_25]: (v2_funct_1(k6_partfun1(A_25)))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_38])).
% 3.36/1.81  tff(c_369, plain, (![B_74, A_75]: (k2_relat_1(k7_relat_1(B_74, A_75))=k9_relat_1(B_74, A_75) | ~v1_relat_1(B_74))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.36/1.81  tff(c_378, plain, (![A_66, B_65]: (k2_relat_1(k6_partfun1(k3_xboole_0(A_66, B_65)))=k9_relat_1(k6_partfun1(A_66), B_65) | ~v1_relat_1(k6_partfun1(A_66)))), inference(superposition, [status(thm), theory('equality')], [c_268, c_369])).
% 3.36/1.81  tff(c_385, plain, (![A_66, B_65]: (k9_relat_1(k6_partfun1(A_66), B_65)=k3_xboole_0(A_66, B_65))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_63, c_378])).
% 3.36/1.81  tff(c_20, plain, (![A_20]: (k1_relat_1(k6_relat_1(A_20))=A_20)), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.36/1.81  tff(c_64, plain, (![A_20]: (k1_relat_1(k6_partfun1(A_20))=A_20)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_20])).
% 3.36/1.81  tff(c_709, plain, (![B_97, A_98]: (k10_relat_1(B_97, k9_relat_1(B_97, A_98))=A_98 | ~v2_funct_1(B_97) | ~r1_tarski(A_98, k1_relat_1(B_97)) | ~v1_funct_1(B_97) | ~v1_relat_1(B_97))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.36/1.81  tff(c_711, plain, (![A_20, A_98]: (k10_relat_1(k6_partfun1(A_20), k9_relat_1(k6_partfun1(A_20), A_98))=A_98 | ~v2_funct_1(k6_partfun1(A_20)) | ~r1_tarski(A_98, A_20) | ~v1_funct_1(k6_partfun1(A_20)) | ~v1_relat_1(k6_partfun1(A_20)))), inference(superposition, [status(thm), theory('equality')], [c_64, c_709])).
% 3.36/1.81  tff(c_1062, plain, (![A_120, A_121]: (k10_relat_1(k6_partfun1(A_120), k3_xboole_0(A_120, A_121))=A_121 | ~r1_tarski(A_121, A_120))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_57, c_55, c_385, c_711])).
% 3.36/1.81  tff(c_1083, plain, (k10_relat_1(k6_partfun1('#skF_1'), '#skF_2')='#skF_2' | ~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_527, c_1062])).
% 3.36/1.81  tff(c_1104, plain, (k10_relat_1(k6_partfun1('#skF_1'), '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_148, c_1083])).
% 3.36/1.81  tff(c_1106, plain, $false, inference(negUnitSimplification, [status(thm)], [c_769, c_1104])).
% 3.36/1.81  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.36/1.81  
% 3.36/1.81  Inference rules
% 3.36/1.81  ----------------------
% 3.36/1.81  #Ref     : 0
% 3.36/1.81  #Sup     : 262
% 3.36/1.81  #Fact    : 0
% 3.36/1.81  #Define  : 0
% 3.36/1.81  #Split   : 1
% 3.36/1.81  #Chain   : 0
% 3.36/1.81  #Close   : 0
% 3.36/1.81  
% 3.36/1.81  Ordering : KBO
% 3.36/1.81  
% 3.36/1.81  Simplification rules
% 3.36/1.81  ----------------------
% 3.36/1.81  #Subsume      : 24
% 3.36/1.81  #Demod        : 136
% 3.36/1.81  #Tautology    : 123
% 3.36/1.81  #SimpNegUnit  : 1
% 3.36/1.81  #BackRed      : 1
% 3.36/1.81  
% 3.36/1.81  #Partial instantiations: 0
% 3.36/1.81  #Strategies tried      : 1
% 3.36/1.81  
% 3.36/1.81  Timing (in seconds)
% 3.36/1.81  ----------------------
% 3.36/1.81  Preprocessing        : 0.53
% 3.36/1.81  Parsing              : 0.28
% 3.36/1.81  CNF conversion       : 0.03
% 3.36/1.81  Main loop            : 0.45
% 3.36/1.81  Inferencing          : 0.15
% 3.36/1.81  Reduction            : 0.17
% 3.36/1.81  Demodulation         : 0.13
% 3.36/1.81  BG Simplification    : 0.03
% 3.36/1.81  Subsumption          : 0.07
% 3.36/1.81  Abstraction          : 0.03
% 3.36/1.81  MUC search           : 0.00
% 3.36/1.81  Cooper               : 0.00
% 3.36/1.81  Total                : 1.02
% 3.36/1.81  Index Insertion      : 0.00
% 3.36/1.81  Index Deletion       : 0.00
% 3.36/1.81  Index Matching       : 0.00
% 3.36/1.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
