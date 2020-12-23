%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:12 EST 2020

% Result     : Theorem 2.73s
% Output     : CNFRefutation 2.97s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 188 expanded)
%              Number of leaves         :   48 (  87 expanded)
%              Depth                    :   11
%              Number of atoms          :  119 ( 229 expanded)
%              Number of equality atoms :   48 ( 119 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(f_108,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k8_relset_1(A,A,k6_partfun1(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_2)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_103,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_81,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_77,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_67,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_91,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_93,axiom,(
    ! [A] : k2_funct_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k10_relat_1(B,A) = k9_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).

tff(f_73,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v4_relat_1(k6_relat_1(A),A)
      & v5_relat_1(k6_relat_1(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc24_relat_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ! [C] :
          ( ( v1_relat_1(C)
            & v4_relat_1(C,A) )
         => v4_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t217_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_33,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_101,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_97,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(c_56,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_168,plain,(
    ! [A_55,B_56] :
      ( r1_tarski(A_55,B_56)
      | ~ m1_subset_1(A_55,k1_zfmisc_1(B_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_176,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_168])).

tff(c_52,plain,(
    ! [A_37] : k6_relat_1(A_37) = k6_partfun1(A_37) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_36,plain,(
    ! [A_26] : v1_relat_1(k6_relat_1(A_26)) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_60,plain,(
    ! [A_26] : v1_relat_1(k6_partfun1(A_26)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_36])).

tff(c_34,plain,(
    ! [A_25] : v1_funct_1(k6_relat_1(A_25)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_61,plain,(
    ! [A_25] : v1_funct_1(k6_partfun1(A_25)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_34])).

tff(c_38,plain,(
    ! [A_26] : v2_funct_1(k6_relat_1(A_26)) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_59,plain,(
    ! [A_26] : v2_funct_1(k6_partfun1(A_26)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_38])).

tff(c_22,plain,(
    ! [A_23] : k1_relat_1(k6_relat_1(A_23)) = A_23 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_67,plain,(
    ! [A_23] : k1_relat_1(k6_partfun1(A_23)) = A_23 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_22])).

tff(c_42,plain,(
    ! [B_30,A_29] : k5_relat_1(k6_relat_1(B_30),k6_relat_1(A_29)) = k6_relat_1(k3_xboole_0(A_29,B_30)) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_58,plain,(
    ! [B_30,A_29] : k5_relat_1(k6_partfun1(B_30),k6_partfun1(A_29)) = k6_partfun1(k3_xboole_0(A_29,B_30)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_52,c_52,c_42])).

tff(c_363,plain,(
    ! [A_87,B_88] :
      ( k10_relat_1(A_87,k1_relat_1(B_88)) = k1_relat_1(k5_relat_1(A_87,B_88))
      | ~ v1_relat_1(B_88)
      | ~ v1_relat_1(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_372,plain,(
    ! [A_87,A_23] :
      ( k1_relat_1(k5_relat_1(A_87,k6_partfun1(A_23))) = k10_relat_1(A_87,A_23)
      | ~ v1_relat_1(k6_partfun1(A_23))
      | ~ v1_relat_1(A_87) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_363])).

tff(c_462,plain,(
    ! [A_94,A_95] :
      ( k1_relat_1(k5_relat_1(A_94,k6_partfun1(A_95))) = k10_relat_1(A_94,A_95)
      | ~ v1_relat_1(A_94) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_372])).

tff(c_474,plain,(
    ! [A_29,B_30] :
      ( k1_relat_1(k6_partfun1(k3_xboole_0(A_29,B_30))) = k10_relat_1(k6_partfun1(B_30),A_29)
      | ~ v1_relat_1(k6_partfun1(B_30)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_462])).

tff(c_478,plain,(
    ! [B_30,A_29] : k10_relat_1(k6_partfun1(B_30),A_29) = k3_xboole_0(A_29,B_30) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_67,c_474])).

tff(c_44,plain,(
    ! [A_31] : k2_funct_1(k6_relat_1(A_31)) = k6_relat_1(A_31) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_57,plain,(
    ! [A_31] : k2_funct_1(k6_partfun1(A_31)) = k6_partfun1(A_31) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_52,c_44])).

tff(c_541,plain,(
    ! [B_102,A_103] :
      ( k9_relat_1(k2_funct_1(B_102),A_103) = k10_relat_1(B_102,A_103)
      | ~ v2_funct_1(B_102)
      | ~ v1_funct_1(B_102)
      | ~ v1_relat_1(B_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_550,plain,(
    ! [A_31,A_103] :
      ( k9_relat_1(k6_partfun1(A_31),A_103) = k10_relat_1(k6_partfun1(A_31),A_103)
      | ~ v2_funct_1(k6_partfun1(A_31))
      | ~ v1_funct_1(k6_partfun1(A_31))
      | ~ v1_relat_1(k6_partfun1(A_31)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_541])).

tff(c_554,plain,(
    ! [A_31,A_103] : k9_relat_1(k6_partfun1(A_31),A_103) = k3_xboole_0(A_103,A_31) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_61,c_59,c_478,c_550])).

tff(c_24,plain,(
    ! [A_23] : k2_relat_1(k6_relat_1(A_23)) = A_23 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_66,plain,(
    ! [A_23] : k2_relat_1(k6_partfun1(A_23)) = A_23 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_24])).

tff(c_28,plain,(
    ! [A_24] : v4_relat_1(k6_relat_1(A_24),A_24) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_64,plain,(
    ! [A_24] : v4_relat_1(k6_partfun1(A_24),A_24) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_28])).

tff(c_297,plain,(
    ! [C_75,B_76,A_77] :
      ( v4_relat_1(C_75,B_76)
      | ~ v4_relat_1(C_75,A_77)
      | ~ v1_relat_1(C_75)
      | ~ r1_tarski(A_77,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_299,plain,(
    ! [A_24,B_76] :
      ( v4_relat_1(k6_partfun1(A_24),B_76)
      | ~ v1_relat_1(k6_partfun1(A_24))
      | ~ r1_tarski(A_24,B_76) ) ),
    inference(resolution,[status(thm)],[c_64,c_297])).

tff(c_303,plain,(
    ! [A_78,B_79] :
      ( v4_relat_1(k6_partfun1(A_78),B_79)
      | ~ r1_tarski(A_78,B_79) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_299])).

tff(c_18,plain,(
    ! [B_18,A_17] :
      ( k7_relat_1(B_18,A_17) = B_18
      | ~ v4_relat_1(B_18,A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_308,plain,(
    ! [A_78,B_79] :
      ( k7_relat_1(k6_partfun1(A_78),B_79) = k6_partfun1(A_78)
      | ~ v1_relat_1(k6_partfun1(A_78))
      | ~ r1_tarski(A_78,B_79) ) ),
    inference(resolution,[status(thm)],[c_303,c_18])).

tff(c_315,plain,(
    ! [A_80,B_81] :
      ( k7_relat_1(k6_partfun1(A_80),B_81) = k6_partfun1(A_80)
      | ~ r1_tarski(A_80,B_81) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_308])).

tff(c_14,plain,(
    ! [B_13,A_12] :
      ( k2_relat_1(k7_relat_1(B_13,A_12)) = k9_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_321,plain,(
    ! [A_80,B_81] :
      ( k9_relat_1(k6_partfun1(A_80),B_81) = k2_relat_1(k6_partfun1(A_80))
      | ~ v1_relat_1(k6_partfun1(A_80))
      | ~ r1_tarski(A_80,B_81) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_315,c_14])).

tff(c_334,plain,(
    ! [A_80,B_81] :
      ( k9_relat_1(k6_partfun1(A_80),B_81) = A_80
      | ~ r1_tarski(A_80,B_81) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_66,c_321])).

tff(c_623,plain,(
    ! [B_109,A_110] :
      ( k3_xboole_0(B_109,A_110) = A_110
      | ~ r1_tarski(A_110,B_109) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_554,c_334])).

tff(c_631,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_176,c_623])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_tarski(B_2,A_1) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_143,plain,(
    ! [A_50,B_51] : k1_setfam_1(k2_tarski(A_50,B_51)) = k3_xboole_0(A_50,B_51) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_183,plain,(
    ! [A_60,B_61] : k1_setfam_1(k2_tarski(A_60,B_61)) = k3_xboole_0(B_61,A_60) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_143])).

tff(c_8,plain,(
    ! [A_8,B_9] : k1_setfam_1(k2_tarski(A_8,B_9)) = k3_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_189,plain,(
    ! [B_61,A_60] : k3_xboole_0(B_61,A_60) = k3_xboole_0(A_60,B_61) ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_8])).

tff(c_50,plain,(
    ! [A_36] : m1_subset_1(k6_partfun1(A_36),k1_zfmisc_1(k2_zfmisc_1(A_36,A_36))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_667,plain,(
    ! [A_114,B_115,C_116,D_117] :
      ( k8_relset_1(A_114,B_115,C_116,D_117) = k10_relat_1(C_116,D_117)
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1(A_114,B_115))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_672,plain,(
    ! [A_36,D_117] : k8_relset_1(A_36,A_36,k6_partfun1(A_36),D_117) = k10_relat_1(k6_partfun1(A_36),D_117) ),
    inference(resolution,[status(thm)],[c_50,c_667])).

tff(c_675,plain,(
    ! [A_36,D_117] : k8_relset_1(A_36,A_36,k6_partfun1(A_36),D_117) = k3_xboole_0(D_117,A_36) ),
    inference(demodulation,[status(thm),theory(equality)],[c_478,c_672])).

tff(c_54,plain,(
    k8_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_686,plain,(
    k3_xboole_0('#skF_2','#skF_1') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_675,c_54])).

tff(c_689,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_631,c_189,c_686])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:27:11 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.73/1.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/1.41  
% 2.73/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/1.41  %$ v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.73/1.41  
% 2.73/1.41  %Foreground sorts:
% 2.73/1.41  
% 2.73/1.41  
% 2.73/1.41  %Background operators:
% 2.73/1.41  
% 2.73/1.41  
% 2.73/1.41  %Foreground operators:
% 2.73/1.41  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.73/1.41  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.73/1.41  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.73/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.73/1.41  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.73/1.41  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.73/1.41  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.73/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.73/1.41  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.73/1.41  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.73/1.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.73/1.41  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.73/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.73/1.41  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.73/1.41  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.73/1.41  tff('#skF_1', type, '#skF_1': $i).
% 2.73/1.41  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.73/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.73/1.41  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.73/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.73/1.41  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.73/1.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.73/1.41  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.73/1.41  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.73/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.73/1.41  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.73/1.41  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.73/1.41  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.73/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.73/1.41  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.73/1.41  
% 2.97/1.43  tff(f_108, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k8_relset_1(A, A, k6_partfun1(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t171_funct_2)).
% 2.97/1.43  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.97/1.43  tff(f_103, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.97/1.43  tff(f_81, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 2.97/1.43  tff(f_77, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.97/1.43  tff(f_67, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 2.97/1.43  tff(f_91, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 2.97/1.43  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 2.97/1.43  tff(f_93, axiom, (![A]: (k2_funct_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_funct_1)).
% 2.97/1.43  tff(f_89, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k10_relat_1(B, A) = k9_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t155_funct_1)).
% 2.97/1.43  tff(f_73, axiom, (![A]: ((v1_relat_1(k6_relat_1(A)) & v4_relat_1(k6_relat_1(A), A)) & v5_relat_1(k6_relat_1(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc24_relat_1)).
% 2.97/1.43  tff(f_63, axiom, (![A, B]: (r1_tarski(A, B) => (![C]: ((v1_relat_1(C) & v4_relat_1(C, A)) => v4_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t217_relat_1)).
% 2.97/1.43  tff(f_54, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 2.97/1.43  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 2.97/1.43  tff(f_27, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.97/1.43  tff(f_33, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.97/1.43  tff(f_101, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 2.97/1.43  tff(f_97, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.97/1.43  tff(c_56, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.97/1.43  tff(c_168, plain, (![A_55, B_56]: (r1_tarski(A_55, B_56) | ~m1_subset_1(A_55, k1_zfmisc_1(B_56)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.97/1.43  tff(c_176, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_56, c_168])).
% 2.97/1.43  tff(c_52, plain, (![A_37]: (k6_relat_1(A_37)=k6_partfun1(A_37))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.97/1.43  tff(c_36, plain, (![A_26]: (v1_relat_1(k6_relat_1(A_26)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.97/1.43  tff(c_60, plain, (![A_26]: (v1_relat_1(k6_partfun1(A_26)))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_36])).
% 2.97/1.43  tff(c_34, plain, (![A_25]: (v1_funct_1(k6_relat_1(A_25)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.97/1.43  tff(c_61, plain, (![A_25]: (v1_funct_1(k6_partfun1(A_25)))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_34])).
% 2.97/1.43  tff(c_38, plain, (![A_26]: (v2_funct_1(k6_relat_1(A_26)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.97/1.43  tff(c_59, plain, (![A_26]: (v2_funct_1(k6_partfun1(A_26)))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_38])).
% 2.97/1.43  tff(c_22, plain, (![A_23]: (k1_relat_1(k6_relat_1(A_23))=A_23)), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.97/1.43  tff(c_67, plain, (![A_23]: (k1_relat_1(k6_partfun1(A_23))=A_23)), inference(demodulation, [status(thm), theory('equality')], [c_52, c_22])).
% 2.97/1.43  tff(c_42, plain, (![B_30, A_29]: (k5_relat_1(k6_relat_1(B_30), k6_relat_1(A_29))=k6_relat_1(k3_xboole_0(A_29, B_30)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.97/1.43  tff(c_58, plain, (![B_30, A_29]: (k5_relat_1(k6_partfun1(B_30), k6_partfun1(A_29))=k6_partfun1(k3_xboole_0(A_29, B_30)))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_52, c_52, c_42])).
% 2.97/1.43  tff(c_363, plain, (![A_87, B_88]: (k10_relat_1(A_87, k1_relat_1(B_88))=k1_relat_1(k5_relat_1(A_87, B_88)) | ~v1_relat_1(B_88) | ~v1_relat_1(A_87))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.97/1.43  tff(c_372, plain, (![A_87, A_23]: (k1_relat_1(k5_relat_1(A_87, k6_partfun1(A_23)))=k10_relat_1(A_87, A_23) | ~v1_relat_1(k6_partfun1(A_23)) | ~v1_relat_1(A_87))), inference(superposition, [status(thm), theory('equality')], [c_67, c_363])).
% 2.97/1.43  tff(c_462, plain, (![A_94, A_95]: (k1_relat_1(k5_relat_1(A_94, k6_partfun1(A_95)))=k10_relat_1(A_94, A_95) | ~v1_relat_1(A_94))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_372])).
% 2.97/1.43  tff(c_474, plain, (![A_29, B_30]: (k1_relat_1(k6_partfun1(k3_xboole_0(A_29, B_30)))=k10_relat_1(k6_partfun1(B_30), A_29) | ~v1_relat_1(k6_partfun1(B_30)))), inference(superposition, [status(thm), theory('equality')], [c_58, c_462])).
% 2.97/1.43  tff(c_478, plain, (![B_30, A_29]: (k10_relat_1(k6_partfun1(B_30), A_29)=k3_xboole_0(A_29, B_30))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_67, c_474])).
% 2.97/1.43  tff(c_44, plain, (![A_31]: (k2_funct_1(k6_relat_1(A_31))=k6_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.97/1.43  tff(c_57, plain, (![A_31]: (k2_funct_1(k6_partfun1(A_31))=k6_partfun1(A_31))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_52, c_44])).
% 2.97/1.43  tff(c_541, plain, (![B_102, A_103]: (k9_relat_1(k2_funct_1(B_102), A_103)=k10_relat_1(B_102, A_103) | ~v2_funct_1(B_102) | ~v1_funct_1(B_102) | ~v1_relat_1(B_102))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.97/1.43  tff(c_550, plain, (![A_31, A_103]: (k9_relat_1(k6_partfun1(A_31), A_103)=k10_relat_1(k6_partfun1(A_31), A_103) | ~v2_funct_1(k6_partfun1(A_31)) | ~v1_funct_1(k6_partfun1(A_31)) | ~v1_relat_1(k6_partfun1(A_31)))), inference(superposition, [status(thm), theory('equality')], [c_57, c_541])).
% 2.97/1.43  tff(c_554, plain, (![A_31, A_103]: (k9_relat_1(k6_partfun1(A_31), A_103)=k3_xboole_0(A_103, A_31))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_61, c_59, c_478, c_550])).
% 2.97/1.43  tff(c_24, plain, (![A_23]: (k2_relat_1(k6_relat_1(A_23))=A_23)), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.97/1.43  tff(c_66, plain, (![A_23]: (k2_relat_1(k6_partfun1(A_23))=A_23)), inference(demodulation, [status(thm), theory('equality')], [c_52, c_24])).
% 2.97/1.43  tff(c_28, plain, (![A_24]: (v4_relat_1(k6_relat_1(A_24), A_24))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.97/1.43  tff(c_64, plain, (![A_24]: (v4_relat_1(k6_partfun1(A_24), A_24))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_28])).
% 2.97/1.43  tff(c_297, plain, (![C_75, B_76, A_77]: (v4_relat_1(C_75, B_76) | ~v4_relat_1(C_75, A_77) | ~v1_relat_1(C_75) | ~r1_tarski(A_77, B_76))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.97/1.43  tff(c_299, plain, (![A_24, B_76]: (v4_relat_1(k6_partfun1(A_24), B_76) | ~v1_relat_1(k6_partfun1(A_24)) | ~r1_tarski(A_24, B_76))), inference(resolution, [status(thm)], [c_64, c_297])).
% 2.97/1.43  tff(c_303, plain, (![A_78, B_79]: (v4_relat_1(k6_partfun1(A_78), B_79) | ~r1_tarski(A_78, B_79))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_299])).
% 2.97/1.43  tff(c_18, plain, (![B_18, A_17]: (k7_relat_1(B_18, A_17)=B_18 | ~v4_relat_1(B_18, A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.97/1.43  tff(c_308, plain, (![A_78, B_79]: (k7_relat_1(k6_partfun1(A_78), B_79)=k6_partfun1(A_78) | ~v1_relat_1(k6_partfun1(A_78)) | ~r1_tarski(A_78, B_79))), inference(resolution, [status(thm)], [c_303, c_18])).
% 2.97/1.43  tff(c_315, plain, (![A_80, B_81]: (k7_relat_1(k6_partfun1(A_80), B_81)=k6_partfun1(A_80) | ~r1_tarski(A_80, B_81))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_308])).
% 2.97/1.43  tff(c_14, plain, (![B_13, A_12]: (k2_relat_1(k7_relat_1(B_13, A_12))=k9_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.97/1.43  tff(c_321, plain, (![A_80, B_81]: (k9_relat_1(k6_partfun1(A_80), B_81)=k2_relat_1(k6_partfun1(A_80)) | ~v1_relat_1(k6_partfun1(A_80)) | ~r1_tarski(A_80, B_81))), inference(superposition, [status(thm), theory('equality')], [c_315, c_14])).
% 2.97/1.43  tff(c_334, plain, (![A_80, B_81]: (k9_relat_1(k6_partfun1(A_80), B_81)=A_80 | ~r1_tarski(A_80, B_81))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_66, c_321])).
% 2.97/1.43  tff(c_623, plain, (![B_109, A_110]: (k3_xboole_0(B_109, A_110)=A_110 | ~r1_tarski(A_110, B_109))), inference(demodulation, [status(thm), theory('equality')], [c_554, c_334])).
% 2.97/1.43  tff(c_631, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_176, c_623])).
% 2.97/1.43  tff(c_2, plain, (![B_2, A_1]: (k2_tarski(B_2, A_1)=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.97/1.43  tff(c_143, plain, (![A_50, B_51]: (k1_setfam_1(k2_tarski(A_50, B_51))=k3_xboole_0(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.97/1.43  tff(c_183, plain, (![A_60, B_61]: (k1_setfam_1(k2_tarski(A_60, B_61))=k3_xboole_0(B_61, A_60))), inference(superposition, [status(thm), theory('equality')], [c_2, c_143])).
% 2.97/1.43  tff(c_8, plain, (![A_8, B_9]: (k1_setfam_1(k2_tarski(A_8, B_9))=k3_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.97/1.43  tff(c_189, plain, (![B_61, A_60]: (k3_xboole_0(B_61, A_60)=k3_xboole_0(A_60, B_61))), inference(superposition, [status(thm), theory('equality')], [c_183, c_8])).
% 2.97/1.43  tff(c_50, plain, (![A_36]: (m1_subset_1(k6_partfun1(A_36), k1_zfmisc_1(k2_zfmisc_1(A_36, A_36))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.97/1.43  tff(c_667, plain, (![A_114, B_115, C_116, D_117]: (k8_relset_1(A_114, B_115, C_116, D_117)=k10_relat_1(C_116, D_117) | ~m1_subset_1(C_116, k1_zfmisc_1(k2_zfmisc_1(A_114, B_115))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.97/1.43  tff(c_672, plain, (![A_36, D_117]: (k8_relset_1(A_36, A_36, k6_partfun1(A_36), D_117)=k10_relat_1(k6_partfun1(A_36), D_117))), inference(resolution, [status(thm)], [c_50, c_667])).
% 2.97/1.43  tff(c_675, plain, (![A_36, D_117]: (k8_relset_1(A_36, A_36, k6_partfun1(A_36), D_117)=k3_xboole_0(D_117, A_36))), inference(demodulation, [status(thm), theory('equality')], [c_478, c_672])).
% 2.97/1.43  tff(c_54, plain, (k8_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.97/1.43  tff(c_686, plain, (k3_xboole_0('#skF_2', '#skF_1')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_675, c_54])).
% 2.97/1.43  tff(c_689, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_631, c_189, c_686])).
% 2.97/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.97/1.43  
% 2.97/1.43  Inference rules
% 2.97/1.43  ----------------------
% 2.97/1.43  #Ref     : 0
% 2.97/1.43  #Sup     : 135
% 2.97/1.43  #Fact    : 0
% 2.97/1.43  #Define  : 0
% 2.97/1.43  #Split   : 0
% 2.97/1.43  #Chain   : 0
% 2.97/1.43  #Close   : 0
% 2.97/1.43  
% 2.97/1.43  Ordering : KBO
% 2.97/1.43  
% 2.97/1.43  Simplification rules
% 2.97/1.43  ----------------------
% 2.97/1.43  #Subsume      : 3
% 2.97/1.43  #Demod        : 68
% 2.97/1.43  #Tautology    : 101
% 2.97/1.43  #SimpNegUnit  : 0
% 2.97/1.43  #BackRed      : 3
% 2.97/1.43  
% 2.97/1.43  #Partial instantiations: 0
% 2.97/1.43  #Strategies tried      : 1
% 2.97/1.43  
% 2.97/1.43  Timing (in seconds)
% 2.97/1.43  ----------------------
% 2.97/1.43  Preprocessing        : 0.35
% 2.97/1.43  Parsing              : 0.20
% 2.97/1.43  CNF conversion       : 0.02
% 2.97/1.43  Main loop            : 0.29
% 2.97/1.43  Inferencing          : 0.11
% 2.97/1.43  Reduction            : 0.10
% 2.97/1.43  Demodulation         : 0.08
% 2.97/1.43  BG Simplification    : 0.02
% 2.97/1.43  Subsumption          : 0.04
% 2.97/1.43  Abstraction          : 0.02
% 2.97/1.43  MUC search           : 0.00
% 2.97/1.44  Cooper               : 0.00
% 2.97/1.44  Total                : 0.67
% 2.97/1.44  Index Insertion      : 0.00
% 2.97/1.44  Index Deletion       : 0.00
% 2.97/1.44  Index Matching       : 0.00
% 2.97/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
