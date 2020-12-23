%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:12 EST 2020

% Result     : Theorem 2.67s
% Output     : CNFRefutation 2.67s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 190 expanded)
%              Number of leaves         :   47 (  87 expanded)
%              Depth                    :   11
%              Number of atoms          :  119 ( 231 expanded)
%              Number of equality atoms :   48 ( 121 expanded)
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

tff(f_106,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k8_relset_1(A,A,k6_partfun1(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_funct_2)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_101,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_81,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_77,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_67,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_91,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_93,axiom,(
    ! [A] : k2_funct_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k10_relat_1(B,A) = k9_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_funct_1)).

tff(f_73,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v4_relat_1(k6_relat_1(A),A)
      & v5_relat_1(k6_relat_1(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc24_relat_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ! [C] :
          ( ( v1_relat_1(C)
            & v4_relat_1(C,A) )
         => v4_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t217_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_33,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_99,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_97,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(c_54,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_157,plain,(
    ! [A_52,B_53] :
      ( r1_tarski(A_52,B_53)
      | ~ m1_subset_1(A_52,k1_zfmisc_1(B_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_165,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_157])).

tff(c_50,plain,(
    ! [A_37] : k6_relat_1(A_37) = k6_partfun1(A_37) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_36,plain,(
    ! [A_26] : v1_relat_1(k6_relat_1(A_26)) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_59,plain,(
    ! [A_26] : v1_relat_1(k6_partfun1(A_26)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_36])).

tff(c_34,plain,(
    ! [A_25] : v1_funct_1(k6_relat_1(A_25)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_60,plain,(
    ! [A_25] : v1_funct_1(k6_partfun1(A_25)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_34])).

tff(c_38,plain,(
    ! [A_26] : v2_funct_1(k6_relat_1(A_26)) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_58,plain,(
    ! [A_26] : v2_funct_1(k6_partfun1(A_26)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_38])).

tff(c_22,plain,(
    ! [A_23] : k1_relat_1(k6_relat_1(A_23)) = A_23 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_66,plain,(
    ! [A_23] : k1_relat_1(k6_partfun1(A_23)) = A_23 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_22])).

tff(c_42,plain,(
    ! [B_30,A_29] : k5_relat_1(k6_relat_1(B_30),k6_relat_1(A_29)) = k6_relat_1(k3_xboole_0(A_29,B_30)) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_57,plain,(
    ! [B_30,A_29] : k5_relat_1(k6_partfun1(B_30),k6_partfun1(A_29)) = k6_partfun1(k3_xboole_0(A_29,B_30)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_50,c_50,c_42])).

tff(c_373,plain,(
    ! [A_87,B_88] :
      ( k10_relat_1(A_87,k1_relat_1(B_88)) = k1_relat_1(k5_relat_1(A_87,B_88))
      | ~ v1_relat_1(B_88)
      | ~ v1_relat_1(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_382,plain,(
    ! [A_87,A_23] :
      ( k1_relat_1(k5_relat_1(A_87,k6_partfun1(A_23))) = k10_relat_1(A_87,A_23)
      | ~ v1_relat_1(k6_partfun1(A_23))
      | ~ v1_relat_1(A_87) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_373])).

tff(c_448,plain,(
    ! [A_91,A_92] :
      ( k1_relat_1(k5_relat_1(A_91,k6_partfun1(A_92))) = k10_relat_1(A_91,A_92)
      | ~ v1_relat_1(A_91) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_382])).

tff(c_460,plain,(
    ! [A_29,B_30] :
      ( k1_relat_1(k6_partfun1(k3_xboole_0(A_29,B_30))) = k10_relat_1(k6_partfun1(B_30),A_29)
      | ~ v1_relat_1(k6_partfun1(B_30)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_448])).

tff(c_464,plain,(
    ! [B_30,A_29] : k10_relat_1(k6_partfun1(B_30),A_29) = k3_xboole_0(A_29,B_30) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_66,c_460])).

tff(c_44,plain,(
    ! [A_31] : k2_funct_1(k6_relat_1(A_31)) = k6_relat_1(A_31) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_56,plain,(
    ! [A_31] : k2_funct_1(k6_partfun1(A_31)) = k6_partfun1(A_31) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_50,c_44])).

tff(c_572,plain,(
    ! [B_103,A_104] :
      ( k9_relat_1(k2_funct_1(B_103),A_104) = k10_relat_1(B_103,A_104)
      | ~ v2_funct_1(B_103)
      | ~ v1_funct_1(B_103)
      | ~ v1_relat_1(B_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_581,plain,(
    ! [A_31,A_104] :
      ( k9_relat_1(k6_partfun1(A_31),A_104) = k10_relat_1(k6_partfun1(A_31),A_104)
      | ~ v2_funct_1(k6_partfun1(A_31))
      | ~ v1_funct_1(k6_partfun1(A_31))
      | ~ v1_relat_1(k6_partfun1(A_31)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_572])).

tff(c_585,plain,(
    ! [A_31,A_104] : k9_relat_1(k6_partfun1(A_31),A_104) = k3_xboole_0(A_104,A_31) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_60,c_58,c_464,c_581])).

tff(c_24,plain,(
    ! [A_23] : k2_relat_1(k6_relat_1(A_23)) = A_23 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_65,plain,(
    ! [A_23] : k2_relat_1(k6_partfun1(A_23)) = A_23 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_24])).

tff(c_28,plain,(
    ! [A_24] : v4_relat_1(k6_relat_1(A_24),A_24) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_63,plain,(
    ! [A_24] : v4_relat_1(k6_partfun1(A_24),A_24) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_28])).

tff(c_295,plain,(
    ! [C_74,B_75,A_76] :
      ( v4_relat_1(C_74,B_75)
      | ~ v4_relat_1(C_74,A_76)
      | ~ v1_relat_1(C_74)
      | ~ r1_tarski(A_76,B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_297,plain,(
    ! [A_24,B_75] :
      ( v4_relat_1(k6_partfun1(A_24),B_75)
      | ~ v1_relat_1(k6_partfun1(A_24))
      | ~ r1_tarski(A_24,B_75) ) ),
    inference(resolution,[status(thm)],[c_63,c_295])).

tff(c_301,plain,(
    ! [A_77,B_78] :
      ( v4_relat_1(k6_partfun1(A_77),B_78)
      | ~ r1_tarski(A_77,B_78) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_297])).

tff(c_18,plain,(
    ! [B_18,A_17] :
      ( k7_relat_1(B_18,A_17) = B_18
      | ~ v4_relat_1(B_18,A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_306,plain,(
    ! [A_77,B_78] :
      ( k7_relat_1(k6_partfun1(A_77),B_78) = k6_partfun1(A_77)
      | ~ v1_relat_1(k6_partfun1(A_77))
      | ~ r1_tarski(A_77,B_78) ) ),
    inference(resolution,[status(thm)],[c_301,c_18])).

tff(c_313,plain,(
    ! [A_79,B_80] :
      ( k7_relat_1(k6_partfun1(A_79),B_80) = k6_partfun1(A_79)
      | ~ r1_tarski(A_79,B_80) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_306])).

tff(c_14,plain,(
    ! [B_13,A_12] :
      ( k2_relat_1(k7_relat_1(B_13,A_12)) = k9_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_323,plain,(
    ! [A_79,B_80] :
      ( k9_relat_1(k6_partfun1(A_79),B_80) = k2_relat_1(k6_partfun1(A_79))
      | ~ v1_relat_1(k6_partfun1(A_79))
      | ~ r1_tarski(A_79,B_80) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_313,c_14])).

tff(c_333,plain,(
    ! [A_79,B_80] :
      ( k9_relat_1(k6_partfun1(A_79),B_80) = A_79
      | ~ r1_tarski(A_79,B_80) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_65,c_323])).

tff(c_663,plain,(
    ! [B_110,A_111] :
      ( k3_xboole_0(B_110,A_111) = A_111
      | ~ r1_tarski(A_111,B_110) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_585,c_333])).

tff(c_671,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_165,c_663])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_tarski(B_2,A_1) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_142,plain,(
    ! [A_50,B_51] : k1_setfam_1(k2_tarski(A_50,B_51)) = k3_xboole_0(A_50,B_51) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_190,plain,(
    ! [B_62,A_63] : k1_setfam_1(k2_tarski(B_62,A_63)) = k3_xboole_0(A_63,B_62) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_142])).

tff(c_8,plain,(
    ! [A_8,B_9] : k1_setfam_1(k2_tarski(A_8,B_9)) = k3_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_196,plain,(
    ! [B_62,A_63] : k3_xboole_0(B_62,A_63) = k3_xboole_0(A_63,B_62) ),
    inference(superposition,[status(thm),theory(equality)],[c_190,c_8])).

tff(c_48,plain,(
    ! [A_36] : m1_subset_1(k6_relat_1(A_36),k1_zfmisc_1(k2_zfmisc_1(A_36,A_36))) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_55,plain,(
    ! [A_36] : m1_subset_1(k6_partfun1(A_36),k1_zfmisc_1(k2_zfmisc_1(A_36,A_36))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48])).

tff(c_707,plain,(
    ! [A_115,B_116,C_117,D_118] :
      ( k8_relset_1(A_115,B_116,C_117,D_118) = k10_relat_1(C_117,D_118)
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1(A_115,B_116))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_712,plain,(
    ! [A_36,D_118] : k8_relset_1(A_36,A_36,k6_partfun1(A_36),D_118) = k10_relat_1(k6_partfun1(A_36),D_118) ),
    inference(resolution,[status(thm)],[c_55,c_707])).

tff(c_715,plain,(
    ! [A_36,D_118] : k8_relset_1(A_36,A_36,k6_partfun1(A_36),D_118) = k3_xboole_0(D_118,A_36) ),
    inference(demodulation,[status(thm),theory(equality)],[c_464,c_712])).

tff(c_52,plain,(
    k8_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_726,plain,(
    k3_xboole_0('#skF_2','#skF_1') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_715,c_52])).

tff(c_729,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_671,c_196,c_726])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n016.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:18:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.67/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.67/1.34  
% 2.67/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.67/1.34  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.67/1.34  
% 2.67/1.34  %Foreground sorts:
% 2.67/1.34  
% 2.67/1.34  
% 2.67/1.34  %Background operators:
% 2.67/1.34  
% 2.67/1.34  
% 2.67/1.34  %Foreground operators:
% 2.67/1.34  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.67/1.34  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.67/1.34  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.67/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.67/1.34  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.67/1.34  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.67/1.34  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.67/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.67/1.34  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.67/1.34  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.67/1.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.67/1.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.67/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.67/1.34  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.67/1.34  tff('#skF_1', type, '#skF_1': $i).
% 2.67/1.34  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.67/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.67/1.34  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.67/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.67/1.34  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.67/1.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.67/1.34  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.67/1.34  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.67/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.67/1.34  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.67/1.34  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.67/1.34  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.67/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.67/1.34  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.67/1.34  
% 2.67/1.36  tff(f_106, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k8_relset_1(A, A, k6_partfun1(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t171_funct_2)).
% 2.67/1.36  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.67/1.36  tff(f_101, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.67/1.36  tff(f_81, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 2.67/1.36  tff(f_77, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.67/1.36  tff(f_67, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.67/1.36  tff(f_91, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 2.67/1.36  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 2.67/1.36  tff(f_93, axiom, (![A]: (k2_funct_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_funct_1)).
% 2.67/1.36  tff(f_89, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k10_relat_1(B, A) = k9_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t155_funct_1)).
% 2.67/1.36  tff(f_73, axiom, (![A]: ((v1_relat_1(k6_relat_1(A)) & v4_relat_1(k6_relat_1(A), A)) & v5_relat_1(k6_relat_1(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc24_relat_1)).
% 2.67/1.36  tff(f_63, axiom, (![A, B]: (r1_tarski(A, B) => (![C]: ((v1_relat_1(C) & v4_relat_1(C, A)) => v4_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t217_relat_1)).
% 2.67/1.36  tff(f_54, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 2.67/1.36  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 2.67/1.36  tff(f_27, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.67/1.36  tff(f_33, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.67/1.36  tff(f_99, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 2.67/1.36  tff(f_97, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.67/1.36  tff(c_54, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.67/1.36  tff(c_157, plain, (![A_52, B_53]: (r1_tarski(A_52, B_53) | ~m1_subset_1(A_52, k1_zfmisc_1(B_53)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.67/1.36  tff(c_165, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_54, c_157])).
% 2.67/1.36  tff(c_50, plain, (![A_37]: (k6_relat_1(A_37)=k6_partfun1(A_37))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.67/1.36  tff(c_36, plain, (![A_26]: (v1_relat_1(k6_relat_1(A_26)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.67/1.36  tff(c_59, plain, (![A_26]: (v1_relat_1(k6_partfun1(A_26)))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_36])).
% 2.67/1.36  tff(c_34, plain, (![A_25]: (v1_funct_1(k6_relat_1(A_25)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.67/1.36  tff(c_60, plain, (![A_25]: (v1_funct_1(k6_partfun1(A_25)))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_34])).
% 2.67/1.36  tff(c_38, plain, (![A_26]: (v2_funct_1(k6_relat_1(A_26)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.67/1.36  tff(c_58, plain, (![A_26]: (v2_funct_1(k6_partfun1(A_26)))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_38])).
% 2.67/1.36  tff(c_22, plain, (![A_23]: (k1_relat_1(k6_relat_1(A_23))=A_23)), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.67/1.36  tff(c_66, plain, (![A_23]: (k1_relat_1(k6_partfun1(A_23))=A_23)), inference(demodulation, [status(thm), theory('equality')], [c_50, c_22])).
% 2.67/1.36  tff(c_42, plain, (![B_30, A_29]: (k5_relat_1(k6_relat_1(B_30), k6_relat_1(A_29))=k6_relat_1(k3_xboole_0(A_29, B_30)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.67/1.36  tff(c_57, plain, (![B_30, A_29]: (k5_relat_1(k6_partfun1(B_30), k6_partfun1(A_29))=k6_partfun1(k3_xboole_0(A_29, B_30)))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_50, c_50, c_42])).
% 2.67/1.36  tff(c_373, plain, (![A_87, B_88]: (k10_relat_1(A_87, k1_relat_1(B_88))=k1_relat_1(k5_relat_1(A_87, B_88)) | ~v1_relat_1(B_88) | ~v1_relat_1(A_87))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.67/1.36  tff(c_382, plain, (![A_87, A_23]: (k1_relat_1(k5_relat_1(A_87, k6_partfun1(A_23)))=k10_relat_1(A_87, A_23) | ~v1_relat_1(k6_partfun1(A_23)) | ~v1_relat_1(A_87))), inference(superposition, [status(thm), theory('equality')], [c_66, c_373])).
% 2.67/1.36  tff(c_448, plain, (![A_91, A_92]: (k1_relat_1(k5_relat_1(A_91, k6_partfun1(A_92)))=k10_relat_1(A_91, A_92) | ~v1_relat_1(A_91))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_382])).
% 2.67/1.36  tff(c_460, plain, (![A_29, B_30]: (k1_relat_1(k6_partfun1(k3_xboole_0(A_29, B_30)))=k10_relat_1(k6_partfun1(B_30), A_29) | ~v1_relat_1(k6_partfun1(B_30)))), inference(superposition, [status(thm), theory('equality')], [c_57, c_448])).
% 2.67/1.36  tff(c_464, plain, (![B_30, A_29]: (k10_relat_1(k6_partfun1(B_30), A_29)=k3_xboole_0(A_29, B_30))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_66, c_460])).
% 2.67/1.36  tff(c_44, plain, (![A_31]: (k2_funct_1(k6_relat_1(A_31))=k6_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.67/1.36  tff(c_56, plain, (![A_31]: (k2_funct_1(k6_partfun1(A_31))=k6_partfun1(A_31))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_50, c_44])).
% 2.67/1.36  tff(c_572, plain, (![B_103, A_104]: (k9_relat_1(k2_funct_1(B_103), A_104)=k10_relat_1(B_103, A_104) | ~v2_funct_1(B_103) | ~v1_funct_1(B_103) | ~v1_relat_1(B_103))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.67/1.36  tff(c_581, plain, (![A_31, A_104]: (k9_relat_1(k6_partfun1(A_31), A_104)=k10_relat_1(k6_partfun1(A_31), A_104) | ~v2_funct_1(k6_partfun1(A_31)) | ~v1_funct_1(k6_partfun1(A_31)) | ~v1_relat_1(k6_partfun1(A_31)))), inference(superposition, [status(thm), theory('equality')], [c_56, c_572])).
% 2.67/1.36  tff(c_585, plain, (![A_31, A_104]: (k9_relat_1(k6_partfun1(A_31), A_104)=k3_xboole_0(A_104, A_31))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_60, c_58, c_464, c_581])).
% 2.67/1.36  tff(c_24, plain, (![A_23]: (k2_relat_1(k6_relat_1(A_23))=A_23)), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.67/1.36  tff(c_65, plain, (![A_23]: (k2_relat_1(k6_partfun1(A_23))=A_23)), inference(demodulation, [status(thm), theory('equality')], [c_50, c_24])).
% 2.67/1.36  tff(c_28, plain, (![A_24]: (v4_relat_1(k6_relat_1(A_24), A_24))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.67/1.36  tff(c_63, plain, (![A_24]: (v4_relat_1(k6_partfun1(A_24), A_24))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_28])).
% 2.67/1.36  tff(c_295, plain, (![C_74, B_75, A_76]: (v4_relat_1(C_74, B_75) | ~v4_relat_1(C_74, A_76) | ~v1_relat_1(C_74) | ~r1_tarski(A_76, B_75))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.67/1.36  tff(c_297, plain, (![A_24, B_75]: (v4_relat_1(k6_partfun1(A_24), B_75) | ~v1_relat_1(k6_partfun1(A_24)) | ~r1_tarski(A_24, B_75))), inference(resolution, [status(thm)], [c_63, c_295])).
% 2.67/1.36  tff(c_301, plain, (![A_77, B_78]: (v4_relat_1(k6_partfun1(A_77), B_78) | ~r1_tarski(A_77, B_78))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_297])).
% 2.67/1.36  tff(c_18, plain, (![B_18, A_17]: (k7_relat_1(B_18, A_17)=B_18 | ~v4_relat_1(B_18, A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.67/1.36  tff(c_306, plain, (![A_77, B_78]: (k7_relat_1(k6_partfun1(A_77), B_78)=k6_partfun1(A_77) | ~v1_relat_1(k6_partfun1(A_77)) | ~r1_tarski(A_77, B_78))), inference(resolution, [status(thm)], [c_301, c_18])).
% 2.67/1.36  tff(c_313, plain, (![A_79, B_80]: (k7_relat_1(k6_partfun1(A_79), B_80)=k6_partfun1(A_79) | ~r1_tarski(A_79, B_80))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_306])).
% 2.67/1.36  tff(c_14, plain, (![B_13, A_12]: (k2_relat_1(k7_relat_1(B_13, A_12))=k9_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.67/1.36  tff(c_323, plain, (![A_79, B_80]: (k9_relat_1(k6_partfun1(A_79), B_80)=k2_relat_1(k6_partfun1(A_79)) | ~v1_relat_1(k6_partfun1(A_79)) | ~r1_tarski(A_79, B_80))), inference(superposition, [status(thm), theory('equality')], [c_313, c_14])).
% 2.67/1.36  tff(c_333, plain, (![A_79, B_80]: (k9_relat_1(k6_partfun1(A_79), B_80)=A_79 | ~r1_tarski(A_79, B_80))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_65, c_323])).
% 2.67/1.36  tff(c_663, plain, (![B_110, A_111]: (k3_xboole_0(B_110, A_111)=A_111 | ~r1_tarski(A_111, B_110))), inference(demodulation, [status(thm), theory('equality')], [c_585, c_333])).
% 2.67/1.36  tff(c_671, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_165, c_663])).
% 2.67/1.36  tff(c_2, plain, (![B_2, A_1]: (k2_tarski(B_2, A_1)=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.67/1.36  tff(c_142, plain, (![A_50, B_51]: (k1_setfam_1(k2_tarski(A_50, B_51))=k3_xboole_0(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.67/1.36  tff(c_190, plain, (![B_62, A_63]: (k1_setfam_1(k2_tarski(B_62, A_63))=k3_xboole_0(A_63, B_62))), inference(superposition, [status(thm), theory('equality')], [c_2, c_142])).
% 2.67/1.36  tff(c_8, plain, (![A_8, B_9]: (k1_setfam_1(k2_tarski(A_8, B_9))=k3_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.67/1.36  tff(c_196, plain, (![B_62, A_63]: (k3_xboole_0(B_62, A_63)=k3_xboole_0(A_63, B_62))), inference(superposition, [status(thm), theory('equality')], [c_190, c_8])).
% 2.67/1.36  tff(c_48, plain, (![A_36]: (m1_subset_1(k6_relat_1(A_36), k1_zfmisc_1(k2_zfmisc_1(A_36, A_36))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.67/1.36  tff(c_55, plain, (![A_36]: (m1_subset_1(k6_partfun1(A_36), k1_zfmisc_1(k2_zfmisc_1(A_36, A_36))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48])).
% 2.67/1.36  tff(c_707, plain, (![A_115, B_116, C_117, D_118]: (k8_relset_1(A_115, B_116, C_117, D_118)=k10_relat_1(C_117, D_118) | ~m1_subset_1(C_117, k1_zfmisc_1(k2_zfmisc_1(A_115, B_116))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.67/1.36  tff(c_712, plain, (![A_36, D_118]: (k8_relset_1(A_36, A_36, k6_partfun1(A_36), D_118)=k10_relat_1(k6_partfun1(A_36), D_118))), inference(resolution, [status(thm)], [c_55, c_707])).
% 2.67/1.36  tff(c_715, plain, (![A_36, D_118]: (k8_relset_1(A_36, A_36, k6_partfun1(A_36), D_118)=k3_xboole_0(D_118, A_36))), inference(demodulation, [status(thm), theory('equality')], [c_464, c_712])).
% 2.67/1.36  tff(c_52, plain, (k8_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.67/1.36  tff(c_726, plain, (k3_xboole_0('#skF_2', '#skF_1')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_715, c_52])).
% 2.67/1.36  tff(c_729, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_671, c_196, c_726])).
% 2.67/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.67/1.36  
% 2.67/1.36  Inference rules
% 2.67/1.36  ----------------------
% 2.67/1.36  #Ref     : 0
% 2.67/1.36  #Sup     : 144
% 2.67/1.36  #Fact    : 0
% 2.67/1.36  #Define  : 0
% 2.67/1.36  #Split   : 0
% 2.67/1.36  #Chain   : 0
% 2.67/1.36  #Close   : 0
% 2.67/1.36  
% 2.67/1.36  Ordering : KBO
% 2.67/1.36  
% 2.67/1.36  Simplification rules
% 2.67/1.36  ----------------------
% 2.67/1.36  #Subsume      : 3
% 2.67/1.36  #Demod        : 71
% 2.67/1.36  #Tautology    : 109
% 2.67/1.36  #SimpNegUnit  : 0
% 2.67/1.36  #BackRed      : 3
% 2.67/1.36  
% 2.67/1.36  #Partial instantiations: 0
% 2.67/1.36  #Strategies tried      : 1
% 2.67/1.36  
% 2.67/1.36  Timing (in seconds)
% 2.67/1.36  ----------------------
% 2.67/1.37  Preprocessing        : 0.32
% 2.67/1.37  Parsing              : 0.17
% 2.85/1.37  CNF conversion       : 0.02
% 2.85/1.37  Main loop            : 0.29
% 2.85/1.37  Inferencing          : 0.11
% 2.85/1.37  Reduction            : 0.10
% 2.85/1.37  Demodulation         : 0.08
% 2.85/1.37  BG Simplification    : 0.02
% 2.85/1.37  Subsumption          : 0.05
% 2.85/1.37  Abstraction          : 0.02
% 2.85/1.37  MUC search           : 0.00
% 2.85/1.37  Cooper               : 0.00
% 2.85/1.37  Total                : 0.65
% 2.85/1.37  Index Insertion      : 0.00
% 2.85/1.37  Index Deletion       : 0.00
% 2.85/1.37  Index Matching       : 0.00
% 2.85/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
