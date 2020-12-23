%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:12 EST 2020

% Result     : Theorem 2.75s
% Output     : CNFRefutation 3.04s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 201 expanded)
%              Number of leaves         :   53 (  93 expanded)
%              Depth                    :   12
%              Number of atoms          :  134 ( 246 expanded)
%              Number of equality atoms :   50 ( 123 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_118,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k8_relset_1(A,A,k6_partfun1(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_funct_2)).

tff(f_41,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_38,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_113,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_93,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_89,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_79,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_103,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_105,axiom,(
    ! [A] : k2_funct_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_1)).

tff(f_101,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k10_relat_1(B,A) = k9_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_funct_1)).

tff(f_85,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v4_relat_1(k6_relat_1(A),A)
      & v5_relat_1(k6_relat_1(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc24_relat_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ! [C] :
          ( ( v1_relat_1(C)
            & v4_relat_1(C,A) )
         => v4_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t217_relat_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_43,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_111,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_109,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(c_66,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_20,plain,(
    ! [A_13] : ~ v1_xboole_0(k1_zfmisc_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_208,plain,(
    ! [A_67,B_68] :
      ( r2_hidden(A_67,B_68)
      | v1_xboole_0(B_68)
      | ~ m1_subset_1(A_67,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_8,plain,(
    ! [C_12,A_8] :
      ( r1_tarski(C_12,A_8)
      | ~ r2_hidden(C_12,k1_zfmisc_1(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_212,plain,(
    ! [A_67,A_8] :
      ( r1_tarski(A_67,A_8)
      | v1_xboole_0(k1_zfmisc_1(A_8))
      | ~ m1_subset_1(A_67,k1_zfmisc_1(A_8)) ) ),
    inference(resolution,[status(thm)],[c_208,c_8])).

tff(c_249,plain,(
    ! [A_71,A_72] :
      ( r1_tarski(A_71,A_72)
      | ~ m1_subset_1(A_71,k1_zfmisc_1(A_72)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_212])).

tff(c_257,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_249])).

tff(c_62,plain,(
    ! [A_43] : k6_relat_1(A_43) = k6_partfun1(A_43) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_48,plain,(
    ! [A_32] : v1_relat_1(k6_relat_1(A_32)) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_71,plain,(
    ! [A_32] : v1_relat_1(k6_partfun1(A_32)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_48])).

tff(c_46,plain,(
    ! [A_31] : v1_funct_1(k6_relat_1(A_31)) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_72,plain,(
    ! [A_31] : v1_funct_1(k6_partfun1(A_31)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_46])).

tff(c_50,plain,(
    ! [A_32] : v2_funct_1(k6_relat_1(A_32)) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_70,plain,(
    ! [A_32] : v2_funct_1(k6_partfun1(A_32)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_50])).

tff(c_34,plain,(
    ! [A_29] : k1_relat_1(k6_relat_1(A_29)) = A_29 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_78,plain,(
    ! [A_29] : k1_relat_1(k6_partfun1(A_29)) = A_29 ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_34])).

tff(c_54,plain,(
    ! [B_36,A_35] : k5_relat_1(k6_relat_1(B_36),k6_relat_1(A_35)) = k6_relat_1(k3_xboole_0(A_35,B_36)) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_69,plain,(
    ! [B_36,A_35] : k5_relat_1(k6_partfun1(B_36),k6_partfun1(A_35)) = k6_partfun1(k3_xboole_0(A_35,B_36)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_62,c_62,c_54])).

tff(c_358,plain,(
    ! [A_92,B_93] :
      ( k10_relat_1(A_92,k1_relat_1(B_93)) = k1_relat_1(k5_relat_1(A_92,B_93))
      | ~ v1_relat_1(B_93)
      | ~ v1_relat_1(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_367,plain,(
    ! [A_92,A_29] :
      ( k1_relat_1(k5_relat_1(A_92,k6_partfun1(A_29))) = k10_relat_1(A_92,A_29)
      | ~ v1_relat_1(k6_partfun1(A_29))
      | ~ v1_relat_1(A_92) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_358])).

tff(c_390,plain,(
    ! [A_96,A_97] :
      ( k1_relat_1(k5_relat_1(A_96,k6_partfun1(A_97))) = k10_relat_1(A_96,A_97)
      | ~ v1_relat_1(A_96) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_367])).

tff(c_402,plain,(
    ! [A_35,B_36] :
      ( k1_relat_1(k6_partfun1(k3_xboole_0(A_35,B_36))) = k10_relat_1(k6_partfun1(B_36),A_35)
      | ~ v1_relat_1(k6_partfun1(B_36)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_390])).

tff(c_406,plain,(
    ! [B_36,A_35] : k10_relat_1(k6_partfun1(B_36),A_35) = k3_xboole_0(A_35,B_36) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_78,c_402])).

tff(c_56,plain,(
    ! [A_37] : k2_funct_1(k6_relat_1(A_37)) = k6_relat_1(A_37) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_68,plain,(
    ! [A_37] : k2_funct_1(k6_partfun1(A_37)) = k6_partfun1(A_37) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_62,c_56])).

tff(c_725,plain,(
    ! [B_124,A_125] :
      ( k9_relat_1(k2_funct_1(B_124),A_125) = k10_relat_1(B_124,A_125)
      | ~ v2_funct_1(B_124)
      | ~ v1_funct_1(B_124)
      | ~ v1_relat_1(B_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_734,plain,(
    ! [A_37,A_125] :
      ( k9_relat_1(k6_partfun1(A_37),A_125) = k10_relat_1(k6_partfun1(A_37),A_125)
      | ~ v2_funct_1(k6_partfun1(A_37))
      | ~ v1_funct_1(k6_partfun1(A_37))
      | ~ v1_relat_1(k6_partfun1(A_37)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_725])).

tff(c_738,plain,(
    ! [A_37,A_125] : k9_relat_1(k6_partfun1(A_37),A_125) = k3_xboole_0(A_125,A_37) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_72,c_70,c_406,c_734])).

tff(c_36,plain,(
    ! [A_29] : k2_relat_1(k6_relat_1(A_29)) = A_29 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_77,plain,(
    ! [A_29] : k2_relat_1(k6_partfun1(A_29)) = A_29 ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_36])).

tff(c_40,plain,(
    ! [A_30] : v4_relat_1(k6_relat_1(A_30),A_30) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_75,plain,(
    ! [A_30] : v4_relat_1(k6_partfun1(A_30),A_30) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_40])).

tff(c_317,plain,(
    ! [C_85,B_86,A_87] :
      ( v4_relat_1(C_85,B_86)
      | ~ v4_relat_1(C_85,A_87)
      | ~ v1_relat_1(C_85)
      | ~ r1_tarski(A_87,B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_319,plain,(
    ! [A_30,B_86] :
      ( v4_relat_1(k6_partfun1(A_30),B_86)
      | ~ v1_relat_1(k6_partfun1(A_30))
      | ~ r1_tarski(A_30,B_86) ) ),
    inference(resolution,[status(thm)],[c_75,c_317])).

tff(c_323,plain,(
    ! [A_88,B_89] :
      ( v4_relat_1(k6_partfun1(A_88),B_89)
      | ~ r1_tarski(A_88,B_89) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_319])).

tff(c_30,plain,(
    ! [B_24,A_23] :
      ( k7_relat_1(B_24,A_23) = B_24
      | ~ v4_relat_1(B_24,A_23)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_328,plain,(
    ! [A_88,B_89] :
      ( k7_relat_1(k6_partfun1(A_88),B_89) = k6_partfun1(A_88)
      | ~ v1_relat_1(k6_partfun1(A_88))
      | ~ r1_tarski(A_88,B_89) ) ),
    inference(resolution,[status(thm)],[c_323,c_30])).

tff(c_335,plain,(
    ! [A_90,B_91] :
      ( k7_relat_1(k6_partfun1(A_90),B_91) = k6_partfun1(A_90)
      | ~ r1_tarski(A_90,B_91) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_328])).

tff(c_26,plain,(
    ! [B_19,A_18] :
      ( k2_relat_1(k7_relat_1(B_19,A_18)) = k9_relat_1(B_19,A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_341,plain,(
    ! [A_90,B_91] :
      ( k9_relat_1(k6_partfun1(A_90),B_91) = k2_relat_1(k6_partfun1(A_90))
      | ~ v1_relat_1(k6_partfun1(A_90))
      | ~ r1_tarski(A_90,B_91) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_335,c_26])).

tff(c_354,plain,(
    ! [A_90,B_91] :
      ( k9_relat_1(k6_partfun1(A_90),B_91) = A_90
      | ~ r1_tarski(A_90,B_91) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_77,c_341])).

tff(c_775,plain,(
    ! [B_131,A_132] :
      ( k3_xboole_0(B_131,A_132) = A_132
      | ~ r1_tarski(A_132,B_131) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_738,c_354])).

tff(c_787,plain,(
    k3_xboole_0('#skF_3','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_257,c_775])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_tarski(B_2,A_1) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_164,plain,(
    ! [A_59,B_60] : k1_setfam_1(k2_tarski(A_59,B_60)) = k3_xboole_0(A_59,B_60) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_185,plain,(
    ! [B_65,A_66] : k1_setfam_1(k2_tarski(B_65,A_66)) = k3_xboole_0(A_66,B_65) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_164])).

tff(c_22,plain,(
    ! [A_14,B_15] : k1_setfam_1(k2_tarski(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_191,plain,(
    ! [B_65,A_66] : k3_xboole_0(B_65,A_66) = k3_xboole_0(A_66,B_65) ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_22])).

tff(c_791,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_787,c_191])).

tff(c_60,plain,(
    ! [A_42] : m1_subset_1(k6_relat_1(A_42),k1_zfmisc_1(k2_zfmisc_1(A_42,A_42))) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_67,plain,(
    ! [A_42] : m1_subset_1(k6_partfun1(A_42),k1_zfmisc_1(k2_zfmisc_1(A_42,A_42))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60])).

tff(c_873,plain,(
    ! [A_148,B_149,C_150,D_151] :
      ( k8_relset_1(A_148,B_149,C_150,D_151) = k10_relat_1(C_150,D_151)
      | ~ m1_subset_1(C_150,k1_zfmisc_1(k2_zfmisc_1(A_148,B_149))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_875,plain,(
    ! [A_42,D_151] : k8_relset_1(A_42,A_42,k6_partfun1(A_42),D_151) = k10_relat_1(k6_partfun1(A_42),D_151) ),
    inference(resolution,[status(thm)],[c_67,c_873])).

tff(c_877,plain,(
    ! [A_42,D_151] : k8_relset_1(A_42,A_42,k6_partfun1(A_42),D_151) = k3_xboole_0(D_151,A_42) ),
    inference(demodulation,[status(thm),theory(equality)],[c_406,c_875])).

tff(c_64,plain,(
    k8_relset_1('#skF_3','#skF_3',k6_partfun1('#skF_3'),'#skF_4') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_878,plain,(
    k3_xboole_0('#skF_4','#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_877,c_64])).

tff(c_881,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_791,c_878])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n008.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 18:06:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.75/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.04/1.43  
% 3.04/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.04/1.43  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.04/1.43  
% 3.04/1.43  %Foreground sorts:
% 3.04/1.43  
% 3.04/1.43  
% 3.04/1.43  %Background operators:
% 3.04/1.43  
% 3.04/1.43  
% 3.04/1.43  %Foreground operators:
% 3.04/1.43  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.04/1.43  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.04/1.43  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.04/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.04/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.04/1.43  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.04/1.43  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.04/1.43  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.04/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.04/1.43  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.04/1.43  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.04/1.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.04/1.43  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.04/1.43  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.04/1.43  tff('#skF_3', type, '#skF_3': $i).
% 3.04/1.43  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.04/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.04/1.43  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 3.04/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.04/1.43  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.04/1.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.04/1.43  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.04/1.43  tff('#skF_4', type, '#skF_4': $i).
% 3.04/1.43  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.04/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.04/1.43  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.04/1.43  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.04/1.43  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.04/1.43  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.04/1.43  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.04/1.43  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.04/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.04/1.43  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.04/1.43  
% 3.04/1.45  tff(f_118, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k8_relset_1(A, A, k6_partfun1(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t171_funct_2)).
% 3.04/1.45  tff(f_41, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 3.04/1.45  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.04/1.45  tff(f_38, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.04/1.45  tff(f_113, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 3.04/1.45  tff(f_93, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 3.04/1.45  tff(f_89, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 3.04/1.45  tff(f_79, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 3.04/1.45  tff(f_103, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 3.04/1.45  tff(f_60, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 3.04/1.45  tff(f_105, axiom, (![A]: (k2_funct_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_funct_1)).
% 3.04/1.45  tff(f_101, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k10_relat_1(B, A) = k9_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t155_funct_1)).
% 3.04/1.45  tff(f_85, axiom, (![A]: ((v1_relat_1(k6_relat_1(A)) & v4_relat_1(k6_relat_1(A), A)) & v5_relat_1(k6_relat_1(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc24_relat_1)).
% 3.04/1.45  tff(f_75, axiom, (![A, B]: (r1_tarski(A, B) => (![C]: ((v1_relat_1(C) & v4_relat_1(C, A)) => v4_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t217_relat_1)).
% 3.04/1.45  tff(f_66, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 3.04/1.45  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 3.04/1.45  tff(f_27, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.04/1.45  tff(f_43, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.04/1.45  tff(f_111, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 3.04/1.45  tff(f_109, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.04/1.45  tff(c_66, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.04/1.45  tff(c_20, plain, (![A_13]: (~v1_xboole_0(k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.04/1.45  tff(c_208, plain, (![A_67, B_68]: (r2_hidden(A_67, B_68) | v1_xboole_0(B_68) | ~m1_subset_1(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.04/1.45  tff(c_8, plain, (![C_12, A_8]: (r1_tarski(C_12, A_8) | ~r2_hidden(C_12, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.04/1.45  tff(c_212, plain, (![A_67, A_8]: (r1_tarski(A_67, A_8) | v1_xboole_0(k1_zfmisc_1(A_8)) | ~m1_subset_1(A_67, k1_zfmisc_1(A_8)))), inference(resolution, [status(thm)], [c_208, c_8])).
% 3.04/1.45  tff(c_249, plain, (![A_71, A_72]: (r1_tarski(A_71, A_72) | ~m1_subset_1(A_71, k1_zfmisc_1(A_72)))), inference(negUnitSimplification, [status(thm)], [c_20, c_212])).
% 3.04/1.45  tff(c_257, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_66, c_249])).
% 3.04/1.45  tff(c_62, plain, (![A_43]: (k6_relat_1(A_43)=k6_partfun1(A_43))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.04/1.45  tff(c_48, plain, (![A_32]: (v1_relat_1(k6_relat_1(A_32)))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.04/1.45  tff(c_71, plain, (![A_32]: (v1_relat_1(k6_partfun1(A_32)))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_48])).
% 3.04/1.45  tff(c_46, plain, (![A_31]: (v1_funct_1(k6_relat_1(A_31)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.04/1.45  tff(c_72, plain, (![A_31]: (v1_funct_1(k6_partfun1(A_31)))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_46])).
% 3.04/1.45  tff(c_50, plain, (![A_32]: (v2_funct_1(k6_relat_1(A_32)))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.04/1.45  tff(c_70, plain, (![A_32]: (v2_funct_1(k6_partfun1(A_32)))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_50])).
% 3.04/1.45  tff(c_34, plain, (![A_29]: (k1_relat_1(k6_relat_1(A_29))=A_29)), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.04/1.45  tff(c_78, plain, (![A_29]: (k1_relat_1(k6_partfun1(A_29))=A_29)), inference(demodulation, [status(thm), theory('equality')], [c_62, c_34])).
% 3.04/1.45  tff(c_54, plain, (![B_36, A_35]: (k5_relat_1(k6_relat_1(B_36), k6_relat_1(A_35))=k6_relat_1(k3_xboole_0(A_35, B_36)))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.04/1.45  tff(c_69, plain, (![B_36, A_35]: (k5_relat_1(k6_partfun1(B_36), k6_partfun1(A_35))=k6_partfun1(k3_xboole_0(A_35, B_36)))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_62, c_62, c_54])).
% 3.04/1.45  tff(c_358, plain, (![A_92, B_93]: (k10_relat_1(A_92, k1_relat_1(B_93))=k1_relat_1(k5_relat_1(A_92, B_93)) | ~v1_relat_1(B_93) | ~v1_relat_1(A_92))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.04/1.45  tff(c_367, plain, (![A_92, A_29]: (k1_relat_1(k5_relat_1(A_92, k6_partfun1(A_29)))=k10_relat_1(A_92, A_29) | ~v1_relat_1(k6_partfun1(A_29)) | ~v1_relat_1(A_92))), inference(superposition, [status(thm), theory('equality')], [c_78, c_358])).
% 3.04/1.45  tff(c_390, plain, (![A_96, A_97]: (k1_relat_1(k5_relat_1(A_96, k6_partfun1(A_97)))=k10_relat_1(A_96, A_97) | ~v1_relat_1(A_96))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_367])).
% 3.04/1.45  tff(c_402, plain, (![A_35, B_36]: (k1_relat_1(k6_partfun1(k3_xboole_0(A_35, B_36)))=k10_relat_1(k6_partfun1(B_36), A_35) | ~v1_relat_1(k6_partfun1(B_36)))), inference(superposition, [status(thm), theory('equality')], [c_69, c_390])).
% 3.04/1.45  tff(c_406, plain, (![B_36, A_35]: (k10_relat_1(k6_partfun1(B_36), A_35)=k3_xboole_0(A_35, B_36))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_78, c_402])).
% 3.04/1.45  tff(c_56, plain, (![A_37]: (k2_funct_1(k6_relat_1(A_37))=k6_relat_1(A_37))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.04/1.45  tff(c_68, plain, (![A_37]: (k2_funct_1(k6_partfun1(A_37))=k6_partfun1(A_37))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_62, c_56])).
% 3.04/1.45  tff(c_725, plain, (![B_124, A_125]: (k9_relat_1(k2_funct_1(B_124), A_125)=k10_relat_1(B_124, A_125) | ~v2_funct_1(B_124) | ~v1_funct_1(B_124) | ~v1_relat_1(B_124))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.04/1.45  tff(c_734, plain, (![A_37, A_125]: (k9_relat_1(k6_partfun1(A_37), A_125)=k10_relat_1(k6_partfun1(A_37), A_125) | ~v2_funct_1(k6_partfun1(A_37)) | ~v1_funct_1(k6_partfun1(A_37)) | ~v1_relat_1(k6_partfun1(A_37)))), inference(superposition, [status(thm), theory('equality')], [c_68, c_725])).
% 3.04/1.45  tff(c_738, plain, (![A_37, A_125]: (k9_relat_1(k6_partfun1(A_37), A_125)=k3_xboole_0(A_125, A_37))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_72, c_70, c_406, c_734])).
% 3.04/1.45  tff(c_36, plain, (![A_29]: (k2_relat_1(k6_relat_1(A_29))=A_29)), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.04/1.45  tff(c_77, plain, (![A_29]: (k2_relat_1(k6_partfun1(A_29))=A_29)), inference(demodulation, [status(thm), theory('equality')], [c_62, c_36])).
% 3.04/1.45  tff(c_40, plain, (![A_30]: (v4_relat_1(k6_relat_1(A_30), A_30))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.04/1.45  tff(c_75, plain, (![A_30]: (v4_relat_1(k6_partfun1(A_30), A_30))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_40])).
% 3.04/1.45  tff(c_317, plain, (![C_85, B_86, A_87]: (v4_relat_1(C_85, B_86) | ~v4_relat_1(C_85, A_87) | ~v1_relat_1(C_85) | ~r1_tarski(A_87, B_86))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.04/1.45  tff(c_319, plain, (![A_30, B_86]: (v4_relat_1(k6_partfun1(A_30), B_86) | ~v1_relat_1(k6_partfun1(A_30)) | ~r1_tarski(A_30, B_86))), inference(resolution, [status(thm)], [c_75, c_317])).
% 3.04/1.45  tff(c_323, plain, (![A_88, B_89]: (v4_relat_1(k6_partfun1(A_88), B_89) | ~r1_tarski(A_88, B_89))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_319])).
% 3.04/1.45  tff(c_30, plain, (![B_24, A_23]: (k7_relat_1(B_24, A_23)=B_24 | ~v4_relat_1(B_24, A_23) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.04/1.45  tff(c_328, plain, (![A_88, B_89]: (k7_relat_1(k6_partfun1(A_88), B_89)=k6_partfun1(A_88) | ~v1_relat_1(k6_partfun1(A_88)) | ~r1_tarski(A_88, B_89))), inference(resolution, [status(thm)], [c_323, c_30])).
% 3.04/1.45  tff(c_335, plain, (![A_90, B_91]: (k7_relat_1(k6_partfun1(A_90), B_91)=k6_partfun1(A_90) | ~r1_tarski(A_90, B_91))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_328])).
% 3.04/1.45  tff(c_26, plain, (![B_19, A_18]: (k2_relat_1(k7_relat_1(B_19, A_18))=k9_relat_1(B_19, A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.04/1.45  tff(c_341, plain, (![A_90, B_91]: (k9_relat_1(k6_partfun1(A_90), B_91)=k2_relat_1(k6_partfun1(A_90)) | ~v1_relat_1(k6_partfun1(A_90)) | ~r1_tarski(A_90, B_91))), inference(superposition, [status(thm), theory('equality')], [c_335, c_26])).
% 3.04/1.45  tff(c_354, plain, (![A_90, B_91]: (k9_relat_1(k6_partfun1(A_90), B_91)=A_90 | ~r1_tarski(A_90, B_91))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_77, c_341])).
% 3.04/1.45  tff(c_775, plain, (![B_131, A_132]: (k3_xboole_0(B_131, A_132)=A_132 | ~r1_tarski(A_132, B_131))), inference(demodulation, [status(thm), theory('equality')], [c_738, c_354])).
% 3.04/1.45  tff(c_787, plain, (k3_xboole_0('#skF_3', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_257, c_775])).
% 3.04/1.45  tff(c_2, plain, (![B_2, A_1]: (k2_tarski(B_2, A_1)=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.04/1.45  tff(c_164, plain, (![A_59, B_60]: (k1_setfam_1(k2_tarski(A_59, B_60))=k3_xboole_0(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.04/1.45  tff(c_185, plain, (![B_65, A_66]: (k1_setfam_1(k2_tarski(B_65, A_66))=k3_xboole_0(A_66, B_65))), inference(superposition, [status(thm), theory('equality')], [c_2, c_164])).
% 3.04/1.45  tff(c_22, plain, (![A_14, B_15]: (k1_setfam_1(k2_tarski(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.04/1.45  tff(c_191, plain, (![B_65, A_66]: (k3_xboole_0(B_65, A_66)=k3_xboole_0(A_66, B_65))), inference(superposition, [status(thm), theory('equality')], [c_185, c_22])).
% 3.04/1.45  tff(c_791, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_787, c_191])).
% 3.04/1.45  tff(c_60, plain, (![A_42]: (m1_subset_1(k6_relat_1(A_42), k1_zfmisc_1(k2_zfmisc_1(A_42, A_42))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.04/1.45  tff(c_67, plain, (![A_42]: (m1_subset_1(k6_partfun1(A_42), k1_zfmisc_1(k2_zfmisc_1(A_42, A_42))))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60])).
% 3.04/1.45  tff(c_873, plain, (![A_148, B_149, C_150, D_151]: (k8_relset_1(A_148, B_149, C_150, D_151)=k10_relat_1(C_150, D_151) | ~m1_subset_1(C_150, k1_zfmisc_1(k2_zfmisc_1(A_148, B_149))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.04/1.45  tff(c_875, plain, (![A_42, D_151]: (k8_relset_1(A_42, A_42, k6_partfun1(A_42), D_151)=k10_relat_1(k6_partfun1(A_42), D_151))), inference(resolution, [status(thm)], [c_67, c_873])).
% 3.04/1.45  tff(c_877, plain, (![A_42, D_151]: (k8_relset_1(A_42, A_42, k6_partfun1(A_42), D_151)=k3_xboole_0(D_151, A_42))), inference(demodulation, [status(thm), theory('equality')], [c_406, c_875])).
% 3.04/1.45  tff(c_64, plain, (k8_relset_1('#skF_3', '#skF_3', k6_partfun1('#skF_3'), '#skF_4')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.04/1.45  tff(c_878, plain, (k3_xboole_0('#skF_4', '#skF_3')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_877, c_64])).
% 3.04/1.45  tff(c_881, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_791, c_878])).
% 3.04/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.04/1.45  
% 3.04/1.45  Inference rules
% 3.04/1.45  ----------------------
% 3.04/1.45  #Ref     : 0
% 3.04/1.45  #Sup     : 174
% 3.04/1.45  #Fact    : 0
% 3.04/1.45  #Define  : 0
% 3.04/1.45  #Split   : 0
% 3.04/1.45  #Chain   : 0
% 3.04/1.45  #Close   : 0
% 3.04/1.45  
% 3.04/1.45  Ordering : KBO
% 3.04/1.45  
% 3.04/1.45  Simplification rules
% 3.04/1.45  ----------------------
% 3.04/1.45  #Subsume      : 3
% 3.04/1.45  #Demod        : 74
% 3.04/1.45  #Tautology    : 130
% 3.04/1.45  #SimpNegUnit  : 1
% 3.04/1.45  #BackRed      : 5
% 3.04/1.45  
% 3.04/1.45  #Partial instantiations: 0
% 3.04/1.45  #Strategies tried      : 1
% 3.04/1.45  
% 3.04/1.45  Timing (in seconds)
% 3.04/1.45  ----------------------
% 3.04/1.46  Preprocessing        : 0.34
% 3.04/1.46  Parsing              : 0.18
% 3.04/1.46  CNF conversion       : 0.02
% 3.04/1.46  Main loop            : 0.33
% 3.04/1.46  Inferencing          : 0.12
% 3.04/1.46  Reduction            : 0.11
% 3.04/1.46  Demodulation         : 0.08
% 3.04/1.46  BG Simplification    : 0.02
% 3.04/1.46  Subsumption          : 0.05
% 3.04/1.46  Abstraction          : 0.02
% 3.04/1.46  MUC search           : 0.00
% 3.04/1.46  Cooper               : 0.00
% 3.04/1.46  Total                : 0.72
% 3.04/1.46  Index Insertion      : 0.00
% 3.04/1.46  Index Deletion       : 0.00
% 3.04/1.46  Index Matching       : 0.00
% 3.04/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
