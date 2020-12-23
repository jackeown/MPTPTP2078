%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:11 EST 2020

% Result     : Theorem 2.67s
% Output     : CNFRefutation 3.08s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 199 expanded)
%              Number of leaves         :   54 (  93 expanded)
%              Depth                    :   12
%              Number of atoms          :  134 ( 244 expanded)
%              Number of equality atoms :   50 ( 121 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

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

tff(f_120,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k8_relset_1(A,A,k6_partfun1(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_2)).

tff(f_41,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_38,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_115,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_93,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_89,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_79,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_103,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_105,axiom,(
    ! [A] : k2_funct_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_1)).

tff(f_101,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k10_relat_1(B,A) = k9_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).

tff(f_85,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v4_relat_1(k6_relat_1(A),A)
      & v5_relat_1(k6_relat_1(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc24_relat_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ! [C] :
          ( ( v1_relat_1(C)
            & v4_relat_1(C,A) )
         => v4_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t217_relat_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_43,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_113,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_109,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(c_68,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_20,plain,(
    ! [A_13] : ~ v1_xboole_0(k1_zfmisc_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_187,plain,(
    ! [A_66,B_67] :
      ( r2_hidden(A_66,B_67)
      | v1_xboole_0(B_67)
      | ~ m1_subset_1(A_66,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_8,plain,(
    ! [C_12,A_8] :
      ( r1_tarski(C_12,A_8)
      | ~ r2_hidden(C_12,k1_zfmisc_1(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_191,plain,(
    ! [A_66,A_8] :
      ( r1_tarski(A_66,A_8)
      | v1_xboole_0(k1_zfmisc_1(A_8))
      | ~ m1_subset_1(A_66,k1_zfmisc_1(A_8)) ) ),
    inference(resolution,[status(thm)],[c_187,c_8])).

tff(c_252,plain,(
    ! [A_72,A_73] :
      ( r1_tarski(A_72,A_73)
      | ~ m1_subset_1(A_72,k1_zfmisc_1(A_73)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_191])).

tff(c_260,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_252])).

tff(c_64,plain,(
    ! [A_43] : k6_relat_1(A_43) = k6_partfun1(A_43) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_48,plain,(
    ! [A_32] : v1_relat_1(k6_relat_1(A_32)) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_72,plain,(
    ! [A_32] : v1_relat_1(k6_partfun1(A_32)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_48])).

tff(c_46,plain,(
    ! [A_31] : v1_funct_1(k6_relat_1(A_31)) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_73,plain,(
    ! [A_31] : v1_funct_1(k6_partfun1(A_31)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_46])).

tff(c_50,plain,(
    ! [A_32] : v2_funct_1(k6_relat_1(A_32)) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_71,plain,(
    ! [A_32] : v2_funct_1(k6_partfun1(A_32)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_50])).

tff(c_34,plain,(
    ! [A_29] : k1_relat_1(k6_relat_1(A_29)) = A_29 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_79,plain,(
    ! [A_29] : k1_relat_1(k6_partfun1(A_29)) = A_29 ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_34])).

tff(c_54,plain,(
    ! [B_36,A_35] : k5_relat_1(k6_relat_1(B_36),k6_relat_1(A_35)) = k6_relat_1(k3_xboole_0(A_35,B_36)) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_70,plain,(
    ! [B_36,A_35] : k5_relat_1(k6_partfun1(B_36),k6_partfun1(A_35)) = k6_partfun1(k3_xboole_0(A_35,B_36)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_64,c_64,c_54])).

tff(c_337,plain,(
    ! [A_91,B_92] :
      ( k10_relat_1(A_91,k1_relat_1(B_92)) = k1_relat_1(k5_relat_1(A_91,B_92))
      | ~ v1_relat_1(B_92)
      | ~ v1_relat_1(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_346,plain,(
    ! [A_91,A_29] :
      ( k1_relat_1(k5_relat_1(A_91,k6_partfun1(A_29))) = k10_relat_1(A_91,A_29)
      | ~ v1_relat_1(k6_partfun1(A_29))
      | ~ v1_relat_1(A_91) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_337])).

tff(c_392,plain,(
    ! [A_97,A_98] :
      ( k1_relat_1(k5_relat_1(A_97,k6_partfun1(A_98))) = k10_relat_1(A_97,A_98)
      | ~ v1_relat_1(A_97) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_346])).

tff(c_404,plain,(
    ! [A_35,B_36] :
      ( k1_relat_1(k6_partfun1(k3_xboole_0(A_35,B_36))) = k10_relat_1(k6_partfun1(B_36),A_35)
      | ~ v1_relat_1(k6_partfun1(B_36)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_392])).

tff(c_408,plain,(
    ! [B_36,A_35] : k10_relat_1(k6_partfun1(B_36),A_35) = k3_xboole_0(A_35,B_36) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_79,c_404])).

tff(c_56,plain,(
    ! [A_37] : k2_funct_1(k6_relat_1(A_37)) = k6_relat_1(A_37) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_69,plain,(
    ! [A_37] : k2_funct_1(k6_partfun1(A_37)) = k6_partfun1(A_37) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_64,c_56])).

tff(c_511,plain,(
    ! [B_109,A_110] :
      ( k9_relat_1(k2_funct_1(B_109),A_110) = k10_relat_1(B_109,A_110)
      | ~ v2_funct_1(B_109)
      | ~ v1_funct_1(B_109)
      | ~ v1_relat_1(B_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_520,plain,(
    ! [A_37,A_110] :
      ( k9_relat_1(k6_partfun1(A_37),A_110) = k10_relat_1(k6_partfun1(A_37),A_110)
      | ~ v2_funct_1(k6_partfun1(A_37))
      | ~ v1_funct_1(k6_partfun1(A_37))
      | ~ v1_relat_1(k6_partfun1(A_37)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_511])).

tff(c_524,plain,(
    ! [A_37,A_110] : k9_relat_1(k6_partfun1(A_37),A_110) = k3_xboole_0(A_110,A_37) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_73,c_71,c_408,c_520])).

tff(c_36,plain,(
    ! [A_29] : k2_relat_1(k6_relat_1(A_29)) = A_29 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_78,plain,(
    ! [A_29] : k2_relat_1(k6_partfun1(A_29)) = A_29 ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_36])).

tff(c_40,plain,(
    ! [A_30] : v4_relat_1(k6_relat_1(A_30),A_30) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_76,plain,(
    ! [A_30] : v4_relat_1(k6_partfun1(A_30),A_30) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_40])).

tff(c_319,plain,(
    ! [C_86,B_87,A_88] :
      ( v4_relat_1(C_86,B_87)
      | ~ v4_relat_1(C_86,A_88)
      | ~ v1_relat_1(C_86)
      | ~ r1_tarski(A_88,B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_321,plain,(
    ! [A_30,B_87] :
      ( v4_relat_1(k6_partfun1(A_30),B_87)
      | ~ v1_relat_1(k6_partfun1(A_30))
      | ~ r1_tarski(A_30,B_87) ) ),
    inference(resolution,[status(thm)],[c_76,c_319])).

tff(c_325,plain,(
    ! [A_89,B_90] :
      ( v4_relat_1(k6_partfun1(A_89),B_90)
      | ~ r1_tarski(A_89,B_90) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_321])).

tff(c_30,plain,(
    ! [B_24,A_23] :
      ( k7_relat_1(B_24,A_23) = B_24
      | ~ v4_relat_1(B_24,A_23)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_330,plain,(
    ! [A_89,B_90] :
      ( k7_relat_1(k6_partfun1(A_89),B_90) = k6_partfun1(A_89)
      | ~ v1_relat_1(k6_partfun1(A_89))
      | ~ r1_tarski(A_89,B_90) ) ),
    inference(resolution,[status(thm)],[c_325,c_30])).

tff(c_351,plain,(
    ! [A_93,B_94] :
      ( k7_relat_1(k6_partfun1(A_93),B_94) = k6_partfun1(A_93)
      | ~ r1_tarski(A_93,B_94) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_330])).

tff(c_26,plain,(
    ! [B_19,A_18] :
      ( k2_relat_1(k7_relat_1(B_19,A_18)) = k9_relat_1(B_19,A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_357,plain,(
    ! [A_93,B_94] :
      ( k9_relat_1(k6_partfun1(A_93),B_94) = k2_relat_1(k6_partfun1(A_93))
      | ~ v1_relat_1(k6_partfun1(A_93))
      | ~ r1_tarski(A_93,B_94) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_351,c_26])).

tff(c_370,plain,(
    ! [A_93,B_94] :
      ( k9_relat_1(k6_partfun1(A_93),B_94) = A_93
      | ~ r1_tarski(A_93,B_94) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_78,c_357])).

tff(c_565,plain,(
    ! [B_116,A_117] :
      ( k3_xboole_0(B_116,A_117) = A_117
      | ~ r1_tarski(A_117,B_116) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_524,c_370])).

tff(c_573,plain,(
    k3_xboole_0('#skF_3','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_260,c_565])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_tarski(B_2,A_1) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_166,plain,(
    ! [A_60,B_61] : k1_setfam_1(k2_tarski(A_60,B_61)) = k3_xboole_0(A_60,B_61) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_195,plain,(
    ! [B_68,A_69] : k1_setfam_1(k2_tarski(B_68,A_69)) = k3_xboole_0(A_69,B_68) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_166])).

tff(c_22,plain,(
    ! [A_14,B_15] : k1_setfam_1(k2_tarski(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_201,plain,(
    ! [B_68,A_69] : k3_xboole_0(B_68,A_69) = k3_xboole_0(A_69,B_68) ),
    inference(superposition,[status(thm),theory(equality)],[c_195,c_22])).

tff(c_577,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_573,c_201])).

tff(c_62,plain,(
    ! [A_42] : m1_subset_1(k6_partfun1(A_42),k1_zfmisc_1(k2_zfmisc_1(A_42,A_42))) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_813,plain,(
    ! [A_147,B_148,C_149,D_150] :
      ( k8_relset_1(A_147,B_148,C_149,D_150) = k10_relat_1(C_149,D_150)
      | ~ m1_subset_1(C_149,k1_zfmisc_1(k2_zfmisc_1(A_147,B_148))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_815,plain,(
    ! [A_42,D_150] : k8_relset_1(A_42,A_42,k6_partfun1(A_42),D_150) = k10_relat_1(k6_partfun1(A_42),D_150) ),
    inference(resolution,[status(thm)],[c_62,c_813])).

tff(c_817,plain,(
    ! [A_42,D_150] : k8_relset_1(A_42,A_42,k6_partfun1(A_42),D_150) = k3_xboole_0(D_150,A_42) ),
    inference(demodulation,[status(thm),theory(equality)],[c_408,c_815])).

tff(c_66,plain,(
    k8_relset_1('#skF_3','#skF_3',k6_partfun1('#skF_3'),'#skF_4') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_818,plain,(
    k3_xboole_0('#skF_4','#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_817,c_66])).

tff(c_821,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_577,c_818])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:38:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.67/1.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.67/1.45  
% 2.67/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.67/1.45  %$ v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.67/1.45  
% 2.67/1.45  %Foreground sorts:
% 2.67/1.45  
% 2.67/1.45  
% 2.67/1.45  %Background operators:
% 2.67/1.45  
% 2.67/1.45  
% 2.67/1.45  %Foreground operators:
% 2.67/1.45  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.67/1.45  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.67/1.45  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.67/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.67/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.67/1.45  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.67/1.45  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.67/1.45  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.67/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.67/1.45  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.67/1.45  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.67/1.45  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.67/1.45  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.67/1.45  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.67/1.45  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.67/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.67/1.45  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.67/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.67/1.45  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.67/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.67/1.45  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.67/1.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.67/1.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.67/1.45  tff('#skF_4', type, '#skF_4': $i).
% 2.67/1.45  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.67/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.67/1.45  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.67/1.45  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.67/1.45  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.67/1.45  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.67/1.45  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.67/1.45  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.67/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.67/1.45  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.67/1.45  
% 3.08/1.47  tff(f_120, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k8_relset_1(A, A, k6_partfun1(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t171_funct_2)).
% 3.08/1.47  tff(f_41, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 3.08/1.47  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 3.08/1.47  tff(f_38, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.08/1.47  tff(f_115, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 3.08/1.47  tff(f_93, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 3.08/1.47  tff(f_89, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 3.08/1.47  tff(f_79, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 3.08/1.47  tff(f_103, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 3.08/1.47  tff(f_60, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 3.08/1.47  tff(f_105, axiom, (![A]: (k2_funct_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_funct_1)).
% 3.08/1.47  tff(f_101, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k10_relat_1(B, A) = k9_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t155_funct_1)).
% 3.08/1.47  tff(f_85, axiom, (![A]: ((v1_relat_1(k6_relat_1(A)) & v4_relat_1(k6_relat_1(A), A)) & v5_relat_1(k6_relat_1(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc24_relat_1)).
% 3.08/1.47  tff(f_75, axiom, (![A, B]: (r1_tarski(A, B) => (![C]: ((v1_relat_1(C) & v4_relat_1(C, A)) => v4_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t217_relat_1)).
% 3.08/1.47  tff(f_66, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 3.08/1.47  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 3.08/1.47  tff(f_27, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.08/1.47  tff(f_43, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.08/1.47  tff(f_113, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 3.08/1.47  tff(f_109, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.08/1.47  tff(c_68, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.08/1.47  tff(c_20, plain, (![A_13]: (~v1_xboole_0(k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.08/1.47  tff(c_187, plain, (![A_66, B_67]: (r2_hidden(A_66, B_67) | v1_xboole_0(B_67) | ~m1_subset_1(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.08/1.47  tff(c_8, plain, (![C_12, A_8]: (r1_tarski(C_12, A_8) | ~r2_hidden(C_12, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.08/1.47  tff(c_191, plain, (![A_66, A_8]: (r1_tarski(A_66, A_8) | v1_xboole_0(k1_zfmisc_1(A_8)) | ~m1_subset_1(A_66, k1_zfmisc_1(A_8)))), inference(resolution, [status(thm)], [c_187, c_8])).
% 3.08/1.47  tff(c_252, plain, (![A_72, A_73]: (r1_tarski(A_72, A_73) | ~m1_subset_1(A_72, k1_zfmisc_1(A_73)))), inference(negUnitSimplification, [status(thm)], [c_20, c_191])).
% 3.08/1.47  tff(c_260, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_68, c_252])).
% 3.08/1.47  tff(c_64, plain, (![A_43]: (k6_relat_1(A_43)=k6_partfun1(A_43))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.08/1.47  tff(c_48, plain, (![A_32]: (v1_relat_1(k6_relat_1(A_32)))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.08/1.47  tff(c_72, plain, (![A_32]: (v1_relat_1(k6_partfun1(A_32)))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_48])).
% 3.08/1.47  tff(c_46, plain, (![A_31]: (v1_funct_1(k6_relat_1(A_31)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.08/1.47  tff(c_73, plain, (![A_31]: (v1_funct_1(k6_partfun1(A_31)))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_46])).
% 3.08/1.47  tff(c_50, plain, (![A_32]: (v2_funct_1(k6_relat_1(A_32)))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.08/1.47  tff(c_71, plain, (![A_32]: (v2_funct_1(k6_partfun1(A_32)))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_50])).
% 3.08/1.47  tff(c_34, plain, (![A_29]: (k1_relat_1(k6_relat_1(A_29))=A_29)), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.08/1.47  tff(c_79, plain, (![A_29]: (k1_relat_1(k6_partfun1(A_29))=A_29)), inference(demodulation, [status(thm), theory('equality')], [c_64, c_34])).
% 3.08/1.47  tff(c_54, plain, (![B_36, A_35]: (k5_relat_1(k6_relat_1(B_36), k6_relat_1(A_35))=k6_relat_1(k3_xboole_0(A_35, B_36)))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.08/1.47  tff(c_70, plain, (![B_36, A_35]: (k5_relat_1(k6_partfun1(B_36), k6_partfun1(A_35))=k6_partfun1(k3_xboole_0(A_35, B_36)))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_64, c_64, c_54])).
% 3.08/1.47  tff(c_337, plain, (![A_91, B_92]: (k10_relat_1(A_91, k1_relat_1(B_92))=k1_relat_1(k5_relat_1(A_91, B_92)) | ~v1_relat_1(B_92) | ~v1_relat_1(A_91))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.08/1.47  tff(c_346, plain, (![A_91, A_29]: (k1_relat_1(k5_relat_1(A_91, k6_partfun1(A_29)))=k10_relat_1(A_91, A_29) | ~v1_relat_1(k6_partfun1(A_29)) | ~v1_relat_1(A_91))), inference(superposition, [status(thm), theory('equality')], [c_79, c_337])).
% 3.08/1.47  tff(c_392, plain, (![A_97, A_98]: (k1_relat_1(k5_relat_1(A_97, k6_partfun1(A_98)))=k10_relat_1(A_97, A_98) | ~v1_relat_1(A_97))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_346])).
% 3.08/1.47  tff(c_404, plain, (![A_35, B_36]: (k1_relat_1(k6_partfun1(k3_xboole_0(A_35, B_36)))=k10_relat_1(k6_partfun1(B_36), A_35) | ~v1_relat_1(k6_partfun1(B_36)))), inference(superposition, [status(thm), theory('equality')], [c_70, c_392])).
% 3.08/1.47  tff(c_408, plain, (![B_36, A_35]: (k10_relat_1(k6_partfun1(B_36), A_35)=k3_xboole_0(A_35, B_36))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_79, c_404])).
% 3.08/1.47  tff(c_56, plain, (![A_37]: (k2_funct_1(k6_relat_1(A_37))=k6_relat_1(A_37))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.08/1.47  tff(c_69, plain, (![A_37]: (k2_funct_1(k6_partfun1(A_37))=k6_partfun1(A_37))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_64, c_56])).
% 3.08/1.47  tff(c_511, plain, (![B_109, A_110]: (k9_relat_1(k2_funct_1(B_109), A_110)=k10_relat_1(B_109, A_110) | ~v2_funct_1(B_109) | ~v1_funct_1(B_109) | ~v1_relat_1(B_109))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.08/1.47  tff(c_520, plain, (![A_37, A_110]: (k9_relat_1(k6_partfun1(A_37), A_110)=k10_relat_1(k6_partfun1(A_37), A_110) | ~v2_funct_1(k6_partfun1(A_37)) | ~v1_funct_1(k6_partfun1(A_37)) | ~v1_relat_1(k6_partfun1(A_37)))), inference(superposition, [status(thm), theory('equality')], [c_69, c_511])).
% 3.08/1.47  tff(c_524, plain, (![A_37, A_110]: (k9_relat_1(k6_partfun1(A_37), A_110)=k3_xboole_0(A_110, A_37))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_73, c_71, c_408, c_520])).
% 3.08/1.47  tff(c_36, plain, (![A_29]: (k2_relat_1(k6_relat_1(A_29))=A_29)), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.08/1.47  tff(c_78, plain, (![A_29]: (k2_relat_1(k6_partfun1(A_29))=A_29)), inference(demodulation, [status(thm), theory('equality')], [c_64, c_36])).
% 3.08/1.47  tff(c_40, plain, (![A_30]: (v4_relat_1(k6_relat_1(A_30), A_30))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.08/1.47  tff(c_76, plain, (![A_30]: (v4_relat_1(k6_partfun1(A_30), A_30))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_40])).
% 3.08/1.47  tff(c_319, plain, (![C_86, B_87, A_88]: (v4_relat_1(C_86, B_87) | ~v4_relat_1(C_86, A_88) | ~v1_relat_1(C_86) | ~r1_tarski(A_88, B_87))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.08/1.47  tff(c_321, plain, (![A_30, B_87]: (v4_relat_1(k6_partfun1(A_30), B_87) | ~v1_relat_1(k6_partfun1(A_30)) | ~r1_tarski(A_30, B_87))), inference(resolution, [status(thm)], [c_76, c_319])).
% 3.08/1.47  tff(c_325, plain, (![A_89, B_90]: (v4_relat_1(k6_partfun1(A_89), B_90) | ~r1_tarski(A_89, B_90))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_321])).
% 3.08/1.47  tff(c_30, plain, (![B_24, A_23]: (k7_relat_1(B_24, A_23)=B_24 | ~v4_relat_1(B_24, A_23) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.08/1.47  tff(c_330, plain, (![A_89, B_90]: (k7_relat_1(k6_partfun1(A_89), B_90)=k6_partfun1(A_89) | ~v1_relat_1(k6_partfun1(A_89)) | ~r1_tarski(A_89, B_90))), inference(resolution, [status(thm)], [c_325, c_30])).
% 3.08/1.47  tff(c_351, plain, (![A_93, B_94]: (k7_relat_1(k6_partfun1(A_93), B_94)=k6_partfun1(A_93) | ~r1_tarski(A_93, B_94))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_330])).
% 3.08/1.47  tff(c_26, plain, (![B_19, A_18]: (k2_relat_1(k7_relat_1(B_19, A_18))=k9_relat_1(B_19, A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.08/1.47  tff(c_357, plain, (![A_93, B_94]: (k9_relat_1(k6_partfun1(A_93), B_94)=k2_relat_1(k6_partfun1(A_93)) | ~v1_relat_1(k6_partfun1(A_93)) | ~r1_tarski(A_93, B_94))), inference(superposition, [status(thm), theory('equality')], [c_351, c_26])).
% 3.08/1.47  tff(c_370, plain, (![A_93, B_94]: (k9_relat_1(k6_partfun1(A_93), B_94)=A_93 | ~r1_tarski(A_93, B_94))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_78, c_357])).
% 3.08/1.47  tff(c_565, plain, (![B_116, A_117]: (k3_xboole_0(B_116, A_117)=A_117 | ~r1_tarski(A_117, B_116))), inference(demodulation, [status(thm), theory('equality')], [c_524, c_370])).
% 3.08/1.47  tff(c_573, plain, (k3_xboole_0('#skF_3', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_260, c_565])).
% 3.08/1.47  tff(c_2, plain, (![B_2, A_1]: (k2_tarski(B_2, A_1)=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.08/1.47  tff(c_166, plain, (![A_60, B_61]: (k1_setfam_1(k2_tarski(A_60, B_61))=k3_xboole_0(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.08/1.47  tff(c_195, plain, (![B_68, A_69]: (k1_setfam_1(k2_tarski(B_68, A_69))=k3_xboole_0(A_69, B_68))), inference(superposition, [status(thm), theory('equality')], [c_2, c_166])).
% 3.08/1.47  tff(c_22, plain, (![A_14, B_15]: (k1_setfam_1(k2_tarski(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.08/1.47  tff(c_201, plain, (![B_68, A_69]: (k3_xboole_0(B_68, A_69)=k3_xboole_0(A_69, B_68))), inference(superposition, [status(thm), theory('equality')], [c_195, c_22])).
% 3.08/1.47  tff(c_577, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_573, c_201])).
% 3.08/1.47  tff(c_62, plain, (![A_42]: (m1_subset_1(k6_partfun1(A_42), k1_zfmisc_1(k2_zfmisc_1(A_42, A_42))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.08/1.47  tff(c_813, plain, (![A_147, B_148, C_149, D_150]: (k8_relset_1(A_147, B_148, C_149, D_150)=k10_relat_1(C_149, D_150) | ~m1_subset_1(C_149, k1_zfmisc_1(k2_zfmisc_1(A_147, B_148))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.08/1.47  tff(c_815, plain, (![A_42, D_150]: (k8_relset_1(A_42, A_42, k6_partfun1(A_42), D_150)=k10_relat_1(k6_partfun1(A_42), D_150))), inference(resolution, [status(thm)], [c_62, c_813])).
% 3.08/1.47  tff(c_817, plain, (![A_42, D_150]: (k8_relset_1(A_42, A_42, k6_partfun1(A_42), D_150)=k3_xboole_0(D_150, A_42))), inference(demodulation, [status(thm), theory('equality')], [c_408, c_815])).
% 3.08/1.47  tff(c_66, plain, (k8_relset_1('#skF_3', '#skF_3', k6_partfun1('#skF_3'), '#skF_4')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.08/1.47  tff(c_818, plain, (k3_xboole_0('#skF_4', '#skF_3')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_817, c_66])).
% 3.08/1.47  tff(c_821, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_577, c_818])).
% 3.08/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.08/1.47  
% 3.08/1.47  Inference rules
% 3.08/1.47  ----------------------
% 3.08/1.47  #Ref     : 0
% 3.08/1.47  #Sup     : 160
% 3.08/1.47  #Fact    : 0
% 3.08/1.47  #Define  : 0
% 3.08/1.47  #Split   : 0
% 3.08/1.47  #Chain   : 0
% 3.08/1.47  #Close   : 0
% 3.08/1.47  
% 3.08/1.47  Ordering : KBO
% 3.08/1.47  
% 3.08/1.47  Simplification rules
% 3.08/1.47  ----------------------
% 3.08/1.47  #Subsume      : 3
% 3.08/1.47  #Demod        : 75
% 3.08/1.47  #Tautology    : 114
% 3.08/1.47  #SimpNegUnit  : 1
% 3.08/1.47  #BackRed      : 3
% 3.08/1.47  
% 3.08/1.47  #Partial instantiations: 0
% 3.08/1.47  #Strategies tried      : 1
% 3.08/1.47  
% 3.08/1.47  Timing (in seconds)
% 3.08/1.47  ----------------------
% 3.08/1.48  Preprocessing        : 0.35
% 3.08/1.48  Parsing              : 0.18
% 3.08/1.48  CNF conversion       : 0.02
% 3.08/1.48  Main loop            : 0.34
% 3.08/1.48  Inferencing          : 0.13
% 3.08/1.48  Reduction            : 0.12
% 3.08/1.48  Demodulation         : 0.09
% 3.08/1.48  BG Simplification    : 0.02
% 3.08/1.48  Subsumption          : 0.05
% 3.08/1.48  Abstraction          : 0.02
% 3.08/1.48  MUC search           : 0.00
% 3.08/1.48  Cooper               : 0.00
% 3.08/1.48  Total                : 0.73
% 3.08/1.48  Index Insertion      : 0.00
% 3.08/1.48  Index Deletion       : 0.00
% 3.08/1.48  Index Matching       : 0.00
% 3.08/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
