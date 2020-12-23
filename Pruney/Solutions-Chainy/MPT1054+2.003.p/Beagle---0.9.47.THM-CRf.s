%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:12 EST 2020

% Result     : Theorem 3.16s
% Output     : CNFRefutation 3.16s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 193 expanded)
%              Number of leaves         :   51 (  89 expanded)
%              Depth                    :   13
%              Number of atoms          :  134 ( 244 expanded)
%              Number of equality atoms :   49 ( 112 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

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

tff(f_110,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_108,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_106,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_115,negated_conjecture,(
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

tff(f_72,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_43,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_90,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_102,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_82,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v4_relat_1(k6_relat_1(A),A)
      & v5_relat_1(k6_relat_1(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc24_relat_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ! [C] :
          ( ( v1_relat_1(C)
            & v4_relat_1(C,A) )
         => v4_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t217_relat_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_86,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_100,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( ( r1_tarski(A,k1_relat_1(B))
          & v2_funct_1(B) )
       => k10_relat_1(B,k9_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).

tff(c_60,plain,(
    ! [A_41] : k6_relat_1(A_41) = k6_partfun1(A_41) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_58,plain,(
    ! [A_40] : m1_subset_1(k6_relat_1(A_40),k1_zfmisc_1(k2_zfmisc_1(A_40,A_40))) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_65,plain,(
    ! [A_40] : m1_subset_1(k6_partfun1(A_40),k1_zfmisc_1(k2_zfmisc_1(A_40,A_40))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58])).

tff(c_814,plain,(
    ! [A_115,B_116,C_117,D_118] :
      ( k8_relset_1(A_115,B_116,C_117,D_118) = k10_relat_1(C_117,D_118)
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1(A_115,B_116))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_817,plain,(
    ! [A_40,D_118] : k8_relset_1(A_40,A_40,k6_partfun1(A_40),D_118) = k10_relat_1(k6_partfun1(A_40),D_118) ),
    inference(resolution,[status(thm)],[c_65,c_814])).

tff(c_62,plain,(
    k8_relset_1('#skF_3','#skF_3',k6_partfun1('#skF_3'),'#skF_4') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_948,plain,(
    k10_relat_1(k6_partfun1('#skF_3'),'#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_817,c_62])).

tff(c_64,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_20,plain,(
    ! [A_13] : ~ v1_xboole_0(k1_zfmisc_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_230,plain,(
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

tff(c_234,plain,(
    ! [A_66,A_8] :
      ( r1_tarski(A_66,A_8)
      | v1_xboole_0(k1_zfmisc_1(A_8))
      | ~ m1_subset_1(A_66,k1_zfmisc_1(A_8)) ) ),
    inference(resolution,[status(thm)],[c_230,c_8])).

tff(c_239,plain,(
    ! [A_68,A_69] :
      ( r1_tarski(A_68,A_69)
      | ~ m1_subset_1(A_68,k1_zfmisc_1(A_69)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_234])).

tff(c_247,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_239])).

tff(c_34,plain,(
    ! [A_26] : k2_relat_1(k6_relat_1(A_26)) = A_26 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_75,plain,(
    ! [A_26] : k2_relat_1(k6_partfun1(A_26)) = A_26 ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_34])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_tarski(B_2,A_1) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_143,plain,(
    ! [A_53,B_54] : k1_setfam_1(k2_tarski(A_53,B_54)) = k3_xboole_0(A_53,B_54) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_174,plain,(
    ! [A_62,B_63] : k1_setfam_1(k2_tarski(A_62,B_63)) = k3_xboole_0(B_63,A_62) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_143])).

tff(c_22,plain,(
    ! [A_14,B_15] : k1_setfam_1(k2_tarski(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_180,plain,(
    ! [B_63,A_62] : k3_xboole_0(B_63,A_62) = k3_xboole_0(A_62,B_63) ),
    inference(superposition,[status(thm),theory(equality)],[c_174,c_22])).

tff(c_48,plain,(
    ! [A_31] : v1_relat_1(k6_relat_1(A_31)) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_68,plain,(
    ! [A_31] : v1_relat_1(k6_partfun1(A_31)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_48])).

tff(c_54,plain,(
    ! [B_35,A_34] : k5_relat_1(k6_relat_1(B_35),k6_relat_1(A_34)) = k6_relat_1(k3_xboole_0(A_34,B_35)) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_306,plain,(
    ! [B_82,A_83] : k5_relat_1(k6_partfun1(B_82),k6_partfun1(A_83)) = k6_partfun1(k3_xboole_0(A_83,B_82)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_60,c_60,c_54])).

tff(c_36,plain,(
    ! [A_27,B_28] :
      ( k5_relat_1(k6_relat_1(A_27),B_28) = k7_relat_1(B_28,A_27)
      | ~ v1_relat_1(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_74,plain,(
    ! [A_27,B_28] :
      ( k5_relat_1(k6_partfun1(A_27),B_28) = k7_relat_1(B_28,A_27)
      | ~ v1_relat_1(B_28) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_36])).

tff(c_312,plain,(
    ! [A_83,B_82] :
      ( k7_relat_1(k6_partfun1(A_83),B_82) = k6_partfun1(k3_xboole_0(A_83,B_82))
      | ~ v1_relat_1(k6_partfun1(A_83)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_306,c_74])).

tff(c_322,plain,(
    ! [A_83,B_82] : k7_relat_1(k6_partfun1(A_83),B_82) = k6_partfun1(k3_xboole_0(A_83,B_82)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_312])).

tff(c_40,plain,(
    ! [A_29] : v4_relat_1(k6_relat_1(A_29),A_29) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_72,plain,(
    ! [A_29] : v4_relat_1(k6_partfun1(A_29),A_29) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_40])).

tff(c_417,plain,(
    ! [C_88,B_89,A_90] :
      ( v4_relat_1(C_88,B_89)
      | ~ v4_relat_1(C_88,A_90)
      | ~ v1_relat_1(C_88)
      | ~ r1_tarski(A_90,B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_419,plain,(
    ! [A_29,B_89] :
      ( v4_relat_1(k6_partfun1(A_29),B_89)
      | ~ v1_relat_1(k6_partfun1(A_29))
      | ~ r1_tarski(A_29,B_89) ) ),
    inference(resolution,[status(thm)],[c_72,c_417])).

tff(c_433,plain,(
    ! [A_93,B_94] :
      ( v4_relat_1(k6_partfun1(A_93),B_94)
      | ~ r1_tarski(A_93,B_94) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_419])).

tff(c_28,plain,(
    ! [B_21,A_20] :
      ( k7_relat_1(B_21,A_20) = B_21
      | ~ v4_relat_1(B_21,A_20)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_438,plain,(
    ! [A_93,B_94] :
      ( k7_relat_1(k6_partfun1(A_93),B_94) = k6_partfun1(A_93)
      | ~ v1_relat_1(k6_partfun1(A_93))
      | ~ r1_tarski(A_93,B_94) ) ),
    inference(resolution,[status(thm)],[c_433,c_28])).

tff(c_474,plain,(
    ! [A_99,B_100] :
      ( k6_partfun1(k3_xboole_0(A_99,B_100)) = k6_partfun1(A_99)
      | ~ r1_tarski(A_99,B_100) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_322,c_438])).

tff(c_614,plain,(
    ! [A_108,B_109] :
      ( k6_partfun1(k3_xboole_0(A_108,B_109)) = k6_partfun1(B_109)
      | ~ r1_tarski(B_109,A_108) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_180,c_474])).

tff(c_662,plain,(
    ! [A_108,B_109] :
      ( k3_xboole_0(A_108,B_109) = k2_relat_1(k6_partfun1(B_109))
      | ~ r1_tarski(B_109,A_108) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_614,c_75])).

tff(c_710,plain,(
    ! [A_110,B_111] :
      ( k3_xboole_0(A_110,B_111) = B_111
      | ~ r1_tarski(B_111,A_110) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_662])).

tff(c_718,plain,(
    k3_xboole_0('#skF_3','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_247,c_710])).

tff(c_46,plain,(
    ! [A_30] : v1_funct_1(k6_relat_1(A_30)) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_69,plain,(
    ! [A_30] : v1_funct_1(k6_partfun1(A_30)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_46])).

tff(c_50,plain,(
    ! [A_31] : v2_funct_1(k6_relat_1(A_31)) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_67,plain,(
    ! [A_31] : v2_funct_1(k6_partfun1(A_31)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_50])).

tff(c_326,plain,(
    ! [A_84,B_85] : k7_relat_1(k6_partfun1(A_84),B_85) = k6_partfun1(k3_xboole_0(A_84,B_85)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_312])).

tff(c_26,plain,(
    ! [B_19,A_18] :
      ( k2_relat_1(k7_relat_1(B_19,A_18)) = k9_relat_1(B_19,A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_336,plain,(
    ! [A_84,B_85] :
      ( k2_relat_1(k6_partfun1(k3_xboole_0(A_84,B_85))) = k9_relat_1(k6_partfun1(A_84),B_85)
      | ~ v1_relat_1(k6_partfun1(A_84)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_326,c_26])).

tff(c_345,plain,(
    ! [A_84,B_85] : k9_relat_1(k6_partfun1(A_84),B_85) = k3_xboole_0(A_84,B_85) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_75,c_336])).

tff(c_32,plain,(
    ! [A_26] : k1_relat_1(k6_relat_1(A_26)) = A_26 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_76,plain,(
    ! [A_26] : k1_relat_1(k6_partfun1(A_26)) = A_26 ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_32])).

tff(c_895,plain,(
    ! [B_123,A_124] :
      ( k10_relat_1(B_123,k9_relat_1(B_123,A_124)) = A_124
      | ~ v2_funct_1(B_123)
      | ~ r1_tarski(A_124,k1_relat_1(B_123))
      | ~ v1_funct_1(B_123)
      | ~ v1_relat_1(B_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_900,plain,(
    ! [A_26,A_124] :
      ( k10_relat_1(k6_partfun1(A_26),k9_relat_1(k6_partfun1(A_26),A_124)) = A_124
      | ~ v2_funct_1(k6_partfun1(A_26))
      | ~ r1_tarski(A_124,A_26)
      | ~ v1_funct_1(k6_partfun1(A_26))
      | ~ v1_relat_1(k6_partfun1(A_26)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_895])).

tff(c_964,plain,(
    ! [A_129,A_130] :
      ( k10_relat_1(k6_partfun1(A_129),k3_xboole_0(A_129,A_130)) = A_130
      | ~ r1_tarski(A_130,A_129) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_69,c_67,c_345,c_900])).

tff(c_976,plain,
    ( k10_relat_1(k6_partfun1('#skF_3'),'#skF_4') = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_718,c_964])).

tff(c_1003,plain,(
    k10_relat_1(k6_partfun1('#skF_3'),'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_247,c_976])).

tff(c_1005,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_948,c_1003])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:07:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.16/1.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.16/1.51  
% 3.16/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.16/1.51  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.16/1.51  
% 3.16/1.51  %Foreground sorts:
% 3.16/1.51  
% 3.16/1.51  
% 3.16/1.51  %Background operators:
% 3.16/1.51  
% 3.16/1.51  
% 3.16/1.51  %Foreground operators:
% 3.16/1.51  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.16/1.51  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.16/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.16/1.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.16/1.51  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.16/1.51  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.16/1.51  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.16/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.16/1.51  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.16/1.51  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.16/1.51  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.16/1.51  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.16/1.51  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.16/1.51  tff('#skF_3', type, '#skF_3': $i).
% 3.16/1.51  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.16/1.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.16/1.51  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 3.16/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.16/1.51  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.16/1.51  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.16/1.51  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.16/1.51  tff('#skF_4', type, '#skF_4': $i).
% 3.16/1.51  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.16/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.16/1.51  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.16/1.51  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.16/1.51  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.16/1.51  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.16/1.51  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.16/1.51  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.16/1.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.16/1.51  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.16/1.51  
% 3.16/1.53  tff(f_110, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 3.16/1.53  tff(f_108, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 3.16/1.53  tff(f_106, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.16/1.53  tff(f_115, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k8_relset_1(A, A, k6_partfun1(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t171_funct_2)).
% 3.16/1.53  tff(f_41, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 3.16/1.53  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 3.16/1.53  tff(f_38, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.16/1.53  tff(f_72, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 3.16/1.53  tff(f_27, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.16/1.53  tff(f_43, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.16/1.53  tff(f_90, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 3.16/1.53  tff(f_102, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 3.16/1.53  tff(f_76, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 3.16/1.53  tff(f_82, axiom, (![A]: ((v1_relat_1(k6_relat_1(A)) & v4_relat_1(k6_relat_1(A), A)) & v5_relat_1(k6_relat_1(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc24_relat_1)).
% 3.16/1.53  tff(f_68, axiom, (![A, B]: (r1_tarski(A, B) => (![C]: ((v1_relat_1(C) & v4_relat_1(C, A)) => v4_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t217_relat_1)).
% 3.16/1.53  tff(f_59, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 3.16/1.53  tff(f_86, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 3.16/1.53  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 3.16/1.53  tff(f_100, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((r1_tarski(A, k1_relat_1(B)) & v2_funct_1(B)) => (k10_relat_1(B, k9_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t164_funct_1)).
% 3.16/1.53  tff(c_60, plain, (![A_41]: (k6_relat_1(A_41)=k6_partfun1(A_41))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.16/1.53  tff(c_58, plain, (![A_40]: (m1_subset_1(k6_relat_1(A_40), k1_zfmisc_1(k2_zfmisc_1(A_40, A_40))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.16/1.53  tff(c_65, plain, (![A_40]: (m1_subset_1(k6_partfun1(A_40), k1_zfmisc_1(k2_zfmisc_1(A_40, A_40))))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58])).
% 3.16/1.53  tff(c_814, plain, (![A_115, B_116, C_117, D_118]: (k8_relset_1(A_115, B_116, C_117, D_118)=k10_relat_1(C_117, D_118) | ~m1_subset_1(C_117, k1_zfmisc_1(k2_zfmisc_1(A_115, B_116))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.16/1.53  tff(c_817, plain, (![A_40, D_118]: (k8_relset_1(A_40, A_40, k6_partfun1(A_40), D_118)=k10_relat_1(k6_partfun1(A_40), D_118))), inference(resolution, [status(thm)], [c_65, c_814])).
% 3.16/1.53  tff(c_62, plain, (k8_relset_1('#skF_3', '#skF_3', k6_partfun1('#skF_3'), '#skF_4')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.16/1.53  tff(c_948, plain, (k10_relat_1(k6_partfun1('#skF_3'), '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_817, c_62])).
% 3.16/1.53  tff(c_64, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.16/1.53  tff(c_20, plain, (![A_13]: (~v1_xboole_0(k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.16/1.53  tff(c_230, plain, (![A_66, B_67]: (r2_hidden(A_66, B_67) | v1_xboole_0(B_67) | ~m1_subset_1(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.16/1.53  tff(c_8, plain, (![C_12, A_8]: (r1_tarski(C_12, A_8) | ~r2_hidden(C_12, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.16/1.53  tff(c_234, plain, (![A_66, A_8]: (r1_tarski(A_66, A_8) | v1_xboole_0(k1_zfmisc_1(A_8)) | ~m1_subset_1(A_66, k1_zfmisc_1(A_8)))), inference(resolution, [status(thm)], [c_230, c_8])).
% 3.16/1.53  tff(c_239, plain, (![A_68, A_69]: (r1_tarski(A_68, A_69) | ~m1_subset_1(A_68, k1_zfmisc_1(A_69)))), inference(negUnitSimplification, [status(thm)], [c_20, c_234])).
% 3.16/1.53  tff(c_247, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_64, c_239])).
% 3.16/1.53  tff(c_34, plain, (![A_26]: (k2_relat_1(k6_relat_1(A_26))=A_26)), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.16/1.53  tff(c_75, plain, (![A_26]: (k2_relat_1(k6_partfun1(A_26))=A_26)), inference(demodulation, [status(thm), theory('equality')], [c_60, c_34])).
% 3.16/1.53  tff(c_2, plain, (![B_2, A_1]: (k2_tarski(B_2, A_1)=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.16/1.53  tff(c_143, plain, (![A_53, B_54]: (k1_setfam_1(k2_tarski(A_53, B_54))=k3_xboole_0(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.16/1.53  tff(c_174, plain, (![A_62, B_63]: (k1_setfam_1(k2_tarski(A_62, B_63))=k3_xboole_0(B_63, A_62))), inference(superposition, [status(thm), theory('equality')], [c_2, c_143])).
% 3.16/1.53  tff(c_22, plain, (![A_14, B_15]: (k1_setfam_1(k2_tarski(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.16/1.53  tff(c_180, plain, (![B_63, A_62]: (k3_xboole_0(B_63, A_62)=k3_xboole_0(A_62, B_63))), inference(superposition, [status(thm), theory('equality')], [c_174, c_22])).
% 3.16/1.53  tff(c_48, plain, (![A_31]: (v1_relat_1(k6_relat_1(A_31)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.16/1.53  tff(c_68, plain, (![A_31]: (v1_relat_1(k6_partfun1(A_31)))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_48])).
% 3.16/1.53  tff(c_54, plain, (![B_35, A_34]: (k5_relat_1(k6_relat_1(B_35), k6_relat_1(A_34))=k6_relat_1(k3_xboole_0(A_34, B_35)))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.16/1.53  tff(c_306, plain, (![B_82, A_83]: (k5_relat_1(k6_partfun1(B_82), k6_partfun1(A_83))=k6_partfun1(k3_xboole_0(A_83, B_82)))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_60, c_60, c_54])).
% 3.16/1.53  tff(c_36, plain, (![A_27, B_28]: (k5_relat_1(k6_relat_1(A_27), B_28)=k7_relat_1(B_28, A_27) | ~v1_relat_1(B_28))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.16/1.53  tff(c_74, plain, (![A_27, B_28]: (k5_relat_1(k6_partfun1(A_27), B_28)=k7_relat_1(B_28, A_27) | ~v1_relat_1(B_28))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_36])).
% 3.16/1.53  tff(c_312, plain, (![A_83, B_82]: (k7_relat_1(k6_partfun1(A_83), B_82)=k6_partfun1(k3_xboole_0(A_83, B_82)) | ~v1_relat_1(k6_partfun1(A_83)))), inference(superposition, [status(thm), theory('equality')], [c_306, c_74])).
% 3.16/1.53  tff(c_322, plain, (![A_83, B_82]: (k7_relat_1(k6_partfun1(A_83), B_82)=k6_partfun1(k3_xboole_0(A_83, B_82)))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_312])).
% 3.16/1.53  tff(c_40, plain, (![A_29]: (v4_relat_1(k6_relat_1(A_29), A_29))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.16/1.53  tff(c_72, plain, (![A_29]: (v4_relat_1(k6_partfun1(A_29), A_29))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_40])).
% 3.16/1.53  tff(c_417, plain, (![C_88, B_89, A_90]: (v4_relat_1(C_88, B_89) | ~v4_relat_1(C_88, A_90) | ~v1_relat_1(C_88) | ~r1_tarski(A_90, B_89))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.16/1.53  tff(c_419, plain, (![A_29, B_89]: (v4_relat_1(k6_partfun1(A_29), B_89) | ~v1_relat_1(k6_partfun1(A_29)) | ~r1_tarski(A_29, B_89))), inference(resolution, [status(thm)], [c_72, c_417])).
% 3.16/1.53  tff(c_433, plain, (![A_93, B_94]: (v4_relat_1(k6_partfun1(A_93), B_94) | ~r1_tarski(A_93, B_94))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_419])).
% 3.16/1.53  tff(c_28, plain, (![B_21, A_20]: (k7_relat_1(B_21, A_20)=B_21 | ~v4_relat_1(B_21, A_20) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.16/1.53  tff(c_438, plain, (![A_93, B_94]: (k7_relat_1(k6_partfun1(A_93), B_94)=k6_partfun1(A_93) | ~v1_relat_1(k6_partfun1(A_93)) | ~r1_tarski(A_93, B_94))), inference(resolution, [status(thm)], [c_433, c_28])).
% 3.16/1.53  tff(c_474, plain, (![A_99, B_100]: (k6_partfun1(k3_xboole_0(A_99, B_100))=k6_partfun1(A_99) | ~r1_tarski(A_99, B_100))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_322, c_438])).
% 3.16/1.53  tff(c_614, plain, (![A_108, B_109]: (k6_partfun1(k3_xboole_0(A_108, B_109))=k6_partfun1(B_109) | ~r1_tarski(B_109, A_108))), inference(superposition, [status(thm), theory('equality')], [c_180, c_474])).
% 3.16/1.53  tff(c_662, plain, (![A_108, B_109]: (k3_xboole_0(A_108, B_109)=k2_relat_1(k6_partfun1(B_109)) | ~r1_tarski(B_109, A_108))), inference(superposition, [status(thm), theory('equality')], [c_614, c_75])).
% 3.16/1.53  tff(c_710, plain, (![A_110, B_111]: (k3_xboole_0(A_110, B_111)=B_111 | ~r1_tarski(B_111, A_110))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_662])).
% 3.16/1.53  tff(c_718, plain, (k3_xboole_0('#skF_3', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_247, c_710])).
% 3.16/1.53  tff(c_46, plain, (![A_30]: (v1_funct_1(k6_relat_1(A_30)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.16/1.53  tff(c_69, plain, (![A_30]: (v1_funct_1(k6_partfun1(A_30)))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_46])).
% 3.16/1.53  tff(c_50, plain, (![A_31]: (v2_funct_1(k6_relat_1(A_31)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.16/1.53  tff(c_67, plain, (![A_31]: (v2_funct_1(k6_partfun1(A_31)))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_50])).
% 3.16/1.53  tff(c_326, plain, (![A_84, B_85]: (k7_relat_1(k6_partfun1(A_84), B_85)=k6_partfun1(k3_xboole_0(A_84, B_85)))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_312])).
% 3.16/1.53  tff(c_26, plain, (![B_19, A_18]: (k2_relat_1(k7_relat_1(B_19, A_18))=k9_relat_1(B_19, A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.16/1.53  tff(c_336, plain, (![A_84, B_85]: (k2_relat_1(k6_partfun1(k3_xboole_0(A_84, B_85)))=k9_relat_1(k6_partfun1(A_84), B_85) | ~v1_relat_1(k6_partfun1(A_84)))), inference(superposition, [status(thm), theory('equality')], [c_326, c_26])).
% 3.16/1.53  tff(c_345, plain, (![A_84, B_85]: (k9_relat_1(k6_partfun1(A_84), B_85)=k3_xboole_0(A_84, B_85))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_75, c_336])).
% 3.16/1.53  tff(c_32, plain, (![A_26]: (k1_relat_1(k6_relat_1(A_26))=A_26)), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.16/1.53  tff(c_76, plain, (![A_26]: (k1_relat_1(k6_partfun1(A_26))=A_26)), inference(demodulation, [status(thm), theory('equality')], [c_60, c_32])).
% 3.16/1.53  tff(c_895, plain, (![B_123, A_124]: (k10_relat_1(B_123, k9_relat_1(B_123, A_124))=A_124 | ~v2_funct_1(B_123) | ~r1_tarski(A_124, k1_relat_1(B_123)) | ~v1_funct_1(B_123) | ~v1_relat_1(B_123))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.16/1.53  tff(c_900, plain, (![A_26, A_124]: (k10_relat_1(k6_partfun1(A_26), k9_relat_1(k6_partfun1(A_26), A_124))=A_124 | ~v2_funct_1(k6_partfun1(A_26)) | ~r1_tarski(A_124, A_26) | ~v1_funct_1(k6_partfun1(A_26)) | ~v1_relat_1(k6_partfun1(A_26)))), inference(superposition, [status(thm), theory('equality')], [c_76, c_895])).
% 3.16/1.53  tff(c_964, plain, (![A_129, A_130]: (k10_relat_1(k6_partfun1(A_129), k3_xboole_0(A_129, A_130))=A_130 | ~r1_tarski(A_130, A_129))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_69, c_67, c_345, c_900])).
% 3.16/1.53  tff(c_976, plain, (k10_relat_1(k6_partfun1('#skF_3'), '#skF_4')='#skF_4' | ~r1_tarski('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_718, c_964])).
% 3.16/1.53  tff(c_1003, plain, (k10_relat_1(k6_partfun1('#skF_3'), '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_247, c_976])).
% 3.16/1.53  tff(c_1005, plain, $false, inference(negUnitSimplification, [status(thm)], [c_948, c_1003])).
% 3.16/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.16/1.53  
% 3.16/1.53  Inference rules
% 3.16/1.53  ----------------------
% 3.16/1.53  #Ref     : 0
% 3.16/1.53  #Sup     : 227
% 3.16/1.53  #Fact    : 0
% 3.16/1.53  #Define  : 0
% 3.16/1.53  #Split   : 2
% 3.16/1.53  #Chain   : 0
% 3.16/1.53  #Close   : 0
% 3.16/1.53  
% 3.16/1.53  Ordering : KBO
% 3.16/1.53  
% 3.16/1.53  Simplification rules
% 3.16/1.53  ----------------------
% 3.16/1.53  #Subsume      : 21
% 3.16/1.53  #Demod        : 124
% 3.16/1.53  #Tautology    : 115
% 3.16/1.53  #SimpNegUnit  : 2
% 3.16/1.53  #BackRed      : 1
% 3.16/1.53  
% 3.16/1.53  #Partial instantiations: 0
% 3.16/1.53  #Strategies tried      : 1
% 3.16/1.53  
% 3.16/1.53  Timing (in seconds)
% 3.16/1.53  ----------------------
% 3.16/1.53  Preprocessing        : 0.37
% 3.16/1.53  Parsing              : 0.19
% 3.16/1.53  CNF conversion       : 0.02
% 3.16/1.53  Main loop            : 0.39
% 3.16/1.53  Inferencing          : 0.14
% 3.16/1.53  Reduction            : 0.15
% 3.16/1.53  Demodulation         : 0.11
% 3.16/1.53  BG Simplification    : 0.02
% 3.16/1.53  Subsumption          : 0.06
% 3.16/1.53  Abstraction          : 0.03
% 3.16/1.53  MUC search           : 0.00
% 3.16/1.53  Cooper               : 0.00
% 3.16/1.53  Total                : 0.80
% 3.16/1.53  Index Insertion      : 0.00
% 3.16/1.53  Index Deletion       : 0.00
% 3.16/1.53  Index Matching       : 0.00
% 3.16/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
