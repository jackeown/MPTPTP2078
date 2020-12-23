%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:52 EST 2020

% Result     : Theorem 3.06s
% Output     : CNFRefutation 3.14s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 143 expanded)
%              Number of leaves         :   49 (  68 expanded)
%              Depth                    :   13
%              Number of atoms          :  127 ( 205 expanded)
%              Number of equality atoms :   54 (  84 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k5_relset_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff(k5_relset_1,type,(
    k5_relset_1: ( $i * $i * $i * $i ) > $i )).

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

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(f_113,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
          & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_102,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_98,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_72,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_94,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(f_106,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => m1_subset_1(k5_relset_1(A,C,D,B),k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_relset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k3_xboole_0(B,k2_zfmisc_1(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t124_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_39,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_68,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

tff(c_50,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_722,plain,(
    ! [A_186,B_187,C_188,D_189] :
      ( k8_relset_1(A_186,B_187,C_188,D_189) = k10_relat_1(C_188,D_189)
      | ~ m1_subset_1(C_188,k1_zfmisc_1(k2_zfmisc_1(A_186,B_187))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_729,plain,(
    ! [D_189] : k8_relset_1('#skF_1','#skF_2','#skF_3',D_189) = k10_relat_1('#skF_3',D_189) ),
    inference(resolution,[status(thm)],[c_50,c_722])).

tff(c_612,plain,(
    ! [A_165,B_166,C_167] :
      ( k1_relset_1(A_165,B_166,C_167) = k1_relat_1(C_167)
      | ~ m1_subset_1(C_167,k1_zfmisc_1(k2_zfmisc_1(A_165,B_166))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_621,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_612])).

tff(c_122,plain,(
    ! [C_64,A_65,B_66] :
      ( v1_relat_1(C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_131,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_122])).

tff(c_189,plain,(
    ! [C_81,A_82,B_83] :
      ( v4_relat_1(C_81,A_82)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_198,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_189])).

tff(c_199,plain,(
    ! [B_84,A_85] :
      ( k7_relat_1(B_84,A_85) = B_84
      | ~ v4_relat_1(B_84,A_85)
      | ~ v1_relat_1(B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_202,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_198,c_199])).

tff(c_205,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_202])).

tff(c_18,plain,(
    ! [B_15,A_14] :
      ( k2_relat_1(k7_relat_1(B_15,A_14)) = k9_relat_1(B_15,A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_209,plain,
    ( k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_205,c_18])).

tff(c_213,plain,(
    k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_209])).

tff(c_388,plain,(
    ! [A_119,B_120,C_121,D_122] :
      ( k7_relset_1(A_119,B_120,C_121,D_122) = k9_relat_1(C_121,D_122)
      | ~ m1_subset_1(C_121,k1_zfmisc_1(k2_zfmisc_1(A_119,B_120))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_395,plain,(
    ! [D_122] : k7_relset_1('#skF_1','#skF_2','#skF_3',D_122) = k9_relat_1('#skF_3',D_122) ),
    inference(resolution,[status(thm)],[c_50,c_388])).

tff(c_285,plain,(
    ! [A_99,B_100,C_101] :
      ( k2_relset_1(A_99,B_100,C_101) = k2_relat_1(C_101)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_99,B_100))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_294,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_285])).

tff(c_48,plain,
    ( k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != k1_relset_1('#skF_1','#skF_2','#skF_3')
    | k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_89,plain,(
    k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_295,plain,(
    k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_294,c_89])).

tff(c_396,plain,(
    k9_relat_1('#skF_3','#skF_1') != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_395,c_295])).

tff(c_399,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_213,c_396])).

tff(c_400,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != k1_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_622,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_621,c_400])).

tff(c_730,plain,(
    k10_relat_1('#skF_3','#skF_2') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_729,c_622])).

tff(c_434,plain,(
    ! [C_127,A_128,B_129] :
      ( v1_relat_1(C_127)
      | ~ m1_subset_1(C_127,k1_zfmisc_1(k2_zfmisc_1(A_128,B_129))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_443,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_434])).

tff(c_28,plain,(
    ! [A_22] :
      ( k7_relat_1(A_22,k1_relat_1(A_22)) = A_22
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_745,plain,(
    ! [A_195,B_196,C_197,D_198] :
      ( k5_relset_1(A_195,B_196,C_197,D_198) = k7_relat_1(C_197,D_198)
      | ~ m1_subset_1(C_197,k1_zfmisc_1(k2_zfmisc_1(A_195,B_196))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_752,plain,(
    ! [D_198] : k5_relset_1('#skF_1','#skF_2','#skF_3',D_198) = k7_relat_1('#skF_3',D_198) ),
    inference(resolution,[status(thm)],[c_50,c_745])).

tff(c_767,plain,(
    ! [A_204,C_205,D_206,B_207] :
      ( m1_subset_1(k5_relset_1(A_204,C_205,D_206,B_207),k1_zfmisc_1(k2_zfmisc_1(B_207,C_205)))
      | ~ m1_subset_1(D_206,k1_zfmisc_1(k2_zfmisc_1(A_204,C_205))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_794,plain,(
    ! [D_198] :
      ( m1_subset_1(k7_relat_1('#skF_3',D_198),k1_zfmisc_1(k2_zfmisc_1(D_198,'#skF_2')))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_752,c_767])).

tff(c_806,plain,(
    ! [D_208] : m1_subset_1(k7_relat_1('#skF_3',D_208),k1_zfmisc_1(k2_zfmisc_1(D_208,'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_794])).

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(A_7,B_8)
      | ~ m1_subset_1(A_7,k1_zfmisc_1(B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_908,plain,(
    ! [D_216] : r1_tarski(k7_relat_1('#skF_3',D_216),k2_zfmisc_1(D_216,'#skF_2')) ),
    inference(resolution,[status(thm)],[c_806,c_8])).

tff(c_939,plain,
    ( r1_tarski('#skF_3',k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_908])).

tff(c_954,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_443,c_939])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = A_1
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1027,plain,(
    k3_xboole_0('#skF_3',k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_954,c_2])).

tff(c_16,plain,(
    ! [B_13,A_12] :
      ( k3_xboole_0(B_13,k2_zfmisc_1(k1_relat_1(B_13),A_12)) = k8_relat_1(A_12,B_13)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1118,plain,
    ( k8_relat_1('#skF_2','#skF_3') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1027,c_16])).

tff(c_1125,plain,(
    k8_relat_1('#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_443,c_1118])).

tff(c_14,plain,(
    ! [B_11,A_10] :
      ( k5_relat_1(B_11,k6_relat_1(A_10)) = k8_relat_1(A_10,B_11)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_12,plain,(
    ! [A_9] : v1_relat_1(k6_relat_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_24,plain,(
    ! [A_21] : k1_relat_1(k6_relat_1(A_21)) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_633,plain,(
    ! [A_171,B_172] :
      ( k10_relat_1(A_171,k1_relat_1(B_172)) = k1_relat_1(k5_relat_1(A_171,B_172))
      | ~ v1_relat_1(B_172)
      | ~ v1_relat_1(A_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_642,plain,(
    ! [A_171,A_21] :
      ( k1_relat_1(k5_relat_1(A_171,k6_relat_1(A_21))) = k10_relat_1(A_171,A_21)
      | ~ v1_relat_1(k6_relat_1(A_21))
      | ~ v1_relat_1(A_171) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_633])).

tff(c_647,plain,(
    ! [A_173,A_174] :
      ( k1_relat_1(k5_relat_1(A_173,k6_relat_1(A_174))) = k10_relat_1(A_173,A_174)
      | ~ v1_relat_1(A_173) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_642])).

tff(c_668,plain,(
    ! [A_10,B_11] :
      ( k1_relat_1(k8_relat_1(A_10,B_11)) = k10_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11)
      | ~ v1_relat_1(B_11) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_647])).

tff(c_1132,plain,
    ( k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1125,c_668])).

tff(c_1136,plain,(
    k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_443,c_443,c_1132])).

tff(c_1138,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_730,c_1136])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:24:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.06/1.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.06/1.48  
% 3.06/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.06/1.48  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k5_relset_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.06/1.48  
% 3.06/1.48  %Foreground sorts:
% 3.06/1.48  
% 3.06/1.48  
% 3.06/1.48  %Background operators:
% 3.06/1.48  
% 3.06/1.48  
% 3.06/1.48  %Foreground operators:
% 3.06/1.48  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.06/1.48  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 3.06/1.48  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 3.06/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.06/1.48  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.06/1.48  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.06/1.48  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.06/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.06/1.48  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.06/1.48  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.06/1.48  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.06/1.48  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.06/1.48  tff('#skF_2', type, '#skF_2': $i).
% 3.06/1.48  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.06/1.48  tff('#skF_3', type, '#skF_3': $i).
% 3.06/1.48  tff('#skF_1', type, '#skF_1': $i).
% 3.06/1.48  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.06/1.48  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.06/1.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.06/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.06/1.48  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.06/1.48  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.06/1.48  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.06/1.48  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.06/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.06/1.48  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.06/1.48  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.06/1.48  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.06/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.06/1.48  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.06/1.48  
% 3.14/1.50  tff(f_113, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 3.14/1.50  tff(f_102, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.14/1.50  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.14/1.50  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.14/1.50  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.14/1.50  tff(f_64, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 3.14/1.50  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 3.14/1.50  tff(f_98, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.14/1.50  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.14/1.50  tff(f_72, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_relat_1)).
% 3.14/1.50  tff(f_94, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 3.14/1.50  tff(f_106, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => m1_subset_1(k5_relset_1(A, C, D, B), k1_zfmisc_1(k2_zfmisc_1(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_relset_1)).
% 3.14/1.50  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.14/1.50  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.14/1.50  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k3_xboole_0(B, k2_zfmisc_1(k1_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t124_relat_1)).
% 3.14/1.50  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_relat_1)).
% 3.14/1.50  tff(f_39, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 3.14/1.50  tff(f_68, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 3.14/1.50  tff(f_58, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 3.14/1.50  tff(c_50, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.14/1.50  tff(c_722, plain, (![A_186, B_187, C_188, D_189]: (k8_relset_1(A_186, B_187, C_188, D_189)=k10_relat_1(C_188, D_189) | ~m1_subset_1(C_188, k1_zfmisc_1(k2_zfmisc_1(A_186, B_187))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.14/1.50  tff(c_729, plain, (![D_189]: (k8_relset_1('#skF_1', '#skF_2', '#skF_3', D_189)=k10_relat_1('#skF_3', D_189))), inference(resolution, [status(thm)], [c_50, c_722])).
% 3.14/1.50  tff(c_612, plain, (![A_165, B_166, C_167]: (k1_relset_1(A_165, B_166, C_167)=k1_relat_1(C_167) | ~m1_subset_1(C_167, k1_zfmisc_1(k2_zfmisc_1(A_165, B_166))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.14/1.50  tff(c_621, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_612])).
% 3.14/1.50  tff(c_122, plain, (![C_64, A_65, B_66]: (v1_relat_1(C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.14/1.50  tff(c_131, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_122])).
% 3.14/1.50  tff(c_189, plain, (![C_81, A_82, B_83]: (v4_relat_1(C_81, A_82) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.14/1.50  tff(c_198, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_50, c_189])).
% 3.14/1.50  tff(c_199, plain, (![B_84, A_85]: (k7_relat_1(B_84, A_85)=B_84 | ~v4_relat_1(B_84, A_85) | ~v1_relat_1(B_84))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.14/1.50  tff(c_202, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_198, c_199])).
% 3.14/1.50  tff(c_205, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_131, c_202])).
% 3.14/1.50  tff(c_18, plain, (![B_15, A_14]: (k2_relat_1(k7_relat_1(B_15, A_14))=k9_relat_1(B_15, A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.14/1.50  tff(c_209, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_205, c_18])).
% 3.14/1.50  tff(c_213, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_131, c_209])).
% 3.14/1.50  tff(c_388, plain, (![A_119, B_120, C_121, D_122]: (k7_relset_1(A_119, B_120, C_121, D_122)=k9_relat_1(C_121, D_122) | ~m1_subset_1(C_121, k1_zfmisc_1(k2_zfmisc_1(A_119, B_120))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.14/1.50  tff(c_395, plain, (![D_122]: (k7_relset_1('#skF_1', '#skF_2', '#skF_3', D_122)=k9_relat_1('#skF_3', D_122))), inference(resolution, [status(thm)], [c_50, c_388])).
% 3.14/1.50  tff(c_285, plain, (![A_99, B_100, C_101]: (k2_relset_1(A_99, B_100, C_101)=k2_relat_1(C_101) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_99, B_100))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.14/1.50  tff(c_294, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_285])).
% 3.14/1.50  tff(c_48, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!=k1_relset_1('#skF_1', '#skF_2', '#skF_3') | k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.14/1.50  tff(c_89, plain, (k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_48])).
% 3.14/1.50  tff(c_295, plain, (k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_294, c_89])).
% 3.14/1.50  tff(c_396, plain, (k9_relat_1('#skF_3', '#skF_1')!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_395, c_295])).
% 3.14/1.50  tff(c_399, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_213, c_396])).
% 3.14/1.50  tff(c_400, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!=k1_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_48])).
% 3.14/1.50  tff(c_622, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_621, c_400])).
% 3.14/1.50  tff(c_730, plain, (k10_relat_1('#skF_3', '#skF_2')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_729, c_622])).
% 3.14/1.50  tff(c_434, plain, (![C_127, A_128, B_129]: (v1_relat_1(C_127) | ~m1_subset_1(C_127, k1_zfmisc_1(k2_zfmisc_1(A_128, B_129))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.14/1.50  tff(c_443, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_434])).
% 3.14/1.50  tff(c_28, plain, (![A_22]: (k7_relat_1(A_22, k1_relat_1(A_22))=A_22 | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.14/1.50  tff(c_745, plain, (![A_195, B_196, C_197, D_198]: (k5_relset_1(A_195, B_196, C_197, D_198)=k7_relat_1(C_197, D_198) | ~m1_subset_1(C_197, k1_zfmisc_1(k2_zfmisc_1(A_195, B_196))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.14/1.50  tff(c_752, plain, (![D_198]: (k5_relset_1('#skF_1', '#skF_2', '#skF_3', D_198)=k7_relat_1('#skF_3', D_198))), inference(resolution, [status(thm)], [c_50, c_745])).
% 3.14/1.50  tff(c_767, plain, (![A_204, C_205, D_206, B_207]: (m1_subset_1(k5_relset_1(A_204, C_205, D_206, B_207), k1_zfmisc_1(k2_zfmisc_1(B_207, C_205))) | ~m1_subset_1(D_206, k1_zfmisc_1(k2_zfmisc_1(A_204, C_205))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.14/1.50  tff(c_794, plain, (![D_198]: (m1_subset_1(k7_relat_1('#skF_3', D_198), k1_zfmisc_1(k2_zfmisc_1(D_198, '#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(superposition, [status(thm), theory('equality')], [c_752, c_767])).
% 3.14/1.50  tff(c_806, plain, (![D_208]: (m1_subset_1(k7_relat_1('#skF_3', D_208), k1_zfmisc_1(k2_zfmisc_1(D_208, '#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_794])).
% 3.14/1.50  tff(c_8, plain, (![A_7, B_8]: (r1_tarski(A_7, B_8) | ~m1_subset_1(A_7, k1_zfmisc_1(B_8)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.14/1.50  tff(c_908, plain, (![D_216]: (r1_tarski(k7_relat_1('#skF_3', D_216), k2_zfmisc_1(D_216, '#skF_2')))), inference(resolution, [status(thm)], [c_806, c_8])).
% 3.14/1.50  tff(c_939, plain, (r1_tarski('#skF_3', k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_28, c_908])).
% 3.14/1.50  tff(c_954, plain, (r1_tarski('#skF_3', k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_443, c_939])).
% 3.14/1.50  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=A_1 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.14/1.50  tff(c_1027, plain, (k3_xboole_0('#skF_3', k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))='#skF_3'), inference(resolution, [status(thm)], [c_954, c_2])).
% 3.14/1.50  tff(c_16, plain, (![B_13, A_12]: (k3_xboole_0(B_13, k2_zfmisc_1(k1_relat_1(B_13), A_12))=k8_relat_1(A_12, B_13) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.14/1.50  tff(c_1118, plain, (k8_relat_1('#skF_2', '#skF_3')='#skF_3' | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1027, c_16])).
% 3.14/1.50  tff(c_1125, plain, (k8_relat_1('#skF_2', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_443, c_1118])).
% 3.14/1.50  tff(c_14, plain, (![B_11, A_10]: (k5_relat_1(B_11, k6_relat_1(A_10))=k8_relat_1(A_10, B_11) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.14/1.50  tff(c_12, plain, (![A_9]: (v1_relat_1(k6_relat_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.14/1.50  tff(c_24, plain, (![A_21]: (k1_relat_1(k6_relat_1(A_21))=A_21)), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.14/1.50  tff(c_633, plain, (![A_171, B_172]: (k10_relat_1(A_171, k1_relat_1(B_172))=k1_relat_1(k5_relat_1(A_171, B_172)) | ~v1_relat_1(B_172) | ~v1_relat_1(A_171))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.14/1.50  tff(c_642, plain, (![A_171, A_21]: (k1_relat_1(k5_relat_1(A_171, k6_relat_1(A_21)))=k10_relat_1(A_171, A_21) | ~v1_relat_1(k6_relat_1(A_21)) | ~v1_relat_1(A_171))), inference(superposition, [status(thm), theory('equality')], [c_24, c_633])).
% 3.14/1.50  tff(c_647, plain, (![A_173, A_174]: (k1_relat_1(k5_relat_1(A_173, k6_relat_1(A_174)))=k10_relat_1(A_173, A_174) | ~v1_relat_1(A_173))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_642])).
% 3.14/1.50  tff(c_668, plain, (![A_10, B_11]: (k1_relat_1(k8_relat_1(A_10, B_11))=k10_relat_1(B_11, A_10) | ~v1_relat_1(B_11) | ~v1_relat_1(B_11))), inference(superposition, [status(thm), theory('equality')], [c_14, c_647])).
% 3.14/1.50  tff(c_1132, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1125, c_668])).
% 3.14/1.50  tff(c_1136, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_443, c_443, c_1132])).
% 3.14/1.50  tff(c_1138, plain, $false, inference(negUnitSimplification, [status(thm)], [c_730, c_1136])).
% 3.14/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.14/1.50  
% 3.14/1.50  Inference rules
% 3.14/1.50  ----------------------
% 3.14/1.50  #Ref     : 0
% 3.14/1.50  #Sup     : 261
% 3.14/1.50  #Fact    : 0
% 3.14/1.50  #Define  : 0
% 3.14/1.50  #Split   : 1
% 3.14/1.50  #Chain   : 0
% 3.14/1.50  #Close   : 0
% 3.14/1.50  
% 3.14/1.50  Ordering : KBO
% 3.14/1.50  
% 3.14/1.50  Simplification rules
% 3.14/1.50  ----------------------
% 3.14/1.50  #Subsume      : 0
% 3.14/1.50  #Demod        : 90
% 3.14/1.50  #Tautology    : 145
% 3.14/1.50  #SimpNegUnit  : 1
% 3.14/1.50  #BackRed      : 5
% 3.14/1.50  
% 3.14/1.50  #Partial instantiations: 0
% 3.14/1.50  #Strategies tried      : 1
% 3.14/1.50  
% 3.14/1.50  Timing (in seconds)
% 3.14/1.50  ----------------------
% 3.14/1.50  Preprocessing        : 0.32
% 3.14/1.50  Parsing              : 0.18
% 3.14/1.50  CNF conversion       : 0.02
% 3.14/1.50  Main loop            : 0.38
% 3.14/1.50  Inferencing          : 0.16
% 3.14/1.50  Reduction            : 0.12
% 3.14/1.50  Demodulation         : 0.08
% 3.14/1.50  BG Simplification    : 0.02
% 3.14/1.50  Subsumption          : 0.04
% 3.14/1.50  Abstraction          : 0.02
% 3.14/1.50  MUC search           : 0.00
% 3.14/1.50  Cooper               : 0.00
% 3.14/1.50  Total                : 0.74
% 3.14/1.50  Index Insertion      : 0.00
% 3.14/1.50  Index Deletion       : 0.00
% 3.14/1.50  Index Matching       : 0.00
% 3.14/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
