%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:43 EST 2020

% Result     : Theorem 9.92s
% Output     : CNFRefutation 9.92s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 269 expanded)
%              Number of leaves         :   45 ( 108 expanded)
%              Depth                    :   11
%              Number of atoms          :  170 ( 535 expanded)
%              Number of equality atoms :   46 ( 102 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_128,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_36,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_106,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_116,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => ( r1_tarski(k1_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relset_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_59,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_110,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_38,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_81,axiom,(
    ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_62,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_165,plain,(
    ! [C_66,A_67,B_68] :
      ( v1_relat_1(C_66)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_177,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_165])).

tff(c_38,plain,(
    ! [B_20,A_19] :
      ( r1_tarski(k1_relat_1(B_20),A_19)
      | ~ v4_relat_1(B_20,A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_10,plain,(
    ! [B_3] : r1_tarski(B_3,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_32,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(A_14,k1_zfmisc_1(B_15))
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_397,plain,(
    ! [C_115,A_116,B_117] :
      ( v1_xboole_0(C_115)
      | ~ m1_subset_1(C_115,k1_zfmisc_1(k2_zfmisc_1(A_116,B_117)))
      | ~ v1_xboole_0(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_434,plain,(
    ! [A_125,A_126,B_127] :
      ( v1_xboole_0(A_125)
      | ~ v1_xboole_0(A_126)
      | ~ r1_tarski(A_125,k2_zfmisc_1(A_126,B_127)) ) ),
    inference(resolution,[status(thm)],[c_32,c_397])).

tff(c_455,plain,(
    ! [A_128,B_129] :
      ( v1_xboole_0(k2_zfmisc_1(A_128,B_129))
      | ~ v1_xboole_0(A_128) ) ),
    inference(resolution,[status(thm)],[c_10,c_434])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_470,plain,(
    ! [A_131,B_132] :
      ( k2_zfmisc_1(A_131,B_132) = k1_xboole_0
      | ~ v1_xboole_0(A_131) ) ),
    inference(resolution,[status(thm)],[c_455,c_4])).

tff(c_481,plain,(
    ! [B_133] : k2_zfmisc_1(k1_xboole_0,B_133) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_470])).

tff(c_410,plain,(
    ! [A_14,A_116,B_117] :
      ( v1_xboole_0(A_14)
      | ~ v1_xboole_0(A_116)
      | ~ r1_tarski(A_14,k2_zfmisc_1(A_116,B_117)) ) ),
    inference(resolution,[status(thm)],[c_32,c_397])).

tff(c_489,plain,(
    ! [A_14] :
      ( v1_xboole_0(A_14)
      | ~ v1_xboole_0(k1_xboole_0)
      | ~ r1_tarski(A_14,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_481,c_410])).

tff(c_532,plain,(
    ! [A_134] :
      ( v1_xboole_0(A_134)
      | ~ r1_tarski(A_134,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_489])).

tff(c_545,plain,(
    ! [B_20] :
      ( v1_xboole_0(k1_relat_1(B_20))
      | ~ v4_relat_1(B_20,k1_xboole_0)
      | ~ v1_relat_1(B_20) ) ),
    inference(resolution,[status(thm)],[c_38,c_532])).

tff(c_720,plain,(
    ! [D_151,B_152,C_153,A_154] :
      ( m1_subset_1(D_151,k1_zfmisc_1(k2_zfmisc_1(B_152,C_153)))
      | ~ r1_tarski(k1_relat_1(D_151),B_152)
      | ~ m1_subset_1(D_151,k1_zfmisc_1(k2_zfmisc_1(A_154,C_153))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_758,plain,(
    ! [B_156] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_156,'#skF_2')))
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_156) ) ),
    inference(resolution,[status(thm)],[c_62,c_720])).

tff(c_52,plain,(
    ! [C_35,A_32,B_33] :
      ( v1_xboole_0(C_35)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_32,B_33)))
      | ~ v1_xboole_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_790,plain,(
    ! [B_156] :
      ( v1_xboole_0('#skF_4')
      | ~ v1_xboole_0(B_156)
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_156) ) ),
    inference(resolution,[status(thm)],[c_758,c_52])).

tff(c_812,plain,(
    ! [B_158] :
      ( ~ v1_xboole_0(B_158)
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_158) ) ),
    inference(splitLeft,[status(thm)],[c_790])).

tff(c_824,plain,(
    ~ v1_xboole_0(k1_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_10,c_812])).

tff(c_827,plain,
    ( ~ v4_relat_1('#skF_4',k1_xboole_0)
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_545,c_824])).

tff(c_830,plain,(
    ~ v4_relat_1('#skF_4',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_827])).

tff(c_40,plain,(
    ! [B_22,A_21] :
      ( r1_tarski(k9_relat_1(B_22,A_21),k2_relat_1(B_22))
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_28,plain,(
    ! [A_13] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_108,plain,(
    ! [A_58,B_59] :
      ( r1_tarski(A_58,B_59)
      | ~ m1_subset_1(A_58,k1_zfmisc_1(B_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_116,plain,(
    ! [A_13] : r1_tarski(k1_xboole_0,A_13) ),
    inference(resolution,[status(thm)],[c_28,c_108])).

tff(c_66,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_44,plain,(
    ! [B_25,A_24] :
      ( k1_tarski(k1_funct_1(B_25,A_24)) = k2_relat_1(B_25)
      | k1_tarski(A_24) != k1_relat_1(B_25)
      | ~ v1_funct_1(B_25)
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_414,plain,(
    ! [A_118,B_119,C_120,D_121] :
      ( k7_relset_1(A_118,B_119,C_120,D_121) = k9_relat_1(C_120,D_121)
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_zfmisc_1(A_118,B_119))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_423,plain,(
    ! [D_121] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_121) = k9_relat_1('#skF_4',D_121) ),
    inference(resolution,[status(thm)],[c_62,c_414])).

tff(c_58,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_460,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_423,c_58])).

tff(c_615,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_460])).

tff(c_617,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_66,c_615])).

tff(c_1011,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_617])).

tff(c_250,plain,(
    ! [C_88,A_89,B_90] :
      ( v4_relat_1(C_88,A_89)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_262,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_62,c_250])).

tff(c_12,plain,(
    ! [A_4] : k2_tarski(A_4,A_4) = k1_tarski(A_4) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_835,plain,(
    ! [B_159,C_160,A_161] :
      ( k2_tarski(B_159,C_160) = A_161
      | k1_tarski(C_160) = A_161
      | k1_tarski(B_159) = A_161
      | k1_xboole_0 = A_161
      | ~ r1_tarski(A_161,k2_tarski(B_159,C_160)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_852,plain,(
    ! [A_4,A_161] :
      ( k2_tarski(A_4,A_4) = A_161
      | k1_tarski(A_4) = A_161
      | k1_tarski(A_4) = A_161
      | k1_xboole_0 = A_161
      | ~ r1_tarski(A_161,k1_tarski(A_4)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_835])).

tff(c_4639,plain,(
    ! [A_396,A_397] :
      ( k1_tarski(A_396) = A_397
      | k1_tarski(A_396) = A_397
      | k1_tarski(A_396) = A_397
      | k1_xboole_0 = A_397
      | ~ r1_tarski(A_397,k1_tarski(A_396)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_852])).

tff(c_6759,plain,(
    ! [A_498,B_499] :
      ( k1_tarski(A_498) = k1_relat_1(B_499)
      | k1_relat_1(B_499) = k1_xboole_0
      | ~ v4_relat_1(B_499,k1_tarski(A_498))
      | ~ v1_relat_1(B_499) ) ),
    inference(resolution,[status(thm)],[c_38,c_4639])).

tff(c_6793,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_262,c_6759])).

tff(c_6817,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_6793])).

tff(c_6818,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_1011,c_6817])).

tff(c_476,plain,(
    ! [B_132] : k2_zfmisc_1(k1_xboole_0,B_132) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_470])).

tff(c_787,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(k1_relat_1('#skF_4'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_476,c_758])).

tff(c_890,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_787])).

tff(c_6839,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6818,c_890])).

tff(c_6861,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_6839])).

tff(c_6862,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_617])).

tff(c_6923,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_6862])).

tff(c_6927,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_6923])).

tff(c_6928,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_787])).

tff(c_50,plain,(
    ! [C_31,A_29,B_30] :
      ( v4_relat_1(C_31,A_29)
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_503,plain,(
    ! [C_31] :
      ( v4_relat_1(C_31,k1_xboole_0)
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_481,c_50])).

tff(c_6934,plain,(
    v4_relat_1('#skF_4',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6928,c_503])).

tff(c_6950,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_830,c_6934])).

tff(c_6951,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_790])).

tff(c_6958,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_6951,c_4])).

tff(c_6981,plain,(
    ! [A_13] : r1_tarski('#skF_4',A_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6958,c_116])).

tff(c_42,plain,(
    ! [A_23] : k9_relat_1(k1_xboole_0,A_23) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_6982,plain,(
    ! [A_23] : k9_relat_1('#skF_4',A_23) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6958,c_6958,c_42])).

tff(c_7085,plain,(
    ~ r1_tarski('#skF_4',k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6982,c_460])).

tff(c_7089,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6981,c_7085])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:54:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.92/3.63  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.92/3.64  
% 9.92/3.64  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.92/3.65  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 9.92/3.65  
% 9.92/3.65  %Foreground sorts:
% 9.92/3.65  
% 9.92/3.65  
% 9.92/3.65  %Background operators:
% 9.92/3.65  
% 9.92/3.65  
% 9.92/3.65  %Foreground operators:
% 9.92/3.65  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.92/3.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.92/3.65  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.92/3.65  tff(k1_tarski, type, k1_tarski: $i > $i).
% 9.92/3.65  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.92/3.65  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.92/3.65  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 9.92/3.65  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.92/3.65  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 9.92/3.65  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.92/3.65  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.92/3.65  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 9.92/3.65  tff('#skF_2', type, '#skF_2': $i).
% 9.92/3.65  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 9.92/3.65  tff('#skF_3', type, '#skF_3': $i).
% 9.92/3.65  tff('#skF_1', type, '#skF_1': $i).
% 9.92/3.65  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 9.92/3.65  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.92/3.65  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 9.92/3.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.92/3.65  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.92/3.65  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.92/3.65  tff('#skF_4', type, '#skF_4': $i).
% 9.92/3.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.92/3.65  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 9.92/3.65  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.92/3.65  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.92/3.65  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.92/3.65  
% 9.92/3.67  tff(f_128, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_2)).
% 9.92/3.67  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 9.92/3.67  tff(f_75, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 9.92/3.67  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 9.92/3.67  tff(f_36, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.92/3.67  tff(f_63, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 9.92/3.67  tff(f_106, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc3_relset_1)).
% 9.92/3.67  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 9.92/3.67  tff(f_116, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (r1_tarski(k1_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_relset_1)).
% 9.92/3.67  tff(f_79, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_relat_1)).
% 9.92/3.67  tff(f_59, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 9.92/3.67  tff(f_89, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 9.92/3.67  tff(f_110, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 9.92/3.67  tff(f_99, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 9.92/3.67  tff(f_38, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 9.92/3.67  tff(f_57, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 9.92/3.67  tff(f_81, axiom, (![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t150_relat_1)).
% 9.92/3.67  tff(c_62, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_128])).
% 9.92/3.67  tff(c_165, plain, (![C_66, A_67, B_68]: (v1_relat_1(C_66) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 9.92/3.67  tff(c_177, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_165])).
% 9.92/3.67  tff(c_38, plain, (![B_20, A_19]: (r1_tarski(k1_relat_1(B_20), A_19) | ~v4_relat_1(B_20, A_19) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_75])).
% 9.92/3.67  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 9.92/3.67  tff(c_10, plain, (![B_3]: (r1_tarski(B_3, B_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 9.92/3.67  tff(c_32, plain, (![A_14, B_15]: (m1_subset_1(A_14, k1_zfmisc_1(B_15)) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_63])).
% 9.92/3.67  tff(c_397, plain, (![C_115, A_116, B_117]: (v1_xboole_0(C_115) | ~m1_subset_1(C_115, k1_zfmisc_1(k2_zfmisc_1(A_116, B_117))) | ~v1_xboole_0(A_116))), inference(cnfTransformation, [status(thm)], [f_106])).
% 9.92/3.67  tff(c_434, plain, (![A_125, A_126, B_127]: (v1_xboole_0(A_125) | ~v1_xboole_0(A_126) | ~r1_tarski(A_125, k2_zfmisc_1(A_126, B_127)))), inference(resolution, [status(thm)], [c_32, c_397])).
% 9.92/3.67  tff(c_455, plain, (![A_128, B_129]: (v1_xboole_0(k2_zfmisc_1(A_128, B_129)) | ~v1_xboole_0(A_128))), inference(resolution, [status(thm)], [c_10, c_434])).
% 9.92/3.67  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 9.92/3.67  tff(c_470, plain, (![A_131, B_132]: (k2_zfmisc_1(A_131, B_132)=k1_xboole_0 | ~v1_xboole_0(A_131))), inference(resolution, [status(thm)], [c_455, c_4])).
% 9.92/3.67  tff(c_481, plain, (![B_133]: (k2_zfmisc_1(k1_xboole_0, B_133)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_470])).
% 9.92/3.67  tff(c_410, plain, (![A_14, A_116, B_117]: (v1_xboole_0(A_14) | ~v1_xboole_0(A_116) | ~r1_tarski(A_14, k2_zfmisc_1(A_116, B_117)))), inference(resolution, [status(thm)], [c_32, c_397])).
% 9.92/3.67  tff(c_489, plain, (![A_14]: (v1_xboole_0(A_14) | ~v1_xboole_0(k1_xboole_0) | ~r1_tarski(A_14, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_481, c_410])).
% 9.92/3.67  tff(c_532, plain, (![A_134]: (v1_xboole_0(A_134) | ~r1_tarski(A_134, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_489])).
% 9.92/3.67  tff(c_545, plain, (![B_20]: (v1_xboole_0(k1_relat_1(B_20)) | ~v4_relat_1(B_20, k1_xboole_0) | ~v1_relat_1(B_20))), inference(resolution, [status(thm)], [c_38, c_532])).
% 9.92/3.67  tff(c_720, plain, (![D_151, B_152, C_153, A_154]: (m1_subset_1(D_151, k1_zfmisc_1(k2_zfmisc_1(B_152, C_153))) | ~r1_tarski(k1_relat_1(D_151), B_152) | ~m1_subset_1(D_151, k1_zfmisc_1(k2_zfmisc_1(A_154, C_153))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 9.92/3.67  tff(c_758, plain, (![B_156]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_156, '#skF_2'))) | ~r1_tarski(k1_relat_1('#skF_4'), B_156))), inference(resolution, [status(thm)], [c_62, c_720])).
% 9.92/3.67  tff(c_52, plain, (![C_35, A_32, B_33]: (v1_xboole_0(C_35) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_32, B_33))) | ~v1_xboole_0(A_32))), inference(cnfTransformation, [status(thm)], [f_106])).
% 9.92/3.67  tff(c_790, plain, (![B_156]: (v1_xboole_0('#skF_4') | ~v1_xboole_0(B_156) | ~r1_tarski(k1_relat_1('#skF_4'), B_156))), inference(resolution, [status(thm)], [c_758, c_52])).
% 9.92/3.67  tff(c_812, plain, (![B_158]: (~v1_xboole_0(B_158) | ~r1_tarski(k1_relat_1('#skF_4'), B_158))), inference(splitLeft, [status(thm)], [c_790])).
% 9.92/3.67  tff(c_824, plain, (~v1_xboole_0(k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_10, c_812])).
% 9.92/3.67  tff(c_827, plain, (~v4_relat_1('#skF_4', k1_xboole_0) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_545, c_824])).
% 9.92/3.67  tff(c_830, plain, (~v4_relat_1('#skF_4', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_177, c_827])).
% 9.92/3.67  tff(c_40, plain, (![B_22, A_21]: (r1_tarski(k9_relat_1(B_22, A_21), k2_relat_1(B_22)) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_79])).
% 9.92/3.67  tff(c_28, plain, (![A_13]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 9.92/3.67  tff(c_108, plain, (![A_58, B_59]: (r1_tarski(A_58, B_59) | ~m1_subset_1(A_58, k1_zfmisc_1(B_59)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 9.92/3.67  tff(c_116, plain, (![A_13]: (r1_tarski(k1_xboole_0, A_13))), inference(resolution, [status(thm)], [c_28, c_108])).
% 9.92/3.67  tff(c_66, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_128])).
% 9.92/3.67  tff(c_44, plain, (![B_25, A_24]: (k1_tarski(k1_funct_1(B_25, A_24))=k2_relat_1(B_25) | k1_tarski(A_24)!=k1_relat_1(B_25) | ~v1_funct_1(B_25) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_89])).
% 9.92/3.67  tff(c_414, plain, (![A_118, B_119, C_120, D_121]: (k7_relset_1(A_118, B_119, C_120, D_121)=k9_relat_1(C_120, D_121) | ~m1_subset_1(C_120, k1_zfmisc_1(k2_zfmisc_1(A_118, B_119))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 9.92/3.67  tff(c_423, plain, (![D_121]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_121)=k9_relat_1('#skF_4', D_121))), inference(resolution, [status(thm)], [c_62, c_414])).
% 9.92/3.67  tff(c_58, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_128])).
% 9.92/3.67  tff(c_460, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_423, c_58])).
% 9.92/3.67  tff(c_615, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_44, c_460])).
% 9.92/3.67  tff(c_617, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_177, c_66, c_615])).
% 9.92/3.67  tff(c_1011, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_617])).
% 9.92/3.67  tff(c_250, plain, (![C_88, A_89, B_90]: (v4_relat_1(C_88, A_89) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 9.92/3.67  tff(c_262, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_62, c_250])).
% 9.92/3.67  tff(c_12, plain, (![A_4]: (k2_tarski(A_4, A_4)=k1_tarski(A_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.92/3.67  tff(c_835, plain, (![B_159, C_160, A_161]: (k2_tarski(B_159, C_160)=A_161 | k1_tarski(C_160)=A_161 | k1_tarski(B_159)=A_161 | k1_xboole_0=A_161 | ~r1_tarski(A_161, k2_tarski(B_159, C_160)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 9.92/3.67  tff(c_852, plain, (![A_4, A_161]: (k2_tarski(A_4, A_4)=A_161 | k1_tarski(A_4)=A_161 | k1_tarski(A_4)=A_161 | k1_xboole_0=A_161 | ~r1_tarski(A_161, k1_tarski(A_4)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_835])).
% 9.92/3.67  tff(c_4639, plain, (![A_396, A_397]: (k1_tarski(A_396)=A_397 | k1_tarski(A_396)=A_397 | k1_tarski(A_396)=A_397 | k1_xboole_0=A_397 | ~r1_tarski(A_397, k1_tarski(A_396)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_852])).
% 9.92/3.67  tff(c_6759, plain, (![A_498, B_499]: (k1_tarski(A_498)=k1_relat_1(B_499) | k1_relat_1(B_499)=k1_xboole_0 | ~v4_relat_1(B_499, k1_tarski(A_498)) | ~v1_relat_1(B_499))), inference(resolution, [status(thm)], [c_38, c_4639])).
% 9.92/3.67  tff(c_6793, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_262, c_6759])).
% 9.92/3.67  tff(c_6817, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_177, c_6793])).
% 9.92/3.67  tff(c_6818, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_1011, c_6817])).
% 9.92/3.67  tff(c_476, plain, (![B_132]: (k2_zfmisc_1(k1_xboole_0, B_132)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_470])).
% 9.92/3.67  tff(c_787, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k1_relat_1('#skF_4'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_476, c_758])).
% 9.92/3.67  tff(c_890, plain, (~r1_tarski(k1_relat_1('#skF_4'), k1_xboole_0)), inference(splitLeft, [status(thm)], [c_787])).
% 9.92/3.67  tff(c_6839, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6818, c_890])).
% 9.92/3.67  tff(c_6861, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_116, c_6839])).
% 9.92/3.67  tff(c_6862, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_617])).
% 9.92/3.67  tff(c_6923, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_6862])).
% 9.92/3.67  tff(c_6927, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_177, c_6923])).
% 9.92/3.67  tff(c_6928, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_787])).
% 9.92/3.67  tff(c_50, plain, (![C_31, A_29, B_30]: (v4_relat_1(C_31, A_29) | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 9.92/3.67  tff(c_503, plain, (![C_31]: (v4_relat_1(C_31, k1_xboole_0) | ~m1_subset_1(C_31, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_481, c_50])).
% 9.92/3.67  tff(c_6934, plain, (v4_relat_1('#skF_4', k1_xboole_0)), inference(resolution, [status(thm)], [c_6928, c_503])).
% 9.92/3.67  tff(c_6950, plain, $false, inference(negUnitSimplification, [status(thm)], [c_830, c_6934])).
% 9.92/3.67  tff(c_6951, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_790])).
% 9.92/3.67  tff(c_6958, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_6951, c_4])).
% 9.92/3.67  tff(c_6981, plain, (![A_13]: (r1_tarski('#skF_4', A_13))), inference(demodulation, [status(thm), theory('equality')], [c_6958, c_116])).
% 9.92/3.67  tff(c_42, plain, (![A_23]: (k9_relat_1(k1_xboole_0, A_23)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_81])).
% 9.92/3.67  tff(c_6982, plain, (![A_23]: (k9_relat_1('#skF_4', A_23)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6958, c_6958, c_42])).
% 9.92/3.67  tff(c_7085, plain, (~r1_tarski('#skF_4', k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_6982, c_460])).
% 9.92/3.67  tff(c_7089, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6981, c_7085])).
% 9.92/3.67  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.92/3.67  
% 9.92/3.67  Inference rules
% 9.92/3.67  ----------------------
% 9.92/3.67  #Ref     : 0
% 9.92/3.67  #Sup     : 1489
% 9.92/3.67  #Fact    : 0
% 9.92/3.67  #Define  : 0
% 9.92/3.67  #Split   : 23
% 9.92/3.67  #Chain   : 0
% 9.92/3.67  #Close   : 0
% 9.92/3.67  
% 9.92/3.67  Ordering : KBO
% 9.92/3.67  
% 9.92/3.67  Simplification rules
% 9.92/3.67  ----------------------
% 9.92/3.67  #Subsume      : 570
% 9.92/3.67  #Demod        : 2021
% 9.92/3.67  #Tautology    : 770
% 9.92/3.67  #SimpNegUnit  : 114
% 9.92/3.67  #BackRed      : 135
% 9.92/3.67  
% 9.92/3.67  #Partial instantiations: 0
% 9.92/3.67  #Strategies tried      : 1
% 9.92/3.67  
% 9.92/3.67  Timing (in seconds)
% 9.92/3.67  ----------------------
% 9.92/3.68  Preprocessing        : 0.56
% 9.92/3.68  Parsing              : 0.29
% 9.92/3.68  CNF conversion       : 0.04
% 9.92/3.68  Main loop            : 2.21
% 9.92/3.68  Inferencing          : 0.71
% 9.92/3.68  Reduction            : 0.83
% 9.92/3.68  Demodulation         : 0.60
% 9.92/3.68  BG Simplification    : 0.07
% 9.92/3.68  Subsumption          : 0.45
% 9.92/3.68  Abstraction          : 0.09
% 9.92/3.68  MUC search           : 0.00
% 10.31/3.68  Cooper               : 0.00
% 10.31/3.68  Total                : 2.83
% 10.31/3.68  Index Insertion      : 0.00
% 10.31/3.68  Index Deletion       : 0.00
% 10.31/3.68  Index Matching       : 0.00
% 10.31/3.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
