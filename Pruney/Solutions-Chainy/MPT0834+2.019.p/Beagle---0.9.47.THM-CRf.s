%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:52 EST 2020

% Result     : Theorem 2.98s
% Output     : CNFRefutation 3.09s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 136 expanded)
%              Number of leaves         :   47 (  65 expanded)
%              Depth                    :   10
%              Number of atoms          :  126 ( 200 expanded)
%              Number of equality atoms :   49 (  78 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_111,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
          & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_35,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_43,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_74,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_104,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_100,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(c_52,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_79,plain,(
    ! [C_53,A_54,B_55] :
      ( v1_relat_1(C_53)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_83,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_79])).

tff(c_493,plain,(
    ! [A_132,B_133,C_134] :
      ( k2_relset_1(A_132,B_133,C_134) = k2_relat_1(C_134)
      | ~ m1_subset_1(C_134,k1_zfmisc_1(k2_zfmisc_1(A_132,B_133))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_497,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_493])).

tff(c_657,plain,(
    ! [A_156,B_157,C_158] :
      ( m1_subset_1(k2_relset_1(A_156,B_157,C_158),k1_zfmisc_1(B_157))
      | ~ m1_subset_1(C_158,k1_zfmisc_1(k2_zfmisc_1(A_156,B_157))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_683,plain,
    ( m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1('#skF_4'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_497,c_657])).

tff(c_691,plain,(
    m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_683])).

tff(c_14,plain,(
    ! [A_6] : ~ v1_xboole_0(k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_414,plain,(
    ! [A_112,B_113] :
      ( r2_hidden(A_112,B_113)
      | v1_xboole_0(B_113)
      | ~ m1_subset_1(A_112,B_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( r1_tarski(C_5,A_1)
      | ~ r2_hidden(C_5,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_418,plain,(
    ! [A_112,A_1] :
      ( r1_tarski(A_112,A_1)
      | v1_xboole_0(k1_zfmisc_1(A_1))
      | ~ m1_subset_1(A_112,k1_zfmisc_1(A_1)) ) ),
    inference(resolution,[status(thm)],[c_414,c_2])).

tff(c_421,plain,(
    ! [A_112,A_1] :
      ( r1_tarski(A_112,A_1)
      | ~ m1_subset_1(A_112,k1_zfmisc_1(A_1)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_418])).

tff(c_695,plain,(
    r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_691,c_421])).

tff(c_22,plain,(
    ! [A_12,B_13] :
      ( k8_relat_1(A_12,B_13) = B_13
      | ~ r1_tarski(k2_relat_1(B_13),A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_698,plain,
    ( k8_relat_1('#skF_4','#skF_5') = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_695,c_22])).

tff(c_701,plain,(
    k8_relat_1('#skF_4','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_698])).

tff(c_20,plain,(
    ! [B_11,A_10] :
      ( k5_relat_1(B_11,k6_relat_1(A_10)) = k8_relat_1(A_10,B_11)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_18,plain,(
    ! [A_9] : v1_relat_1(k6_relat_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_30,plain,(
    ! [A_21] : k1_relat_1(k6_relat_1(A_21)) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_517,plain,(
    ! [A_138,B_139] :
      ( k10_relat_1(A_138,k1_relat_1(B_139)) = k1_relat_1(k5_relat_1(A_138,B_139))
      | ~ v1_relat_1(B_139)
      | ~ v1_relat_1(A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_526,plain,(
    ! [A_138,A_21] :
      ( k1_relat_1(k5_relat_1(A_138,k6_relat_1(A_21))) = k10_relat_1(A_138,A_21)
      | ~ v1_relat_1(k6_relat_1(A_21))
      | ~ v1_relat_1(A_138) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_517])).

tff(c_531,plain,(
    ! [A_140,A_141] :
      ( k1_relat_1(k5_relat_1(A_140,k6_relat_1(A_141))) = k10_relat_1(A_140,A_141)
      | ~ v1_relat_1(A_140) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_526])).

tff(c_543,plain,(
    ! [A_10,B_11] :
      ( k1_relat_1(k8_relat_1(A_10,B_11)) = k10_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11)
      | ~ v1_relat_1(B_11) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_531])).

tff(c_705,plain,
    ( k10_relat_1('#skF_5','#skF_4') = k1_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_701,c_543])).

tff(c_709,plain,(
    k10_relat_1('#skF_5','#skF_4') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_83,c_705])).

tff(c_730,plain,(
    ! [A_164,B_165,C_166,D_167] :
      ( k8_relset_1(A_164,B_165,C_166,D_167) = k10_relat_1(C_166,D_167)
      | ~ m1_subset_1(C_166,k1_zfmisc_1(k2_zfmisc_1(A_164,B_165))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_737,plain,(
    ! [D_167] : k8_relset_1('#skF_3','#skF_4','#skF_5',D_167) = k10_relat_1('#skF_5',D_167) ),
    inference(resolution,[status(thm)],[c_52,c_730])).

tff(c_507,plain,(
    ! [A_135,B_136,C_137] :
      ( k1_relset_1(A_135,B_136,C_137) = k1_relat_1(C_137)
      | ~ m1_subset_1(C_137,k1_zfmisc_1(k2_zfmisc_1(A_135,B_136))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_511,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_507])).

tff(c_112,plain,(
    ! [C_65,A_66,B_67] :
      ( v4_relat_1(C_65,A_66)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_116,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_112])).

tff(c_126,plain,(
    ! [B_70,A_71] :
      ( k7_relat_1(B_70,A_71) = B_70
      | ~ v4_relat_1(B_70,A_71)
      | ~ v1_relat_1(B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_129,plain,
    ( k7_relat_1('#skF_5','#skF_3') = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_116,c_126])).

tff(c_132,plain,(
    k7_relat_1('#skF_5','#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_129])).

tff(c_24,plain,(
    ! [B_15,A_14] :
      ( k2_relat_1(k7_relat_1(B_15,A_14)) = k9_relat_1(B_15,A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_136,plain,
    ( k9_relat_1('#skF_5','#skF_3') = k2_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_24])).

tff(c_140,plain,(
    k9_relat_1('#skF_5','#skF_3') = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_136])).

tff(c_396,plain,(
    ! [A_108,B_109,C_110,D_111] :
      ( k7_relset_1(A_108,B_109,C_110,D_111) = k9_relat_1(C_110,D_111)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(A_108,B_109))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_403,plain,(
    ! [D_111] : k7_relset_1('#skF_3','#skF_4','#skF_5',D_111) = k9_relat_1('#skF_5',D_111) ),
    inference(resolution,[status(thm)],[c_52,c_396])).

tff(c_231,plain,(
    ! [A_84,B_85,C_86] :
      ( k2_relset_1(A_84,B_85,C_86) = k2_relat_1(C_86)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_235,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_231])).

tff(c_50,plain,
    ( k8_relset_1('#skF_3','#skF_4','#skF_5','#skF_4') != k1_relset_1('#skF_3','#skF_4','#skF_5')
    | k7_relset_1('#skF_3','#skF_4','#skF_5','#skF_3') != k2_relset_1('#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_84,plain,(
    k7_relset_1('#skF_3','#skF_4','#skF_5','#skF_3') != k2_relset_1('#skF_3','#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_236,plain,(
    k7_relset_1('#skF_3','#skF_4','#skF_5','#skF_3') != k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_235,c_84])).

tff(c_404,plain,(
    k9_relat_1('#skF_5','#skF_3') != k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_403,c_236])).

tff(c_407,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_404])).

tff(c_408,plain,(
    k8_relset_1('#skF_3','#skF_4','#skF_5','#skF_4') != k1_relset_1('#skF_3','#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_512,plain,(
    k8_relset_1('#skF_3','#skF_4','#skF_5','#skF_4') != k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_511,c_408])).

tff(c_738,plain,(
    k10_relat_1('#skF_5','#skF_4') != k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_737,c_512])).

tff(c_741,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_709,c_738])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 21:06:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.98/1.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.98/1.49  
% 2.98/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.98/1.50  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.98/1.50  
% 2.98/1.50  %Foreground sorts:
% 2.98/1.50  
% 2.98/1.50  
% 2.98/1.50  %Background operators:
% 2.98/1.50  
% 2.98/1.50  
% 2.98/1.50  %Foreground operators:
% 2.98/1.50  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.98/1.50  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.98/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.98/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.98/1.50  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.98/1.50  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.98/1.50  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.98/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.98/1.50  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.98/1.50  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.98/1.50  tff('#skF_5', type, '#skF_5': $i).
% 2.98/1.50  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.98/1.50  tff('#skF_3', type, '#skF_3': $i).
% 2.98/1.50  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.98/1.50  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.98/1.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.98/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.98/1.50  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.98/1.50  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.98/1.50  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.98/1.50  tff('#skF_4', type, '#skF_4': $i).
% 2.98/1.50  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.98/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.98/1.50  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.98/1.50  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.98/1.50  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.98/1.50  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.98/1.50  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.98/1.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.98/1.50  
% 3.09/1.51  tff(f_111, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 3.09/1.51  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.09/1.51  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.09/1.51  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 3.09/1.51  tff(f_35, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 3.09/1.51  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.09/1.51  tff(f_32, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.09/1.51  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_relat_1)).
% 3.09/1.51  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_relat_1)).
% 3.09/1.51  tff(f_43, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 3.09/1.51  tff(f_74, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 3.09/1.51  tff(f_64, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 3.09/1.51  tff(f_104, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.09/1.51  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.09/1.51  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.09/1.51  tff(f_70, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 3.09/1.51  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 3.09/1.51  tff(f_100, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.09/1.51  tff(c_52, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.09/1.51  tff(c_79, plain, (![C_53, A_54, B_55]: (v1_relat_1(C_53) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.09/1.51  tff(c_83, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_52, c_79])).
% 3.09/1.51  tff(c_493, plain, (![A_132, B_133, C_134]: (k2_relset_1(A_132, B_133, C_134)=k2_relat_1(C_134) | ~m1_subset_1(C_134, k1_zfmisc_1(k2_zfmisc_1(A_132, B_133))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.09/1.51  tff(c_497, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_52, c_493])).
% 3.09/1.51  tff(c_657, plain, (![A_156, B_157, C_158]: (m1_subset_1(k2_relset_1(A_156, B_157, C_158), k1_zfmisc_1(B_157)) | ~m1_subset_1(C_158, k1_zfmisc_1(k2_zfmisc_1(A_156, B_157))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.09/1.51  tff(c_683, plain, (m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1('#skF_4')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_497, c_657])).
% 3.09/1.51  tff(c_691, plain, (m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_683])).
% 3.09/1.51  tff(c_14, plain, (![A_6]: (~v1_xboole_0(k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.09/1.51  tff(c_414, plain, (![A_112, B_113]: (r2_hidden(A_112, B_113) | v1_xboole_0(B_113) | ~m1_subset_1(A_112, B_113))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.09/1.51  tff(c_2, plain, (![C_5, A_1]: (r1_tarski(C_5, A_1) | ~r2_hidden(C_5, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.09/1.51  tff(c_418, plain, (![A_112, A_1]: (r1_tarski(A_112, A_1) | v1_xboole_0(k1_zfmisc_1(A_1)) | ~m1_subset_1(A_112, k1_zfmisc_1(A_1)))), inference(resolution, [status(thm)], [c_414, c_2])).
% 3.09/1.51  tff(c_421, plain, (![A_112, A_1]: (r1_tarski(A_112, A_1) | ~m1_subset_1(A_112, k1_zfmisc_1(A_1)))), inference(negUnitSimplification, [status(thm)], [c_14, c_418])).
% 3.09/1.51  tff(c_695, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_691, c_421])).
% 3.09/1.51  tff(c_22, plain, (![A_12, B_13]: (k8_relat_1(A_12, B_13)=B_13 | ~r1_tarski(k2_relat_1(B_13), A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.09/1.51  tff(c_698, plain, (k8_relat_1('#skF_4', '#skF_5')='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_695, c_22])).
% 3.09/1.51  tff(c_701, plain, (k8_relat_1('#skF_4', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_83, c_698])).
% 3.09/1.51  tff(c_20, plain, (![B_11, A_10]: (k5_relat_1(B_11, k6_relat_1(A_10))=k8_relat_1(A_10, B_11) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.09/1.51  tff(c_18, plain, (![A_9]: (v1_relat_1(k6_relat_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.09/1.51  tff(c_30, plain, (![A_21]: (k1_relat_1(k6_relat_1(A_21))=A_21)), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.09/1.51  tff(c_517, plain, (![A_138, B_139]: (k10_relat_1(A_138, k1_relat_1(B_139))=k1_relat_1(k5_relat_1(A_138, B_139)) | ~v1_relat_1(B_139) | ~v1_relat_1(A_138))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.09/1.51  tff(c_526, plain, (![A_138, A_21]: (k1_relat_1(k5_relat_1(A_138, k6_relat_1(A_21)))=k10_relat_1(A_138, A_21) | ~v1_relat_1(k6_relat_1(A_21)) | ~v1_relat_1(A_138))), inference(superposition, [status(thm), theory('equality')], [c_30, c_517])).
% 3.09/1.51  tff(c_531, plain, (![A_140, A_141]: (k1_relat_1(k5_relat_1(A_140, k6_relat_1(A_141)))=k10_relat_1(A_140, A_141) | ~v1_relat_1(A_140))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_526])).
% 3.09/1.51  tff(c_543, plain, (![A_10, B_11]: (k1_relat_1(k8_relat_1(A_10, B_11))=k10_relat_1(B_11, A_10) | ~v1_relat_1(B_11) | ~v1_relat_1(B_11))), inference(superposition, [status(thm), theory('equality')], [c_20, c_531])).
% 3.09/1.51  tff(c_705, plain, (k10_relat_1('#skF_5', '#skF_4')=k1_relat_1('#skF_5') | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_701, c_543])).
% 3.09/1.51  tff(c_709, plain, (k10_relat_1('#skF_5', '#skF_4')=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_83, c_83, c_705])).
% 3.09/1.51  tff(c_730, plain, (![A_164, B_165, C_166, D_167]: (k8_relset_1(A_164, B_165, C_166, D_167)=k10_relat_1(C_166, D_167) | ~m1_subset_1(C_166, k1_zfmisc_1(k2_zfmisc_1(A_164, B_165))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.09/1.51  tff(c_737, plain, (![D_167]: (k8_relset_1('#skF_3', '#skF_4', '#skF_5', D_167)=k10_relat_1('#skF_5', D_167))), inference(resolution, [status(thm)], [c_52, c_730])).
% 3.09/1.51  tff(c_507, plain, (![A_135, B_136, C_137]: (k1_relset_1(A_135, B_136, C_137)=k1_relat_1(C_137) | ~m1_subset_1(C_137, k1_zfmisc_1(k2_zfmisc_1(A_135, B_136))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.09/1.51  tff(c_511, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_52, c_507])).
% 3.09/1.51  tff(c_112, plain, (![C_65, A_66, B_67]: (v4_relat_1(C_65, A_66) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.09/1.51  tff(c_116, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_52, c_112])).
% 3.09/1.51  tff(c_126, plain, (![B_70, A_71]: (k7_relat_1(B_70, A_71)=B_70 | ~v4_relat_1(B_70, A_71) | ~v1_relat_1(B_70))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.09/1.51  tff(c_129, plain, (k7_relat_1('#skF_5', '#skF_3')='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_116, c_126])).
% 3.09/1.51  tff(c_132, plain, (k7_relat_1('#skF_5', '#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_83, c_129])).
% 3.09/1.51  tff(c_24, plain, (![B_15, A_14]: (k2_relat_1(k7_relat_1(B_15, A_14))=k9_relat_1(B_15, A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.09/1.51  tff(c_136, plain, (k9_relat_1('#skF_5', '#skF_3')=k2_relat_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_132, c_24])).
% 3.09/1.51  tff(c_140, plain, (k9_relat_1('#skF_5', '#skF_3')=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_83, c_136])).
% 3.09/1.51  tff(c_396, plain, (![A_108, B_109, C_110, D_111]: (k7_relset_1(A_108, B_109, C_110, D_111)=k9_relat_1(C_110, D_111) | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(A_108, B_109))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.09/1.51  tff(c_403, plain, (![D_111]: (k7_relset_1('#skF_3', '#skF_4', '#skF_5', D_111)=k9_relat_1('#skF_5', D_111))), inference(resolution, [status(thm)], [c_52, c_396])).
% 3.09/1.51  tff(c_231, plain, (![A_84, B_85, C_86]: (k2_relset_1(A_84, B_85, C_86)=k2_relat_1(C_86) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.09/1.51  tff(c_235, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_52, c_231])).
% 3.09/1.51  tff(c_50, plain, (k8_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_4')!=k1_relset_1('#skF_3', '#skF_4', '#skF_5') | k7_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_3')!=k2_relset_1('#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.09/1.51  tff(c_84, plain, (k7_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_3')!=k2_relset_1('#skF_3', '#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_50])).
% 3.09/1.51  tff(c_236, plain, (k7_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_3')!=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_235, c_84])).
% 3.09/1.51  tff(c_404, plain, (k9_relat_1('#skF_5', '#skF_3')!=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_403, c_236])).
% 3.09/1.51  tff(c_407, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_140, c_404])).
% 3.09/1.51  tff(c_408, plain, (k8_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_4')!=k1_relset_1('#skF_3', '#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_50])).
% 3.09/1.51  tff(c_512, plain, (k8_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_4')!=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_511, c_408])).
% 3.09/1.51  tff(c_738, plain, (k10_relat_1('#skF_5', '#skF_4')!=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_737, c_512])).
% 3.09/1.51  tff(c_741, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_709, c_738])).
% 3.09/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.09/1.51  
% 3.09/1.51  Inference rules
% 3.09/1.51  ----------------------
% 3.09/1.51  #Ref     : 0
% 3.09/1.51  #Sup     : 156
% 3.09/1.51  #Fact    : 0
% 3.09/1.51  #Define  : 0
% 3.09/1.51  #Split   : 1
% 3.09/1.51  #Chain   : 0
% 3.09/1.51  #Close   : 0
% 3.09/1.51  
% 3.09/1.51  Ordering : KBO
% 3.09/1.51  
% 3.09/1.51  Simplification rules
% 3.09/1.51  ----------------------
% 3.09/1.51  #Subsume      : 10
% 3.09/1.51  #Demod        : 65
% 3.09/1.51  #Tautology    : 73
% 3.09/1.51  #SimpNegUnit  : 2
% 3.09/1.51  #BackRed      : 5
% 3.09/1.51  
% 3.09/1.51  #Partial instantiations: 0
% 3.09/1.51  #Strategies tried      : 1
% 3.09/1.51  
% 3.09/1.51  Timing (in seconds)
% 3.09/1.51  ----------------------
% 3.09/1.52  Preprocessing        : 0.36
% 3.09/1.52  Parsing              : 0.18
% 3.09/1.52  CNF conversion       : 0.02
% 3.09/1.52  Main loop            : 0.37
% 3.09/1.52  Inferencing          : 0.15
% 3.09/1.52  Reduction            : 0.11
% 3.09/1.52  Demodulation         : 0.07
% 3.09/1.52  BG Simplification    : 0.02
% 3.09/1.52  Subsumption          : 0.05
% 3.09/1.52  Abstraction          : 0.03
% 3.09/1.52  MUC search           : 0.00
% 3.09/1.52  Cooper               : 0.00
% 3.09/1.52  Total                : 0.78
% 3.09/1.52  Index Insertion      : 0.00
% 3.09/1.52  Index Deletion       : 0.00
% 3.09/1.52  Index Matching       : 0.00
% 3.09/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
