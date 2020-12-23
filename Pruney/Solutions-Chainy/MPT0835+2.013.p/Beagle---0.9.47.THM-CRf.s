%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:57 EST 2020

% Result     : Theorem 3.53s
% Output     : CNFRefutation 3.69s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 158 expanded)
%              Number of leaves         :   40 (  69 expanded)
%              Depth                    :    9
%              Number of atoms          :  132 ( 248 expanded)
%              Number of equality atoms :   61 ( 108 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_105,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( k7_relset_1(B,A,C,k8_relset_1(B,A,C,A)) = k2_relset_1(B,A,C)
          & k8_relset_1(B,A,C,k7_relset_1(B,A,C,B)) = k1_relset_1(B,A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_relset_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_33,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_54,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_82,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_86,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_92,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => ( r1_tarski(k1_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

tff(c_44,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_73,plain,(
    ! [C_47,A_48,B_49] :
      ( v1_relat_1(C_47)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_77,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_73])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_585,plain,(
    ! [B_113,A_114] :
      ( k5_relat_1(B_113,k6_relat_1(A_114)) = B_113
      | ~ r1_tarski(k2_relat_1(B_113),A_114)
      | ~ v1_relat_1(B_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_598,plain,(
    ! [B_113] :
      ( k5_relat_1(B_113,k6_relat_1(k2_relat_1(B_113))) = B_113
      | ~ v1_relat_1(B_113) ) ),
    inference(resolution,[status(thm)],[c_6,c_585])).

tff(c_8,plain,(
    ! [A_3] : v1_relat_1(k6_relat_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_16,plain,(
    ! [A_11] : k1_relat_1(k6_relat_1(A_11)) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_685,plain,(
    ! [A_125,B_126] :
      ( k10_relat_1(A_125,k1_relat_1(B_126)) = k1_relat_1(k5_relat_1(A_125,B_126))
      | ~ v1_relat_1(B_126)
      | ~ v1_relat_1(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_694,plain,(
    ! [A_125,A_11] :
      ( k1_relat_1(k5_relat_1(A_125,k6_relat_1(A_11))) = k10_relat_1(A_125,A_11)
      | ~ v1_relat_1(k6_relat_1(A_11))
      | ~ v1_relat_1(A_125) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_685])).

tff(c_699,plain,(
    ! [A_127,A_128] :
      ( k1_relat_1(k5_relat_1(A_127,k6_relat_1(A_128))) = k10_relat_1(A_127,A_128)
      | ~ v1_relat_1(A_127) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_694])).

tff(c_717,plain,(
    ! [B_113] :
      ( k10_relat_1(B_113,k2_relat_1(B_113)) = k1_relat_1(B_113)
      | ~ v1_relat_1(B_113)
      | ~ v1_relat_1(B_113) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_598,c_699])).

tff(c_552,plain,(
    ! [C_108,A_109,B_110] :
      ( v4_relat_1(C_108,A_109)
      | ~ m1_subset_1(C_108,k1_zfmisc_1(k2_zfmisc_1(A_109,B_110))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_556,plain,(
    v4_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_552])).

tff(c_14,plain,(
    ! [B_10,A_9] :
      ( k7_relat_1(B_10,A_9) = B_10
      | ~ v4_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_568,plain,
    ( k7_relat_1('#skF_3','#skF_2') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_556,c_14])).

tff(c_571,plain,(
    k7_relat_1('#skF_3','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_568])).

tff(c_10,plain,(
    ! [B_5,A_4] :
      ( k2_relat_1(k7_relat_1(B_5,A_4)) = k9_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_575,plain,
    ( k9_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_571,c_10])).

tff(c_579,plain,(
    k9_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_575])).

tff(c_827,plain,(
    ! [A_138,B_139,C_140,D_141] :
      ( k7_relset_1(A_138,B_139,C_140,D_141) = k9_relat_1(C_140,D_141)
      | ~ m1_subset_1(C_140,k1_zfmisc_1(k2_zfmisc_1(A_138,B_139))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_830,plain,(
    ! [D_141] : k7_relset_1('#skF_2','#skF_1','#skF_3',D_141) = k9_relat_1('#skF_3',D_141) ),
    inference(resolution,[status(thm)],[c_44,c_827])).

tff(c_808,plain,(
    ! [A_133,B_134,C_135,D_136] :
      ( k8_relset_1(A_133,B_134,C_135,D_136) = k10_relat_1(C_135,D_136)
      | ~ m1_subset_1(C_135,k1_zfmisc_1(k2_zfmisc_1(A_133,B_134))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_811,plain,(
    ! [D_136] : k8_relset_1('#skF_2','#skF_1','#skF_3',D_136) = k10_relat_1('#skF_3',D_136) ),
    inference(resolution,[status(thm)],[c_44,c_808])).

tff(c_661,plain,(
    ! [A_119,B_120,C_121] :
      ( k1_relset_1(A_119,B_120,C_121) = k1_relat_1(C_121)
      | ~ m1_subset_1(C_121,k1_zfmisc_1(k2_zfmisc_1(A_119,B_120))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_665,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_661])).

tff(c_436,plain,(
    ! [A_83,B_84,C_85,D_86] :
      ( k8_relset_1(A_83,B_84,C_85,D_86) = k10_relat_1(C_85,D_86)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_439,plain,(
    ! [D_86] : k8_relset_1('#skF_2','#skF_1','#skF_3',D_86) = k10_relat_1('#skF_3',D_86) ),
    inference(resolution,[status(thm)],[c_44,c_436])).

tff(c_254,plain,(
    ! [A_71,B_72,C_73] :
      ( k1_relset_1(A_71,B_72,C_73) = k1_relat_1(C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_258,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_254])).

tff(c_464,plain,(
    ! [A_93,B_94,C_95] :
      ( k8_relset_1(A_93,B_94,C_95,B_94) = k1_relset_1(A_93,B_94,C_95)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_93,B_94))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_466,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1') = k1_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_464])).

tff(c_468,plain,(
    k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_439,c_258,c_466])).

tff(c_450,plain,(
    ! [A_88,B_89,C_90,D_91] :
      ( k7_relset_1(A_88,B_89,C_90,D_91) = k9_relat_1(C_90,D_91)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_453,plain,(
    ! [D_91] : k7_relset_1('#skF_2','#skF_1','#skF_3',D_91) = k9_relat_1('#skF_3',D_91) ),
    inference(resolution,[status(thm)],[c_44,c_450])).

tff(c_326,plain,(
    ! [A_77,B_78,C_79] :
      ( k2_relset_1(A_77,B_78,C_79) = k2_relat_1(C_79)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_330,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_326])).

tff(c_42,plain,
    ( k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relset_1('#skF_2','#skF_1','#skF_3')
    | k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_83,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_331,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_330,c_83])).

tff(c_440,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k10_relat_1('#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_439,c_331])).

tff(c_454,plain,(
    k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_453,c_440])).

tff(c_469,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_468,c_454])).

tff(c_479,plain,(
    ! [D_99,B_100,C_101,A_102] :
      ( m1_subset_1(D_99,k1_zfmisc_1(k2_zfmisc_1(B_100,C_101)))
      | ~ r1_tarski(k1_relat_1(D_99),B_100)
      | ~ m1_subset_1(D_99,k1_zfmisc_1(k2_zfmisc_1(A_102,C_101))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_483,plain,(
    ! [B_103] :
      ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(B_103,'#skF_1')))
      | ~ r1_tarski(k1_relat_1('#skF_3'),B_103) ) ),
    inference(resolution,[status(thm)],[c_44,c_479])).

tff(c_26,plain,(
    ! [C_19,A_17,B_18] :
      ( v4_relat_1(C_19,A_17)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(A_17,B_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_521,plain,(
    ! [B_104] :
      ( v4_relat_1('#skF_3',B_104)
      | ~ r1_tarski(k1_relat_1('#skF_3'),B_104) ) ),
    inference(resolution,[status(thm)],[c_483,c_26])).

tff(c_526,plain,(
    v4_relat_1('#skF_3',k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_6,c_521])).

tff(c_535,plain,
    ( k7_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_526,c_14])).

tff(c_538,plain,(
    k7_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_535])).

tff(c_542,plain,
    ( k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_538,c_10])).

tff(c_546,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_542])).

tff(c_548,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_469,c_546])).

tff(c_549,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_671,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_665,c_549])).

tff(c_813,plain,(
    k10_relat_1('#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_811,c_671])).

tff(c_831,plain,(
    k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_830,c_813])).

tff(c_832,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_579,c_831])).

tff(c_850,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_717,c_832])).

tff(c_854,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_850])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:44:14 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.53/1.95  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.53/1.96  
% 3.53/1.96  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.53/1.96  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.53/1.96  
% 3.53/1.96  %Foreground sorts:
% 3.53/1.96  
% 3.53/1.96  
% 3.53/1.96  %Background operators:
% 3.53/1.96  
% 3.53/1.96  
% 3.53/1.96  %Foreground operators:
% 3.53/1.96  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.53/1.96  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.53/1.96  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.53/1.96  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.53/1.96  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.53/1.96  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.53/1.96  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.53/1.96  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.53/1.96  tff('#skF_2', type, '#skF_2': $i).
% 3.53/1.96  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.53/1.96  tff('#skF_3', type, '#skF_3': $i).
% 3.53/1.96  tff('#skF_1', type, '#skF_1': $i).
% 3.53/1.96  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.53/1.96  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.53/1.96  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.53/1.96  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.53/1.96  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.53/1.96  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.53/1.96  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.53/1.96  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.53/1.96  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.53/1.96  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.53/1.96  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.53/1.96  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.53/1.96  
% 3.69/1.99  tff(f_105, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((k7_relset_1(B, A, C, k8_relset_1(B, A, C, A)) = k2_relset_1(B, A, C)) & (k8_relset_1(B, A, C, k7_relset_1(B, A, C, B)) = k1_relset_1(B, A, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_relset_1)).
% 3.69/1.99  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.69/1.99  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.69/1.99  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 3.69/1.99  tff(f_33, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 3.69/1.99  tff(f_54, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 3.69/1.99  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 3.69/1.99  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.69/1.99  tff(f_50, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 3.69/1.99  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 3.69/1.99  tff(f_82, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.69/1.99  tff(f_86, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.69/1.99  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.69/1.99  tff(f_98, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 3.69/1.99  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.69/1.99  tff(f_92, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (r1_tarski(k1_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_relset_1)).
% 3.69/1.99  tff(c_44, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.69/1.99  tff(c_73, plain, (![C_47, A_48, B_49]: (v1_relat_1(C_47) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.69/1.99  tff(c_77, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_73])).
% 3.69/1.99  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.69/1.99  tff(c_585, plain, (![B_113, A_114]: (k5_relat_1(B_113, k6_relat_1(A_114))=B_113 | ~r1_tarski(k2_relat_1(B_113), A_114) | ~v1_relat_1(B_113))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.69/1.99  tff(c_598, plain, (![B_113]: (k5_relat_1(B_113, k6_relat_1(k2_relat_1(B_113)))=B_113 | ~v1_relat_1(B_113))), inference(resolution, [status(thm)], [c_6, c_585])).
% 3.69/1.99  tff(c_8, plain, (![A_3]: (v1_relat_1(k6_relat_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.69/1.99  tff(c_16, plain, (![A_11]: (k1_relat_1(k6_relat_1(A_11))=A_11)), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.69/1.99  tff(c_685, plain, (![A_125, B_126]: (k10_relat_1(A_125, k1_relat_1(B_126))=k1_relat_1(k5_relat_1(A_125, B_126)) | ~v1_relat_1(B_126) | ~v1_relat_1(A_125))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.69/1.99  tff(c_694, plain, (![A_125, A_11]: (k1_relat_1(k5_relat_1(A_125, k6_relat_1(A_11)))=k10_relat_1(A_125, A_11) | ~v1_relat_1(k6_relat_1(A_11)) | ~v1_relat_1(A_125))), inference(superposition, [status(thm), theory('equality')], [c_16, c_685])).
% 3.69/1.99  tff(c_699, plain, (![A_127, A_128]: (k1_relat_1(k5_relat_1(A_127, k6_relat_1(A_128)))=k10_relat_1(A_127, A_128) | ~v1_relat_1(A_127))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_694])).
% 3.69/1.99  tff(c_717, plain, (![B_113]: (k10_relat_1(B_113, k2_relat_1(B_113))=k1_relat_1(B_113) | ~v1_relat_1(B_113) | ~v1_relat_1(B_113))), inference(superposition, [status(thm), theory('equality')], [c_598, c_699])).
% 3.69/1.99  tff(c_552, plain, (![C_108, A_109, B_110]: (v4_relat_1(C_108, A_109) | ~m1_subset_1(C_108, k1_zfmisc_1(k2_zfmisc_1(A_109, B_110))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.69/1.99  tff(c_556, plain, (v4_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_44, c_552])).
% 3.69/1.99  tff(c_14, plain, (![B_10, A_9]: (k7_relat_1(B_10, A_9)=B_10 | ~v4_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.69/1.99  tff(c_568, plain, (k7_relat_1('#skF_3', '#skF_2')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_556, c_14])).
% 3.69/1.99  tff(c_571, plain, (k7_relat_1('#skF_3', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_77, c_568])).
% 3.69/1.99  tff(c_10, plain, (![B_5, A_4]: (k2_relat_1(k7_relat_1(B_5, A_4))=k9_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.69/1.99  tff(c_575, plain, (k9_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_571, c_10])).
% 3.69/1.99  tff(c_579, plain, (k9_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_77, c_575])).
% 3.69/1.99  tff(c_827, plain, (![A_138, B_139, C_140, D_141]: (k7_relset_1(A_138, B_139, C_140, D_141)=k9_relat_1(C_140, D_141) | ~m1_subset_1(C_140, k1_zfmisc_1(k2_zfmisc_1(A_138, B_139))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.69/1.99  tff(c_830, plain, (![D_141]: (k7_relset_1('#skF_2', '#skF_1', '#skF_3', D_141)=k9_relat_1('#skF_3', D_141))), inference(resolution, [status(thm)], [c_44, c_827])).
% 3.69/1.99  tff(c_808, plain, (![A_133, B_134, C_135, D_136]: (k8_relset_1(A_133, B_134, C_135, D_136)=k10_relat_1(C_135, D_136) | ~m1_subset_1(C_135, k1_zfmisc_1(k2_zfmisc_1(A_133, B_134))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.69/1.99  tff(c_811, plain, (![D_136]: (k8_relset_1('#skF_2', '#skF_1', '#skF_3', D_136)=k10_relat_1('#skF_3', D_136))), inference(resolution, [status(thm)], [c_44, c_808])).
% 3.69/1.99  tff(c_661, plain, (![A_119, B_120, C_121]: (k1_relset_1(A_119, B_120, C_121)=k1_relat_1(C_121) | ~m1_subset_1(C_121, k1_zfmisc_1(k2_zfmisc_1(A_119, B_120))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.69/1.99  tff(c_665, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_661])).
% 3.69/1.99  tff(c_436, plain, (![A_83, B_84, C_85, D_86]: (k8_relset_1(A_83, B_84, C_85, D_86)=k10_relat_1(C_85, D_86) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.69/1.99  tff(c_439, plain, (![D_86]: (k8_relset_1('#skF_2', '#skF_1', '#skF_3', D_86)=k10_relat_1('#skF_3', D_86))), inference(resolution, [status(thm)], [c_44, c_436])).
% 3.69/1.99  tff(c_254, plain, (![A_71, B_72, C_73]: (k1_relset_1(A_71, B_72, C_73)=k1_relat_1(C_73) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.69/1.99  tff(c_258, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_254])).
% 3.69/1.99  tff(c_464, plain, (![A_93, B_94, C_95]: (k8_relset_1(A_93, B_94, C_95, B_94)=k1_relset_1(A_93, B_94, C_95) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.69/1.99  tff(c_466, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1')=k1_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_44, c_464])).
% 3.69/1.99  tff(c_468, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_439, c_258, c_466])).
% 3.69/1.99  tff(c_450, plain, (![A_88, B_89, C_90, D_91]: (k7_relset_1(A_88, B_89, C_90, D_91)=k9_relat_1(C_90, D_91) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.69/1.99  tff(c_453, plain, (![D_91]: (k7_relset_1('#skF_2', '#skF_1', '#skF_3', D_91)=k9_relat_1('#skF_3', D_91))), inference(resolution, [status(thm)], [c_44, c_450])).
% 3.69/1.99  tff(c_326, plain, (![A_77, B_78, C_79]: (k2_relset_1(A_77, B_78, C_79)=k2_relat_1(C_79) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.69/1.99  tff(c_330, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_326])).
% 3.69/1.99  tff(c_42, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relset_1('#skF_2', '#skF_1', '#skF_3') | k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.69/1.99  tff(c_83, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_42])).
% 3.69/1.99  tff(c_331, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_330, c_83])).
% 3.69/1.99  tff(c_440, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k10_relat_1('#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_439, c_331])).
% 3.69/1.99  tff(c_454, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_453, c_440])).
% 3.69/1.99  tff(c_469, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_468, c_454])).
% 3.69/1.99  tff(c_479, plain, (![D_99, B_100, C_101, A_102]: (m1_subset_1(D_99, k1_zfmisc_1(k2_zfmisc_1(B_100, C_101))) | ~r1_tarski(k1_relat_1(D_99), B_100) | ~m1_subset_1(D_99, k1_zfmisc_1(k2_zfmisc_1(A_102, C_101))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.69/1.99  tff(c_483, plain, (![B_103]: (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(B_103, '#skF_1'))) | ~r1_tarski(k1_relat_1('#skF_3'), B_103))), inference(resolution, [status(thm)], [c_44, c_479])).
% 3.69/1.99  tff(c_26, plain, (![C_19, A_17, B_18]: (v4_relat_1(C_19, A_17) | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(A_17, B_18))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.69/1.99  tff(c_521, plain, (![B_104]: (v4_relat_1('#skF_3', B_104) | ~r1_tarski(k1_relat_1('#skF_3'), B_104))), inference(resolution, [status(thm)], [c_483, c_26])).
% 3.69/1.99  tff(c_526, plain, (v4_relat_1('#skF_3', k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_6, c_521])).
% 3.69/1.99  tff(c_535, plain, (k7_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_526, c_14])).
% 3.69/1.99  tff(c_538, plain, (k7_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_77, c_535])).
% 3.69/1.99  tff(c_542, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_538, c_10])).
% 3.69/1.99  tff(c_546, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_77, c_542])).
% 3.69/1.99  tff(c_548, plain, $false, inference(negUnitSimplification, [status(thm)], [c_469, c_546])).
% 3.69/1.99  tff(c_549, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_42])).
% 3.69/1.99  tff(c_671, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_665, c_549])).
% 3.69/1.99  tff(c_813, plain, (k10_relat_1('#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_811, c_671])).
% 3.69/1.99  tff(c_831, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_830, c_813])).
% 3.69/1.99  tff(c_832, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_579, c_831])).
% 3.69/1.99  tff(c_850, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_717, c_832])).
% 3.69/1.99  tff(c_854, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_77, c_850])).
% 3.69/1.99  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.69/1.99  
% 3.69/1.99  Inference rules
% 3.69/1.99  ----------------------
% 3.69/1.99  #Ref     : 0
% 3.69/1.99  #Sup     : 178
% 3.69/1.99  #Fact    : 0
% 3.69/1.99  #Define  : 0
% 3.69/1.99  #Split   : 1
% 3.69/1.99  #Chain   : 0
% 3.69/1.99  #Close   : 0
% 3.69/1.99  
% 3.69/1.99  Ordering : KBO
% 3.69/1.99  
% 3.69/1.99  Simplification rules
% 3.69/1.99  ----------------------
% 3.69/1.99  #Subsume      : 5
% 3.69/1.99  #Demod        : 135
% 3.69/1.99  #Tautology    : 107
% 3.69/1.99  #SimpNegUnit  : 1
% 3.69/1.99  #BackRed      : 8
% 3.69/1.99  
% 3.69/1.99  #Partial instantiations: 0
% 3.69/1.99  #Strategies tried      : 1
% 3.69/1.99  
% 3.69/1.99  Timing (in seconds)
% 3.69/1.99  ----------------------
% 3.69/2.00  Preprocessing        : 0.52
% 3.69/2.00  Parsing              : 0.27
% 3.69/2.00  CNF conversion       : 0.04
% 3.69/2.00  Main loop            : 0.54
% 3.69/2.00  Inferencing          : 0.21
% 3.69/2.00  Reduction            : 0.17
% 3.69/2.00  Demodulation         : 0.13
% 3.69/2.00  BG Simplification    : 0.03
% 3.69/2.00  Subsumption          : 0.08
% 3.69/2.00  Abstraction          : 0.03
% 3.69/2.00  MUC search           : 0.00
% 3.69/2.00  Cooper               : 0.00
% 3.69/2.00  Total                : 1.12
% 3.69/2.00  Index Insertion      : 0.00
% 3.69/2.00  Index Deletion       : 0.00
% 3.69/2.00  Index Matching       : 0.00
% 3.69/2.00  BG Taut test         : 0.00
%------------------------------------------------------------------------------
