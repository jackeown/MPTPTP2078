%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:01 EST 2020

% Result     : Theorem 2.84s
% Output     : CNFRefutation 2.97s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 150 expanded)
%              Number of leaves         :   41 (  66 expanded)
%              Depth                    :    9
%              Number of atoms          :  134 ( 235 expanded)
%              Number of equality atoms :   55 (  87 expanded)
%              Maximal formula depth    :    7 (   4 average)
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

tff(f_42,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_106,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( k7_relset_1(B,A,C,k8_relset_1(B,A,C,A)) = k2_relset_1(B,A,C)
          & k8_relset_1(B,A,C,k7_relset_1(B,A,C,B)) = k1_relset_1(B,A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_relset_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_95,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_99,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_40,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_71,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(c_10,plain,(
    ! [A_7,B_8] : v1_relat_1(k2_zfmisc_1(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_42,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_553,plain,(
    ! [B_101,A_102] :
      ( v1_relat_1(B_101)
      | ~ m1_subset_1(B_101,k1_zfmisc_1(A_102))
      | ~ v1_relat_1(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_556,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_42,c_553])).

tff(c_559,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_556])).

tff(c_16,plain,(
    ! [A_12] :
      ( k10_relat_1(A_12,k2_relat_1(A_12)) = k1_relat_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_588,plain,(
    ! [C_114,A_115,B_116] :
      ( v4_relat_1(C_114,A_115)
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1(A_115,B_116))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_592,plain,(
    v4_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_588])).

tff(c_20,plain,(
    ! [B_17,A_16] :
      ( k7_relat_1(B_17,A_16) = B_17
      | ~ v4_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_595,plain,
    ( k7_relat_1('#skF_3','#skF_2') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_592,c_20])).

tff(c_598,plain,(
    k7_relat_1('#skF_3','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_559,c_595])).

tff(c_14,plain,(
    ! [B_11,A_10] :
      ( k2_relat_1(k7_relat_1(B_11,A_10)) = k9_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_606,plain,
    ( k9_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_598,c_14])).

tff(c_610,plain,(
    k9_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_559,c_606])).

tff(c_924,plain,(
    ! [A_148,B_149,C_150,D_151] :
      ( k7_relset_1(A_148,B_149,C_150,D_151) = k9_relat_1(C_150,D_151)
      | ~ m1_subset_1(C_150,k1_zfmisc_1(k2_zfmisc_1(A_148,B_149))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_927,plain,(
    ! [D_151] : k7_relset_1('#skF_2','#skF_1','#skF_3',D_151) = k9_relat_1('#skF_3',D_151) ),
    inference(resolution,[status(thm)],[c_42,c_924])).

tff(c_887,plain,(
    ! [A_141,B_142,C_143,D_144] :
      ( k8_relset_1(A_141,B_142,C_143,D_144) = k10_relat_1(C_143,D_144)
      | ~ m1_subset_1(C_143,k1_zfmisc_1(k2_zfmisc_1(A_141,B_142))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_890,plain,(
    ! [D_144] : k8_relset_1('#skF_2','#skF_1','#skF_3',D_144) = k10_relat_1('#skF_3',D_144) ),
    inference(resolution,[status(thm)],[c_42,c_887])).

tff(c_727,plain,(
    ! [A_131,B_132,C_133] :
      ( k1_relset_1(A_131,B_132,C_133) = k1_relat_1(C_133)
      | ~ m1_subset_1(C_133,k1_zfmisc_1(k2_zfmisc_1(A_131,B_132))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_731,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_727])).

tff(c_110,plain,(
    ! [B_47,A_48] :
      ( v1_relat_1(B_47)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(A_48))
      | ~ v1_relat_1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_113,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_42,c_110])).

tff(c_116,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_113])).

tff(c_12,plain,(
    ! [A_9] :
      ( k9_relat_1(A_9,k1_relat_1(A_9)) = k2_relat_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_125,plain,(
    ! [C_55,B_56,A_57] :
      ( v5_relat_1(C_55,B_56)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_57,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_129,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_125])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k2_relat_1(B_5),A_4)
      | ~ v5_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_187,plain,(
    ! [B_67,A_68] :
      ( k5_relat_1(B_67,k6_relat_1(A_68)) = B_67
      | ~ r1_tarski(k2_relat_1(B_67),A_68)
      | ~ v1_relat_1(B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_197,plain,(
    ! [B_5,A_4] :
      ( k5_relat_1(B_5,k6_relat_1(A_4)) = B_5
      | ~ v5_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(resolution,[status(thm)],[c_6,c_187])).

tff(c_8,plain,(
    ! [A_6] : v1_relat_1(k6_relat_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_22,plain,(
    ! [A_18] : k1_relat_1(k6_relat_1(A_18)) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_240,plain,(
    ! [A_76,B_77] :
      ( k10_relat_1(A_76,k1_relat_1(B_77)) = k1_relat_1(k5_relat_1(A_76,B_77))
      | ~ v1_relat_1(B_77)
      | ~ v1_relat_1(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_257,plain,(
    ! [A_76,A_18] :
      ( k1_relat_1(k5_relat_1(A_76,k6_relat_1(A_18))) = k10_relat_1(A_76,A_18)
      | ~ v1_relat_1(k6_relat_1(A_18))
      | ~ v1_relat_1(A_76) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_240])).

tff(c_266,plain,(
    ! [A_78,A_79] :
      ( k1_relat_1(k5_relat_1(A_78,k6_relat_1(A_79))) = k10_relat_1(A_78,A_79)
      | ~ v1_relat_1(A_78) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_257])).

tff(c_449,plain,(
    ! [B_92,A_93] :
      ( k10_relat_1(B_92,A_93) = k1_relat_1(B_92)
      | ~ v1_relat_1(B_92)
      | ~ v5_relat_1(B_92,A_93)
      | ~ v1_relat_1(B_92) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_197,c_266])).

tff(c_452,plain,
    ( k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_129,c_449])).

tff(c_458,plain,(
    k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_452])).

tff(c_529,plain,(
    ! [A_96,B_97,C_98,D_99] :
      ( k8_relset_1(A_96,B_97,C_98,D_99) = k10_relat_1(C_98,D_99)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_532,plain,(
    ! [D_99] : k8_relset_1('#skF_2','#skF_1','#skF_3',D_99) = k10_relat_1('#skF_3',D_99) ),
    inference(resolution,[status(thm)],[c_42,c_529])).

tff(c_435,plain,(
    ! [A_87,B_88,C_89,D_90] :
      ( k7_relset_1(A_87,B_88,C_89,D_90) = k9_relat_1(C_89,D_90)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_87,B_88))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_438,plain,(
    ! [D_90] : k7_relset_1('#skF_2','#skF_1','#skF_3',D_90) = k9_relat_1('#skF_3',D_90) ),
    inference(resolution,[status(thm)],[c_42,c_435])).

tff(c_425,plain,(
    ! [A_84,B_85,C_86] :
      ( k2_relset_1(A_84,B_85,C_86) = k2_relat_1(C_86)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_429,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_425])).

tff(c_40,plain,
    ( k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relset_1('#skF_2','#skF_1','#skF_3')
    | k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_109,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_430,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_429,c_109])).

tff(c_439,plain,(
    k9_relat_1('#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_438,c_430])).

tff(c_533,plain,(
    k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_532,c_439])).

tff(c_534,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_458,c_533])).

tff(c_546,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_534])).

tff(c_550,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_546])).

tff(c_551,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_732,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_731,c_551])).

tff(c_892,plain,(
    k10_relat_1('#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_890,c_732])).

tff(c_928,plain,(
    k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_927,c_892])).

tff(c_929,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_610,c_928])).

tff(c_941,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_929])).

tff(c_945,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_559,c_941])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:11:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.84/1.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.84/1.46  
% 2.84/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.84/1.46  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.84/1.46  
% 2.84/1.46  %Foreground sorts:
% 2.84/1.46  
% 2.84/1.46  
% 2.84/1.46  %Background operators:
% 2.84/1.46  
% 2.84/1.46  
% 2.84/1.46  %Foreground operators:
% 2.84/1.46  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.84/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.84/1.46  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.84/1.46  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.84/1.46  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.84/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.84/1.46  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.84/1.46  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.84/1.46  tff('#skF_2', type, '#skF_2': $i).
% 2.84/1.46  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.84/1.46  tff('#skF_3', type, '#skF_3': $i).
% 2.84/1.46  tff('#skF_1', type, '#skF_1': $i).
% 2.84/1.46  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.84/1.46  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.84/1.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.84/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.84/1.46  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.84/1.46  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.84/1.46  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.84/1.46  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.84/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.84/1.46  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.84/1.46  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.84/1.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.84/1.46  
% 2.97/1.48  tff(f_42, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.97/1.48  tff(f_106, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((k7_relset_1(B, A, C, k8_relset_1(B, A, C, A)) = k2_relset_1(B, A, C)) & (k8_relset_1(B, A, C, k7_relset_1(B, A, C, B)) = k1_relset_1(B, A, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_relset_1)).
% 2.97/1.48  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.97/1.48  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 2.97/1.48  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.97/1.48  tff(f_67, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 2.97/1.48  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 2.97/1.48  tff(f_95, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.97/1.48  tff(f_99, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.97/1.48  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.97/1.48  tff(f_46, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 2.97/1.48  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 2.97/1.48  tff(f_77, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 2.97/1.48  tff(f_40, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.97/1.48  tff(f_71, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.97/1.48  tff(f_61, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 2.97/1.48  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.97/1.48  tff(c_10, plain, (![A_7, B_8]: (v1_relat_1(k2_zfmisc_1(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.97/1.48  tff(c_42, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.97/1.48  tff(c_553, plain, (![B_101, A_102]: (v1_relat_1(B_101) | ~m1_subset_1(B_101, k1_zfmisc_1(A_102)) | ~v1_relat_1(A_102))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.97/1.48  tff(c_556, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_42, c_553])).
% 2.97/1.48  tff(c_559, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_556])).
% 2.97/1.48  tff(c_16, plain, (![A_12]: (k10_relat_1(A_12, k2_relat_1(A_12))=k1_relat_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.97/1.48  tff(c_588, plain, (![C_114, A_115, B_116]: (v4_relat_1(C_114, A_115) | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1(A_115, B_116))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.97/1.48  tff(c_592, plain, (v4_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_42, c_588])).
% 2.97/1.48  tff(c_20, plain, (![B_17, A_16]: (k7_relat_1(B_17, A_16)=B_17 | ~v4_relat_1(B_17, A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.97/1.48  tff(c_595, plain, (k7_relat_1('#skF_3', '#skF_2')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_592, c_20])).
% 2.97/1.48  tff(c_598, plain, (k7_relat_1('#skF_3', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_559, c_595])).
% 2.97/1.48  tff(c_14, plain, (![B_11, A_10]: (k2_relat_1(k7_relat_1(B_11, A_10))=k9_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.97/1.48  tff(c_606, plain, (k9_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_598, c_14])).
% 2.97/1.48  tff(c_610, plain, (k9_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_559, c_606])).
% 2.97/1.48  tff(c_924, plain, (![A_148, B_149, C_150, D_151]: (k7_relset_1(A_148, B_149, C_150, D_151)=k9_relat_1(C_150, D_151) | ~m1_subset_1(C_150, k1_zfmisc_1(k2_zfmisc_1(A_148, B_149))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.97/1.48  tff(c_927, plain, (![D_151]: (k7_relset_1('#skF_2', '#skF_1', '#skF_3', D_151)=k9_relat_1('#skF_3', D_151))), inference(resolution, [status(thm)], [c_42, c_924])).
% 2.97/1.48  tff(c_887, plain, (![A_141, B_142, C_143, D_144]: (k8_relset_1(A_141, B_142, C_143, D_144)=k10_relat_1(C_143, D_144) | ~m1_subset_1(C_143, k1_zfmisc_1(k2_zfmisc_1(A_141, B_142))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.97/1.48  tff(c_890, plain, (![D_144]: (k8_relset_1('#skF_2', '#skF_1', '#skF_3', D_144)=k10_relat_1('#skF_3', D_144))), inference(resolution, [status(thm)], [c_42, c_887])).
% 2.97/1.48  tff(c_727, plain, (![A_131, B_132, C_133]: (k1_relset_1(A_131, B_132, C_133)=k1_relat_1(C_133) | ~m1_subset_1(C_133, k1_zfmisc_1(k2_zfmisc_1(A_131, B_132))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.97/1.48  tff(c_731, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_42, c_727])).
% 2.97/1.48  tff(c_110, plain, (![B_47, A_48]: (v1_relat_1(B_47) | ~m1_subset_1(B_47, k1_zfmisc_1(A_48)) | ~v1_relat_1(A_48))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.97/1.48  tff(c_113, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_42, c_110])).
% 2.97/1.48  tff(c_116, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_113])).
% 2.97/1.48  tff(c_12, plain, (![A_9]: (k9_relat_1(A_9, k1_relat_1(A_9))=k2_relat_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.97/1.48  tff(c_125, plain, (![C_55, B_56, A_57]: (v5_relat_1(C_55, B_56) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_57, B_56))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.97/1.48  tff(c_129, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_42, c_125])).
% 2.97/1.48  tff(c_6, plain, (![B_5, A_4]: (r1_tarski(k2_relat_1(B_5), A_4) | ~v5_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.97/1.48  tff(c_187, plain, (![B_67, A_68]: (k5_relat_1(B_67, k6_relat_1(A_68))=B_67 | ~r1_tarski(k2_relat_1(B_67), A_68) | ~v1_relat_1(B_67))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.97/1.48  tff(c_197, plain, (![B_5, A_4]: (k5_relat_1(B_5, k6_relat_1(A_4))=B_5 | ~v5_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(resolution, [status(thm)], [c_6, c_187])).
% 2.97/1.48  tff(c_8, plain, (![A_6]: (v1_relat_1(k6_relat_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.97/1.48  tff(c_22, plain, (![A_18]: (k1_relat_1(k6_relat_1(A_18))=A_18)), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.97/1.48  tff(c_240, plain, (![A_76, B_77]: (k10_relat_1(A_76, k1_relat_1(B_77))=k1_relat_1(k5_relat_1(A_76, B_77)) | ~v1_relat_1(B_77) | ~v1_relat_1(A_76))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.97/1.48  tff(c_257, plain, (![A_76, A_18]: (k1_relat_1(k5_relat_1(A_76, k6_relat_1(A_18)))=k10_relat_1(A_76, A_18) | ~v1_relat_1(k6_relat_1(A_18)) | ~v1_relat_1(A_76))), inference(superposition, [status(thm), theory('equality')], [c_22, c_240])).
% 2.97/1.48  tff(c_266, plain, (![A_78, A_79]: (k1_relat_1(k5_relat_1(A_78, k6_relat_1(A_79)))=k10_relat_1(A_78, A_79) | ~v1_relat_1(A_78))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_257])).
% 2.97/1.48  tff(c_449, plain, (![B_92, A_93]: (k10_relat_1(B_92, A_93)=k1_relat_1(B_92) | ~v1_relat_1(B_92) | ~v5_relat_1(B_92, A_93) | ~v1_relat_1(B_92))), inference(superposition, [status(thm), theory('equality')], [c_197, c_266])).
% 2.97/1.48  tff(c_452, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_129, c_449])).
% 2.97/1.48  tff(c_458, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_116, c_452])).
% 2.97/1.48  tff(c_529, plain, (![A_96, B_97, C_98, D_99]: (k8_relset_1(A_96, B_97, C_98, D_99)=k10_relat_1(C_98, D_99) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.97/1.48  tff(c_532, plain, (![D_99]: (k8_relset_1('#skF_2', '#skF_1', '#skF_3', D_99)=k10_relat_1('#skF_3', D_99))), inference(resolution, [status(thm)], [c_42, c_529])).
% 2.97/1.48  tff(c_435, plain, (![A_87, B_88, C_89, D_90]: (k7_relset_1(A_87, B_88, C_89, D_90)=k9_relat_1(C_89, D_90) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_87, B_88))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.97/1.48  tff(c_438, plain, (![D_90]: (k7_relset_1('#skF_2', '#skF_1', '#skF_3', D_90)=k9_relat_1('#skF_3', D_90))), inference(resolution, [status(thm)], [c_42, c_435])).
% 2.97/1.48  tff(c_425, plain, (![A_84, B_85, C_86]: (k2_relset_1(A_84, B_85, C_86)=k2_relat_1(C_86) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.97/1.48  tff(c_429, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_42, c_425])).
% 2.97/1.48  tff(c_40, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relset_1('#skF_2', '#skF_1', '#skF_3') | k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.97/1.48  tff(c_109, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_40])).
% 2.97/1.48  tff(c_430, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_429, c_109])).
% 2.97/1.48  tff(c_439, plain, (k9_relat_1('#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_438, c_430])).
% 2.97/1.48  tff(c_533, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_532, c_439])).
% 2.97/1.48  tff(c_534, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_458, c_533])).
% 2.97/1.48  tff(c_546, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_12, c_534])).
% 2.97/1.48  tff(c_550, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_116, c_546])).
% 2.97/1.48  tff(c_551, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_40])).
% 2.97/1.48  tff(c_732, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_731, c_551])).
% 2.97/1.48  tff(c_892, plain, (k10_relat_1('#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_890, c_732])).
% 2.97/1.48  tff(c_928, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_927, c_892])).
% 2.97/1.48  tff(c_929, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_610, c_928])).
% 2.97/1.48  tff(c_941, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_16, c_929])).
% 2.97/1.48  tff(c_945, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_559, c_941])).
% 2.97/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.97/1.48  
% 2.97/1.48  Inference rules
% 2.97/1.48  ----------------------
% 2.97/1.48  #Ref     : 0
% 2.97/1.48  #Sup     : 201
% 2.97/1.48  #Fact    : 0
% 2.97/1.48  #Define  : 0
% 2.97/1.48  #Split   : 1
% 2.97/1.48  #Chain   : 0
% 2.97/1.48  #Close   : 0
% 2.97/1.48  
% 2.97/1.48  Ordering : KBO
% 2.97/1.48  
% 2.97/1.48  Simplification rules
% 2.97/1.48  ----------------------
% 2.97/1.48  #Subsume      : 6
% 2.97/1.48  #Demod        : 139
% 2.97/1.48  #Tautology    : 118
% 2.97/1.48  #SimpNegUnit  : 0
% 2.97/1.48  #BackRed      : 9
% 2.97/1.48  
% 2.97/1.48  #Partial instantiations: 0
% 2.97/1.48  #Strategies tried      : 1
% 2.97/1.48  
% 2.97/1.48  Timing (in seconds)
% 2.97/1.48  ----------------------
% 2.97/1.48  Preprocessing        : 0.32
% 2.97/1.48  Parsing              : 0.18
% 2.97/1.48  CNF conversion       : 0.02
% 2.97/1.48  Main loop            : 0.36
% 2.97/1.48  Inferencing          : 0.15
% 2.97/1.48  Reduction            : 0.11
% 2.97/1.48  Demodulation         : 0.08
% 2.97/1.48  BG Simplification    : 0.02
% 2.97/1.48  Subsumption          : 0.04
% 2.97/1.48  Abstraction          : 0.02
% 2.97/1.48  MUC search           : 0.00
% 2.97/1.48  Cooper               : 0.00
% 2.97/1.48  Total                : 0.72
% 2.97/1.48  Index Insertion      : 0.00
% 2.97/1.48  Index Deletion       : 0.00
% 2.97/1.49  Index Matching       : 0.00
% 2.97/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
