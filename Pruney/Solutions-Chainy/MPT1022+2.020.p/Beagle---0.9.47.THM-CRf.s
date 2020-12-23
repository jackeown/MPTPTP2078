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
% DateTime   : Thu Dec  3 10:16:16 EST 2020

% Result     : Theorem 3.11s
% Output     : CNFRefutation 3.30s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 312 expanded)
%              Number of leaves         :   39 ( 132 expanded)
%              Depth                    :   15
%              Number of atoms          :  235 ( 972 expanded)
%              Number of equality atoms :   46 ( 203 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k9_relat_1 > k2_zfmisc_1 > k2_funct_2 > k10_relat_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k2_funct_2,type,(
    k2_funct_2: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v2_funct_2,type,(
    v2_funct_2: ( $i * $i ) > $o )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v3_funct_2,type,(
    v3_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_137,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,A)
          & v3_funct_2(C,A,A)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( r1_tarski(B,A)
         => ( k7_relset_1(A,A,C,k8_relset_1(A,A,C,B)) = B
            & k8_relset_1(A,A,C,k7_relset_1(A,A,C,B)) = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_funct_2)).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_122,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_112,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => ( v1_funct_1(k2_funct_2(A,B))
        & v1_funct_2(k2_funct_2(A,B),A,A)
        & v3_funct_2(k2_funct_2(A,B),A,A)
        & m1_subset_1(k2_funct_2(A,B),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_2)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_96,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_62,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( ( r1_tarski(A,k1_relat_1(B))
          & v2_funct_1(B) )
       => k10_relat_1(B,k9_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_1)).

tff(f_72,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_76,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

tff(c_44,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_46,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_54,plain,(
    ! [B_33,A_34] :
      ( v1_relat_1(B_33)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(A_34))
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_57,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_46,c_54])).

tff(c_60,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_57])).

tff(c_52,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_48,plain,(
    v3_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_390,plain,(
    ! [C_118,A_119,B_120] :
      ( v2_funct_1(C_118)
      | ~ v3_funct_2(C_118,A_119,B_120)
      | ~ v1_funct_1(C_118)
      | ~ m1_subset_1(C_118,k1_zfmisc_1(k2_zfmisc_1(A_119,B_120))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_393,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_390])).

tff(c_396,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48,c_393])).

tff(c_50,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_447,plain,(
    ! [A_131,B_132] :
      ( k2_funct_2(A_131,B_132) = k2_funct_1(B_132)
      | ~ m1_subset_1(B_132,k1_zfmisc_1(k2_zfmisc_1(A_131,A_131)))
      | ~ v3_funct_2(B_132,A_131,A_131)
      | ~ v1_funct_2(B_132,A_131,A_131)
      | ~ v1_funct_1(B_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_450,plain,
    ( k2_funct_2('#skF_1','#skF_3') = k2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_447])).

tff(c_453,plain,(
    k2_funct_2('#skF_1','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_450])).

tff(c_440,plain,(
    ! [A_129,B_130] :
      ( v1_funct_1(k2_funct_2(A_129,B_130))
      | ~ m1_subset_1(B_130,k1_zfmisc_1(k2_zfmisc_1(A_129,A_129)))
      | ~ v3_funct_2(B_130,A_129,A_129)
      | ~ v1_funct_2(B_130,A_129,A_129)
      | ~ v1_funct_1(B_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_443,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_440])).

tff(c_446,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_443])).

tff(c_454,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_453,c_446])).

tff(c_459,plain,(
    ! [A_133,B_134] :
      ( v3_funct_2(k2_funct_2(A_133,B_134),A_133,A_133)
      | ~ m1_subset_1(B_134,k1_zfmisc_1(k2_zfmisc_1(A_133,A_133)))
      | ~ v3_funct_2(B_134,A_133,A_133)
      | ~ v1_funct_2(B_134,A_133,A_133)
      | ~ v1_funct_1(B_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_461,plain,
    ( v3_funct_2(k2_funct_2('#skF_1','#skF_3'),'#skF_1','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_459])).

tff(c_464,plain,(
    v3_funct_2(k2_funct_1('#skF_3'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_453,c_461])).

tff(c_475,plain,(
    ! [A_138,B_139] :
      ( m1_subset_1(k2_funct_2(A_138,B_139),k1_zfmisc_1(k2_zfmisc_1(A_138,A_138)))
      | ~ m1_subset_1(B_139,k1_zfmisc_1(k2_zfmisc_1(A_138,A_138)))
      | ~ v3_funct_2(B_139,A_138,A_138)
      | ~ v1_funct_2(B_139,A_138,A_138)
      | ~ v1_funct_1(B_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_507,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_453,c_475])).

tff(c_522,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_507])).

tff(c_22,plain,(
    ! [C_24,B_23,A_22] :
      ( v2_funct_2(C_24,B_23)
      | ~ v3_funct_2(C_24,A_22,B_23)
      | ~ v1_funct_1(C_24)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_549,plain,
    ( v2_funct_2(k2_funct_1('#skF_3'),'#skF_1')
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_522,c_22])).

tff(c_583,plain,(
    v2_funct_2(k2_funct_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_454,c_464,c_549])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v1_relat_1(B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_504,plain,(
    ! [A_138,B_139] :
      ( v1_relat_1(k2_funct_2(A_138,B_139))
      | ~ v1_relat_1(k2_zfmisc_1(A_138,A_138))
      | ~ m1_subset_1(B_139,k1_zfmisc_1(k2_zfmisc_1(A_138,A_138)))
      | ~ v3_funct_2(B_139,A_138,A_138)
      | ~ v1_funct_2(B_139,A_138,A_138)
      | ~ v1_funct_1(B_139) ) ),
    inference(resolution,[status(thm)],[c_475,c_2])).

tff(c_523,plain,(
    ! [A_140,B_141] :
      ( v1_relat_1(k2_funct_2(A_140,B_141))
      | ~ m1_subset_1(B_141,k1_zfmisc_1(k2_zfmisc_1(A_140,A_140)))
      | ~ v3_funct_2(B_141,A_140,A_140)
      | ~ v1_funct_2(B_141,A_140,A_140)
      | ~ v1_funct_1(B_141) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_504])).

tff(c_529,plain,
    ( v1_relat_1(k2_funct_2('#skF_1','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_523])).

tff(c_533,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_453,c_529])).

tff(c_14,plain,(
    ! [C_13,B_12,A_11] :
      ( v5_relat_1(C_13,B_12)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(A_11,B_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_590,plain,(
    v5_relat_1(k2_funct_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_522,c_14])).

tff(c_30,plain,(
    ! [B_26,A_25] :
      ( k2_relat_1(B_26) = A_25
      | ~ v2_funct_2(B_26,A_25)
      | ~ v5_relat_1(B_26,A_25)
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_596,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1'
    | ~ v2_funct_2(k2_funct_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_590,c_30])).

tff(c_599,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1'
    | ~ v2_funct_2(k2_funct_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_533,c_596])).

tff(c_670,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_583,c_599])).

tff(c_10,plain,(
    ! [A_10] :
      ( k2_relat_1(k2_funct_1(A_10)) = k1_relat_1(A_10)
      | ~ v2_funct_1(A_10)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_679,plain,
    ( k1_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_670,c_10])).

tff(c_693,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_52,c_396,c_679])).

tff(c_8,plain,(
    ! [B_9,A_8] :
      ( k10_relat_1(B_9,k9_relat_1(B_9,A_8)) = A_8
      | ~ v2_funct_1(B_9)
      | ~ r1_tarski(A_8,k1_relat_1(B_9))
      | ~ v1_funct_1(B_9)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_701,plain,(
    ! [A_8] :
      ( k10_relat_1('#skF_3',k9_relat_1('#skF_3',A_8)) = A_8
      | ~ v2_funct_1('#skF_3')
      | ~ r1_tarski(A_8,'#skF_1')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_693,c_8])).

tff(c_895,plain,(
    ! [A_152] :
      ( k10_relat_1('#skF_3',k9_relat_1('#skF_3',A_152)) = A_152
      | ~ r1_tarski(A_152,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_52,c_396,c_701])).

tff(c_370,plain,(
    ! [A_113,B_114,C_115,D_116] :
      ( k7_relset_1(A_113,B_114,C_115,D_116) = k9_relat_1(C_115,D_116)
      | ~ m1_subset_1(C_115,k1_zfmisc_1(k2_zfmisc_1(A_113,B_114))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_373,plain,(
    ! [D_116] : k7_relset_1('#skF_1','#skF_1','#skF_3',D_116) = k9_relat_1('#skF_3',D_116) ),
    inference(resolution,[status(thm)],[c_46,c_370])).

tff(c_351,plain,(
    ! [A_108,B_109,C_110,D_111] :
      ( k8_relset_1(A_108,B_109,C_110,D_111) = k10_relat_1(C_110,D_111)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(A_108,B_109))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_354,plain,(
    ! [D_111] : k8_relset_1('#skF_1','#skF_1','#skF_3',D_111) = k10_relat_1('#skF_3',D_111) ),
    inference(resolution,[status(thm)],[c_46,c_351])).

tff(c_61,plain,(
    ! [C_35,B_36,A_37] :
      ( v5_relat_1(C_35,B_36)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_37,B_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_65,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_61])).

tff(c_73,plain,(
    ! [B_42,A_43] :
      ( k2_relat_1(B_42) = A_43
      | ~ v2_funct_2(B_42,A_43)
      | ~ v5_relat_1(B_42,A_43)
      | ~ v1_relat_1(B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_76,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_65,c_73])).

tff(c_79,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_76])).

tff(c_80,plain,(
    ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_79])).

tff(c_140,plain,(
    ! [C_61,B_62,A_63] :
      ( v2_funct_2(C_61,B_62)
      | ~ v3_funct_2(C_61,A_63,B_62)
      | ~ v1_funct_1(C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_63,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_143,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_140])).

tff(c_146,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48,c_143])).

tff(c_148,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_146])).

tff(c_149,plain,(
    k2_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_79])).

tff(c_203,plain,(
    ! [B_74,A_75] :
      ( k9_relat_1(B_74,k10_relat_1(B_74,A_75)) = A_75
      | ~ r1_tarski(A_75,k2_relat_1(B_74))
      | ~ v1_funct_1(B_74)
      | ~ v1_relat_1(B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_207,plain,(
    ! [A_75] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_75)) = A_75
      | ~ r1_tarski(A_75,'#skF_1')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_203])).

tff(c_209,plain,(
    ! [A_75] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_75)) = A_75
      | ~ r1_tarski(A_75,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_52,c_207])).

tff(c_219,plain,(
    ! [A_77,B_78,C_79,D_80] :
      ( k7_relset_1(A_77,B_78,C_79,D_80) = k9_relat_1(C_79,D_80)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_222,plain,(
    ! [D_80] : k7_relset_1('#skF_1','#skF_1','#skF_3',D_80) = k9_relat_1('#skF_3',D_80) ),
    inference(resolution,[status(thm)],[c_46,c_219])).

tff(c_189,plain,(
    ! [A_69,B_70,C_71,D_72] :
      ( k8_relset_1(A_69,B_70,C_71,D_72) = k10_relat_1(C_71,D_72)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_192,plain,(
    ! [D_72] : k8_relset_1('#skF_1','#skF_1','#skF_3',D_72) = k10_relat_1('#skF_3',D_72) ),
    inference(resolution,[status(thm)],[c_46,c_189])).

tff(c_42,plain,
    ( k8_relset_1('#skF_1','#skF_1','#skF_3',k7_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2'
    | k7_relset_1('#skF_1','#skF_1','#skF_3',k8_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_66,plain,(
    k7_relset_1('#skF_1','#skF_1','#skF_3',k8_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_193,plain,(
    k7_relset_1('#skF_1','#skF_1','#skF_3',k10_relat_1('#skF_3','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_66])).

tff(c_223,plain,(
    k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_222,c_193])).

tff(c_235,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_209,c_223])).

tff(c_239,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_235])).

tff(c_240,plain,(
    k8_relset_1('#skF_1','#skF_1','#skF_3',k7_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_356,plain,(
    k10_relat_1('#skF_3',k7_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_354,c_240])).

tff(c_374,plain,(
    k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_373,c_356])).

tff(c_904,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_895,c_374])).

tff(c_919,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_904])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:30:15 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.11/1.50  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.11/1.51  
% 3.11/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.11/1.51  %$ v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k9_relat_1 > k2_zfmisc_1 > k2_funct_2 > k10_relat_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.11/1.51  
% 3.11/1.51  %Foreground sorts:
% 3.11/1.51  
% 3.11/1.51  
% 3.11/1.51  %Background operators:
% 3.11/1.51  
% 3.11/1.51  
% 3.11/1.51  %Foreground operators:
% 3.11/1.51  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.11/1.51  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.11/1.51  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.11/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.11/1.51  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.11/1.51  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 3.11/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.11/1.51  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.11/1.51  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.11/1.51  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.11/1.51  tff('#skF_2', type, '#skF_2': $i).
% 3.11/1.51  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.11/1.51  tff('#skF_3', type, '#skF_3': $i).
% 3.11/1.51  tff('#skF_1', type, '#skF_1': $i).
% 3.11/1.51  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 3.11/1.51  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.11/1.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.11/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.11/1.51  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.11/1.51  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.11/1.51  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.11/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.11/1.51  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.11/1.51  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 3.11/1.51  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.11/1.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.11/1.51  
% 3.30/1.53  tff(f_137, negated_conjecture, ~(![A, B, C]: ((((v1_funct_1(C) & v1_funct_2(C, A, A)) & v3_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r1_tarski(B, A) => ((k7_relset_1(A, A, C, k8_relset_1(A, A, C, B)) = B) & (k8_relset_1(A, A, C, k7_relset_1(A, A, C, B)) = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_funct_2)).
% 3.30/1.53  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.30/1.53  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.30/1.53  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_funct_2)).
% 3.30/1.53  tff(f_122, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 3.30/1.53  tff(f_112, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 3.30/1.53  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.30/1.53  tff(f_96, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 3.30/1.53  tff(f_62, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 3.30/1.53  tff(f_52, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((r1_tarski(A, k1_relat_1(B)) & v2_funct_1(B)) => (k10_relat_1(B, k9_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t164_funct_1)).
% 3.30/1.53  tff(f_72, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.30/1.53  tff(f_76, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.30/1.53  tff(f_42, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_funct_1)).
% 3.30/1.53  tff(c_44, plain, (r1_tarski('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.30/1.53  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.30/1.53  tff(c_46, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.30/1.53  tff(c_54, plain, (![B_33, A_34]: (v1_relat_1(B_33) | ~m1_subset_1(B_33, k1_zfmisc_1(A_34)) | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.30/1.53  tff(c_57, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_46, c_54])).
% 3.30/1.53  tff(c_60, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_57])).
% 3.30/1.53  tff(c_52, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.30/1.53  tff(c_48, plain, (v3_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.30/1.53  tff(c_390, plain, (![C_118, A_119, B_120]: (v2_funct_1(C_118) | ~v3_funct_2(C_118, A_119, B_120) | ~v1_funct_1(C_118) | ~m1_subset_1(C_118, k1_zfmisc_1(k2_zfmisc_1(A_119, B_120))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.30/1.53  tff(c_393, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_390])).
% 3.30/1.53  tff(c_396, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_48, c_393])).
% 3.30/1.53  tff(c_50, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.30/1.53  tff(c_447, plain, (![A_131, B_132]: (k2_funct_2(A_131, B_132)=k2_funct_1(B_132) | ~m1_subset_1(B_132, k1_zfmisc_1(k2_zfmisc_1(A_131, A_131))) | ~v3_funct_2(B_132, A_131, A_131) | ~v1_funct_2(B_132, A_131, A_131) | ~v1_funct_1(B_132))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.30/1.53  tff(c_450, plain, (k2_funct_2('#skF_1', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_447])).
% 3.30/1.53  tff(c_453, plain, (k2_funct_2('#skF_1', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_450])).
% 3.30/1.53  tff(c_440, plain, (![A_129, B_130]: (v1_funct_1(k2_funct_2(A_129, B_130)) | ~m1_subset_1(B_130, k1_zfmisc_1(k2_zfmisc_1(A_129, A_129))) | ~v3_funct_2(B_130, A_129, A_129) | ~v1_funct_2(B_130, A_129, A_129) | ~v1_funct_1(B_130))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.30/1.53  tff(c_443, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_440])).
% 3.30/1.53  tff(c_446, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_443])).
% 3.30/1.53  tff(c_454, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_453, c_446])).
% 3.30/1.53  tff(c_459, plain, (![A_133, B_134]: (v3_funct_2(k2_funct_2(A_133, B_134), A_133, A_133) | ~m1_subset_1(B_134, k1_zfmisc_1(k2_zfmisc_1(A_133, A_133))) | ~v3_funct_2(B_134, A_133, A_133) | ~v1_funct_2(B_134, A_133, A_133) | ~v1_funct_1(B_134))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.30/1.53  tff(c_461, plain, (v3_funct_2(k2_funct_2('#skF_1', '#skF_3'), '#skF_1', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_459])).
% 3.30/1.53  tff(c_464, plain, (v3_funct_2(k2_funct_1('#skF_3'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_453, c_461])).
% 3.30/1.53  tff(c_475, plain, (![A_138, B_139]: (m1_subset_1(k2_funct_2(A_138, B_139), k1_zfmisc_1(k2_zfmisc_1(A_138, A_138))) | ~m1_subset_1(B_139, k1_zfmisc_1(k2_zfmisc_1(A_138, A_138))) | ~v3_funct_2(B_139, A_138, A_138) | ~v1_funct_2(B_139, A_138, A_138) | ~v1_funct_1(B_139))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.30/1.53  tff(c_507, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_453, c_475])).
% 3.30/1.53  tff(c_522, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_507])).
% 3.30/1.53  tff(c_22, plain, (![C_24, B_23, A_22]: (v2_funct_2(C_24, B_23) | ~v3_funct_2(C_24, A_22, B_23) | ~v1_funct_1(C_24) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.30/1.53  tff(c_549, plain, (v2_funct_2(k2_funct_1('#skF_3'), '#skF_1') | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_522, c_22])).
% 3.30/1.53  tff(c_583, plain, (v2_funct_2(k2_funct_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_454, c_464, c_549])).
% 3.30/1.53  tff(c_2, plain, (![B_3, A_1]: (v1_relat_1(B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.30/1.53  tff(c_504, plain, (![A_138, B_139]: (v1_relat_1(k2_funct_2(A_138, B_139)) | ~v1_relat_1(k2_zfmisc_1(A_138, A_138)) | ~m1_subset_1(B_139, k1_zfmisc_1(k2_zfmisc_1(A_138, A_138))) | ~v3_funct_2(B_139, A_138, A_138) | ~v1_funct_2(B_139, A_138, A_138) | ~v1_funct_1(B_139))), inference(resolution, [status(thm)], [c_475, c_2])).
% 3.30/1.53  tff(c_523, plain, (![A_140, B_141]: (v1_relat_1(k2_funct_2(A_140, B_141)) | ~m1_subset_1(B_141, k1_zfmisc_1(k2_zfmisc_1(A_140, A_140))) | ~v3_funct_2(B_141, A_140, A_140) | ~v1_funct_2(B_141, A_140, A_140) | ~v1_funct_1(B_141))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_504])).
% 3.30/1.53  tff(c_529, plain, (v1_relat_1(k2_funct_2('#skF_1', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_523])).
% 3.30/1.53  tff(c_533, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_453, c_529])).
% 3.30/1.53  tff(c_14, plain, (![C_13, B_12, A_11]: (v5_relat_1(C_13, B_12) | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(A_11, B_12))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.30/1.53  tff(c_590, plain, (v5_relat_1(k2_funct_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_522, c_14])).
% 3.30/1.53  tff(c_30, plain, (![B_26, A_25]: (k2_relat_1(B_26)=A_25 | ~v2_funct_2(B_26, A_25) | ~v5_relat_1(B_26, A_25) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.30/1.53  tff(c_596, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1' | ~v2_funct_2(k2_funct_1('#skF_3'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_590, c_30])).
% 3.30/1.53  tff(c_599, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1' | ~v2_funct_2(k2_funct_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_533, c_596])).
% 3.30/1.53  tff(c_670, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_583, c_599])).
% 3.30/1.53  tff(c_10, plain, (![A_10]: (k2_relat_1(k2_funct_1(A_10))=k1_relat_1(A_10) | ~v2_funct_1(A_10) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.30/1.53  tff(c_679, plain, (k1_relat_1('#skF_3')='#skF_1' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_670, c_10])).
% 3.30/1.53  tff(c_693, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_52, c_396, c_679])).
% 3.30/1.53  tff(c_8, plain, (![B_9, A_8]: (k10_relat_1(B_9, k9_relat_1(B_9, A_8))=A_8 | ~v2_funct_1(B_9) | ~r1_tarski(A_8, k1_relat_1(B_9)) | ~v1_funct_1(B_9) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.30/1.53  tff(c_701, plain, (![A_8]: (k10_relat_1('#skF_3', k9_relat_1('#skF_3', A_8))=A_8 | ~v2_funct_1('#skF_3') | ~r1_tarski(A_8, '#skF_1') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_693, c_8])).
% 3.30/1.53  tff(c_895, plain, (![A_152]: (k10_relat_1('#skF_3', k9_relat_1('#skF_3', A_152))=A_152 | ~r1_tarski(A_152, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_52, c_396, c_701])).
% 3.30/1.53  tff(c_370, plain, (![A_113, B_114, C_115, D_116]: (k7_relset_1(A_113, B_114, C_115, D_116)=k9_relat_1(C_115, D_116) | ~m1_subset_1(C_115, k1_zfmisc_1(k2_zfmisc_1(A_113, B_114))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.30/1.53  tff(c_373, plain, (![D_116]: (k7_relset_1('#skF_1', '#skF_1', '#skF_3', D_116)=k9_relat_1('#skF_3', D_116))), inference(resolution, [status(thm)], [c_46, c_370])).
% 3.30/1.53  tff(c_351, plain, (![A_108, B_109, C_110, D_111]: (k8_relset_1(A_108, B_109, C_110, D_111)=k10_relat_1(C_110, D_111) | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(A_108, B_109))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.30/1.53  tff(c_354, plain, (![D_111]: (k8_relset_1('#skF_1', '#skF_1', '#skF_3', D_111)=k10_relat_1('#skF_3', D_111))), inference(resolution, [status(thm)], [c_46, c_351])).
% 3.30/1.53  tff(c_61, plain, (![C_35, B_36, A_37]: (v5_relat_1(C_35, B_36) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_37, B_36))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.30/1.53  tff(c_65, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_46, c_61])).
% 3.30/1.53  tff(c_73, plain, (![B_42, A_43]: (k2_relat_1(B_42)=A_43 | ~v2_funct_2(B_42, A_43) | ~v5_relat_1(B_42, A_43) | ~v1_relat_1(B_42))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.30/1.53  tff(c_76, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_65, c_73])).
% 3.30/1.53  tff(c_79, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_76])).
% 3.30/1.53  tff(c_80, plain, (~v2_funct_2('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_79])).
% 3.30/1.53  tff(c_140, plain, (![C_61, B_62, A_63]: (v2_funct_2(C_61, B_62) | ~v3_funct_2(C_61, A_63, B_62) | ~v1_funct_1(C_61) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_63, B_62))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.30/1.53  tff(c_143, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_140])).
% 3.30/1.53  tff(c_146, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_48, c_143])).
% 3.30/1.53  tff(c_148, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_146])).
% 3.30/1.53  tff(c_149, plain, (k2_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_79])).
% 3.30/1.53  tff(c_203, plain, (![B_74, A_75]: (k9_relat_1(B_74, k10_relat_1(B_74, A_75))=A_75 | ~r1_tarski(A_75, k2_relat_1(B_74)) | ~v1_funct_1(B_74) | ~v1_relat_1(B_74))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.30/1.53  tff(c_207, plain, (![A_75]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_75))=A_75 | ~r1_tarski(A_75, '#skF_1') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_149, c_203])).
% 3.30/1.53  tff(c_209, plain, (![A_75]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_75))=A_75 | ~r1_tarski(A_75, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_52, c_207])).
% 3.30/1.53  tff(c_219, plain, (![A_77, B_78, C_79, D_80]: (k7_relset_1(A_77, B_78, C_79, D_80)=k9_relat_1(C_79, D_80) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.30/1.53  tff(c_222, plain, (![D_80]: (k7_relset_1('#skF_1', '#skF_1', '#skF_3', D_80)=k9_relat_1('#skF_3', D_80))), inference(resolution, [status(thm)], [c_46, c_219])).
% 3.30/1.53  tff(c_189, plain, (![A_69, B_70, C_71, D_72]: (k8_relset_1(A_69, B_70, C_71, D_72)=k10_relat_1(C_71, D_72) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.30/1.53  tff(c_192, plain, (![D_72]: (k8_relset_1('#skF_1', '#skF_1', '#skF_3', D_72)=k10_relat_1('#skF_3', D_72))), inference(resolution, [status(thm)], [c_46, c_189])).
% 3.30/1.53  tff(c_42, plain, (k8_relset_1('#skF_1', '#skF_1', '#skF_3', k7_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2' | k7_relset_1('#skF_1', '#skF_1', '#skF_3', k8_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.30/1.53  tff(c_66, plain, (k7_relset_1('#skF_1', '#skF_1', '#skF_3', k8_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_42])).
% 3.30/1.53  tff(c_193, plain, (k7_relset_1('#skF_1', '#skF_1', '#skF_3', k10_relat_1('#skF_3', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_192, c_66])).
% 3.30/1.53  tff(c_223, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_222, c_193])).
% 3.30/1.53  tff(c_235, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_209, c_223])).
% 3.30/1.53  tff(c_239, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_235])).
% 3.30/1.53  tff(c_240, plain, (k8_relset_1('#skF_1', '#skF_1', '#skF_3', k7_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2'), inference(splitRight, [status(thm)], [c_42])).
% 3.30/1.53  tff(c_356, plain, (k10_relat_1('#skF_3', k7_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_354, c_240])).
% 3.30/1.53  tff(c_374, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_373, c_356])).
% 3.30/1.53  tff(c_904, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_895, c_374])).
% 3.30/1.53  tff(c_919, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_904])).
% 3.30/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.30/1.53  
% 3.30/1.53  Inference rules
% 3.30/1.53  ----------------------
% 3.30/1.53  #Ref     : 0
% 3.30/1.53  #Sup     : 186
% 3.30/1.53  #Fact    : 0
% 3.30/1.53  #Define  : 0
% 3.30/1.53  #Split   : 3
% 3.30/1.53  #Chain   : 0
% 3.30/1.53  #Close   : 0
% 3.30/1.53  
% 3.30/1.53  Ordering : KBO
% 3.30/1.53  
% 3.30/1.53  Simplification rules
% 3.30/1.53  ----------------------
% 3.30/1.53  #Subsume      : 0
% 3.30/1.53  #Demod        : 216
% 3.30/1.53  #Tautology    : 92
% 3.30/1.53  #SimpNegUnit  : 2
% 3.30/1.53  #BackRed      : 21
% 3.30/1.53  
% 3.30/1.53  #Partial instantiations: 0
% 3.30/1.53  #Strategies tried      : 1
% 3.30/1.53  
% 3.30/1.53  Timing (in seconds)
% 3.30/1.53  ----------------------
% 3.30/1.53  Preprocessing        : 0.35
% 3.30/1.53  Parsing              : 0.19
% 3.30/1.53  CNF conversion       : 0.02
% 3.30/1.53  Main loop            : 0.40
% 3.30/1.53  Inferencing          : 0.15
% 3.30/1.53  Reduction            : 0.13
% 3.30/1.54  Demodulation         : 0.09
% 3.30/1.54  BG Simplification    : 0.02
% 3.30/1.54  Subsumption          : 0.06
% 3.30/1.54  Abstraction          : 0.02
% 3.30/1.54  MUC search           : 0.00
% 3.30/1.54  Cooper               : 0.00
% 3.30/1.54  Total                : 0.79
% 3.30/1.54  Index Insertion      : 0.00
% 3.30/1.54  Index Deletion       : 0.00
% 3.30/1.54  Index Matching       : 0.00
% 3.30/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
