%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:14 EST 2020

% Result     : Theorem 7.69s
% Output     : CNFRefutation 8.08s
% Verified   : 
% Statistics : Number of formulae       :  170 ( 743 expanded)
%              Number of leaves         :   46 ( 287 expanded)
%              Depth                    :   19
%              Number of atoms          :  334 (2237 expanded)
%              Number of equality atoms :   74 ( 442 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_funct_2 > k10_relat_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(f_167,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,A)
          & v3_funct_2(C,A,A)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( r1_tarski(B,A)
         => ( k7_relset_1(A,A,C,k8_relset_1(A,A,C,B)) = B
            & k8_relset_1(A,A,C,k7_relset_1(A,A,C,B)) = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_funct_2)).

tff(f_46,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_118,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_126,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_152,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_142,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => ( v1_funct_1(k2_funct_2(A,B))
        & v1_funct_2(k2_funct_2(A,B),A,A)
        & v3_funct_2(k2_funct_2(A,B),A,A)
        & m1_subset_1(k2_funct_2(A,B),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k9_relat_1(B,A) = k10_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_funct_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( ( r1_tarski(A,k1_relat_1(B))
          & v2_funct_1(B) )
       => k10_relat_1(B,k9_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).

tff(f_102,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_106,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

tff(c_60,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_14,plain,(
    ! [A_8,B_9] : v1_relat_1(k2_zfmisc_1(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_62,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_72,plain,(
    ! [B_46,A_47] :
      ( v1_relat_1(B_46)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(A_47))
      | ~ v1_relat_1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_75,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_62,c_72])).

tff(c_78,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_75])).

tff(c_68,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_64,plain,(
    v3_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_989,plain,(
    ! [C_183,A_184,B_185] :
      ( v2_funct_1(C_183)
      | ~ v3_funct_2(C_183,A_184,B_185)
      | ~ v1_funct_1(C_183)
      | ~ m1_subset_1(C_183,k1_zfmisc_1(k2_zfmisc_1(A_184,B_185))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_992,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_989])).

tff(c_995,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_992])).

tff(c_538,plain,(
    ! [C_120,B_121,A_122] :
      ( v5_relat_1(C_120,B_121)
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_zfmisc_1(A_122,B_121))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_542,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_538])).

tff(c_628,plain,(
    ! [B_138,A_139] :
      ( k2_relat_1(B_138) = A_139
      | ~ v2_funct_2(B_138,A_139)
      | ~ v5_relat_1(B_138,A_139)
      | ~ v1_relat_1(B_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_631,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_542,c_628])).

tff(c_634,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_631])).

tff(c_635,plain,(
    ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_634])).

tff(c_801,plain,(
    ! [C_163,B_164,A_165] :
      ( v2_funct_2(C_163,B_164)
      | ~ v3_funct_2(C_163,A_165,B_164)
      | ~ v1_funct_1(C_163)
      | ~ m1_subset_1(C_163,k1_zfmisc_1(k2_zfmisc_1(A_165,B_164))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_804,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_801])).

tff(c_807,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_804])).

tff(c_809,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_635,c_807])).

tff(c_810,plain,(
    k2_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_634])).

tff(c_18,plain,(
    ! [A_12] :
      ( k10_relat_1(A_12,k2_relat_1(A_12)) = k1_relat_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_819,plain,
    ( k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_810,c_18])).

tff(c_825,plain,(
    k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_819])).

tff(c_544,plain,(
    ! [C_125,A_126,B_127] :
      ( v4_relat_1(C_125,A_126)
      | ~ m1_subset_1(C_125,k1_zfmisc_1(k2_zfmisc_1(A_126,B_127))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_548,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_544])).

tff(c_20,plain,(
    ! [B_14,A_13] :
      ( k7_relat_1(B_14,A_13) = B_14
      | ~ v4_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_551,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_548,c_20])).

tff(c_554,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_551])).

tff(c_563,plain,(
    ! [B_128,A_129] :
      ( k2_relat_1(k7_relat_1(B_128,A_129)) = k9_relat_1(B_128,A_129)
      | ~ v1_relat_1(B_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_575,plain,
    ( k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_554,c_563])).

tff(c_579,plain,(
    k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_575])).

tff(c_812,plain,(
    k9_relat_1('#skF_3','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_810,c_579])).

tff(c_66,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_1343,plain,(
    ! [A_206,B_207] :
      ( k2_funct_2(A_206,B_207) = k2_funct_1(B_207)
      | ~ m1_subset_1(B_207,k1_zfmisc_1(k2_zfmisc_1(A_206,A_206)))
      | ~ v3_funct_2(B_207,A_206,A_206)
      | ~ v1_funct_2(B_207,A_206,A_206)
      | ~ v1_funct_1(B_207) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_1346,plain,
    ( k2_funct_2('#skF_1','#skF_3') = k2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_1343])).

tff(c_1349,plain,(
    k2_funct_2('#skF_1','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_1346])).

tff(c_1646,plain,(
    ! [A_218,B_219] :
      ( m1_subset_1(k2_funct_2(A_218,B_219),k1_zfmisc_1(k2_zfmisc_1(A_218,A_218)))
      | ~ m1_subset_1(B_219,k1_zfmisc_1(k2_zfmisc_1(A_218,A_218)))
      | ~ v3_funct_2(B_219,A_218,A_218)
      | ~ v1_funct_2(B_219,A_218,A_218)
      | ~ v1_funct_1(B_219) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_1678,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1349,c_1646])).

tff(c_1693,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_62,c_1678])).

tff(c_8,plain,(
    ! [B_5,A_3] :
      ( v1_relat_1(B_5)
      | ~ m1_subset_1(B_5,k1_zfmisc_1(A_3))
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1722,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_1693,c_8])).

tff(c_1747,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1722])).

tff(c_1238,plain,(
    ! [A_201,B_202] :
      ( v1_funct_1(k2_funct_2(A_201,B_202))
      | ~ m1_subset_1(B_202,k1_zfmisc_1(k2_zfmisc_1(A_201,A_201)))
      | ~ v3_funct_2(B_202,A_201,A_201)
      | ~ v1_funct_2(B_202,A_201,A_201)
      | ~ v1_funct_1(B_202) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_1241,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_1238])).

tff(c_1244,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_1241])).

tff(c_1350,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1349,c_1244])).

tff(c_1495,plain,(
    ! [A_209,B_210] :
      ( v3_funct_2(k2_funct_2(A_209,B_210),A_209,A_209)
      | ~ m1_subset_1(B_210,k1_zfmisc_1(k2_zfmisc_1(A_209,A_209)))
      | ~ v3_funct_2(B_210,A_209,A_209)
      | ~ v1_funct_2(B_210,A_209,A_209)
      | ~ v1_funct_1(B_210) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_1497,plain,
    ( v3_funct_2(k2_funct_2('#skF_1','#skF_3'),'#skF_1','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_1495])).

tff(c_1500,plain,(
    v3_funct_2(k2_funct_1('#skF_3'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_1349,c_1497])).

tff(c_38,plain,(
    ! [C_36,B_35,A_34] :
      ( v2_funct_2(C_36,B_35)
      | ~ v3_funct_2(C_36,A_34,B_35)
      | ~ v1_funct_1(C_36)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_1706,plain,
    ( v2_funct_2(k2_funct_1('#skF_3'),'#skF_1')
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1693,c_38])).

tff(c_1737,plain,(
    v2_funct_2(k2_funct_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1350,c_1500,c_1706])).

tff(c_30,plain,(
    ! [C_25,B_24,A_23] :
      ( v5_relat_1(C_25,B_24)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1744,plain,(
    v5_relat_1(k2_funct_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_1693,c_30])).

tff(c_46,plain,(
    ! [B_38,A_37] :
      ( k2_relat_1(B_38) = A_37
      | ~ v2_funct_2(B_38,A_37)
      | ~ v5_relat_1(B_38,A_37)
      | ~ v1_relat_1(B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_1756,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1'
    | ~ v2_funct_2(k2_funct_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1744,c_46])).

tff(c_1759,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1'
    | ~ v2_funct_2(k2_funct_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1747,c_1756])).

tff(c_1857,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1737,c_1759])).

tff(c_32,plain,(
    ! [C_25,A_23,B_24] :
      ( v4_relat_1(C_25,A_23)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1743,plain,(
    v4_relat_1(k2_funct_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_1693,c_32])).

tff(c_1750,plain,
    ( k7_relat_1(k2_funct_1('#skF_3'),'#skF_1') = k2_funct_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1743,c_20])).

tff(c_1753,plain,(
    k7_relat_1(k2_funct_1('#skF_3'),'#skF_1') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1747,c_1750])).

tff(c_16,plain,(
    ! [B_11,A_10] :
      ( k2_relat_1(k7_relat_1(B_11,A_10)) = k9_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1766,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),'#skF_1') = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1753,c_16])).

tff(c_1772,plain,(
    k9_relat_1(k2_funct_1('#skF_3'),'#skF_1') = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1747,c_1766])).

tff(c_1858,plain,(
    k9_relat_1(k2_funct_1('#skF_3'),'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1857,c_1772])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_588,plain,(
    ! [B_132,A_133] :
      ( v4_relat_1(B_132,A_133)
      | ~ r1_tarski(k1_relat_1(B_132),A_133)
      | ~ v1_relat_1(B_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_602,plain,(
    ! [B_135] :
      ( v4_relat_1(B_135,k1_relat_1(B_135))
      | ~ v1_relat_1(B_135) ) ),
    inference(resolution,[status(thm)],[c_6,c_588])).

tff(c_607,plain,(
    ! [B_136] :
      ( k7_relat_1(B_136,k1_relat_1(B_136)) = B_136
      | ~ v1_relat_1(B_136) ) ),
    inference(resolution,[status(thm)],[c_602,c_20])).

tff(c_613,plain,(
    ! [B_136] :
      ( k9_relat_1(B_136,k1_relat_1(B_136)) = k2_relat_1(B_136)
      | ~ v1_relat_1(B_136)
      | ~ v1_relat_1(B_136) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_607,c_16])).

tff(c_22,plain,(
    ! [B_16,A_15] :
      ( r1_tarski(k9_relat_1(B_16,k10_relat_1(B_16,A_15)),A_15)
      | ~ v1_funct_1(B_16)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_842,plain,
    ( r1_tarski(k9_relat_1('#skF_3',k1_relat_1('#skF_3')),'#skF_1')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_825,c_22])).

tff(c_846,plain,(
    r1_tarski(k9_relat_1('#skF_3',k1_relat_1('#skF_3')),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_68,c_842])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_853,plain,
    ( k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_1'
    | ~ r1_tarski('#skF_1',k9_relat_1('#skF_3',k1_relat_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_846,c_2])).

tff(c_856,plain,(
    ~ r1_tarski('#skF_1',k9_relat_1('#skF_3',k1_relat_1('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_853])).

tff(c_859,plain,
    ( ~ r1_tarski('#skF_1',k2_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_613,c_856])).

tff(c_862,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_78,c_6,c_810,c_859])).

tff(c_863,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_853])).

tff(c_899,plain,(
    ! [B_170,A_171] :
      ( k10_relat_1(k2_funct_1(B_170),A_171) = k9_relat_1(B_170,A_171)
      | ~ v2_funct_1(B_170)
      | ~ v1_funct_1(B_170)
      | ~ v1_relat_1(B_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1964,plain,(
    ! [B_223,A_224] :
      ( r1_tarski(k9_relat_1(k2_funct_1(B_223),k9_relat_1(B_223,A_224)),A_224)
      | ~ v1_funct_1(k2_funct_1(B_223))
      | ~ v1_relat_1(k2_funct_1(B_223))
      | ~ v2_funct_1(B_223)
      | ~ v1_funct_1(B_223)
      | ~ v1_relat_1(B_223) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_899,c_22])).

tff(c_2007,plain,
    ( r1_tarski(k9_relat_1(k2_funct_1('#skF_3'),'#skF_1'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_863,c_1964])).

tff(c_2026,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_68,c_995,c_1747,c_1350,c_1858,c_2007])).

tff(c_28,plain,(
    ! [B_22,A_21] :
      ( k10_relat_1(B_22,k9_relat_1(B_22,A_21)) = A_21
      | ~ v2_funct_1(B_22)
      | ~ r1_tarski(A_21,k1_relat_1(B_22))
      | ~ v1_funct_1(B_22)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_2033,plain,
    ( k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')) = '#skF_1'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2026,c_28])).

tff(c_2044,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_68,c_995,c_825,c_812,c_2033])).

tff(c_2076,plain,(
    ! [A_21] :
      ( k10_relat_1('#skF_3',k9_relat_1('#skF_3',A_21)) = A_21
      | ~ v2_funct_1('#skF_3')
      | ~ r1_tarski(A_21,'#skF_1')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2044,c_28])).

tff(c_3625,plain,(
    ! [A_258] :
      ( k10_relat_1('#skF_3',k9_relat_1('#skF_3',A_258)) = A_258
      | ~ r1_tarski(A_258,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_68,c_995,c_2076])).

tff(c_959,plain,(
    ! [A_178,B_179,C_180,D_181] :
      ( k7_relset_1(A_178,B_179,C_180,D_181) = k9_relat_1(C_180,D_181)
      | ~ m1_subset_1(C_180,k1_zfmisc_1(k2_zfmisc_1(A_178,B_179))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_962,plain,(
    ! [D_181] : k7_relset_1('#skF_1','#skF_1','#skF_3',D_181) = k9_relat_1('#skF_3',D_181) ),
    inference(resolution,[status(thm)],[c_62,c_959])).

tff(c_940,plain,(
    ! [A_173,B_174,C_175,D_176] :
      ( k8_relset_1(A_173,B_174,C_175,D_176) = k10_relat_1(C_175,D_176)
      | ~ m1_subset_1(C_175,k1_zfmisc_1(k2_zfmisc_1(A_173,B_174))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_943,plain,(
    ! [D_176] : k8_relset_1('#skF_1','#skF_1','#skF_3',D_176) = k10_relat_1('#skF_3',D_176) ),
    inference(resolution,[status(thm)],[c_62,c_940])).

tff(c_100,plain,(
    ! [C_51,B_52,A_53] :
      ( v5_relat_1(C_51,B_52)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_53,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_104,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_100])).

tff(c_193,plain,(
    ! [B_71,A_72] :
      ( k2_relat_1(B_71) = A_72
      | ~ v2_funct_2(B_71,A_72)
      | ~ v5_relat_1(B_71,A_72)
      | ~ v1_relat_1(B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_196,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_104,c_193])).

tff(c_199,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_196])).

tff(c_200,plain,(
    ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_199])).

tff(c_302,plain,(
    ! [C_93,B_94,A_95] :
      ( v2_funct_2(C_93,B_94)
      | ~ v3_funct_2(C_93,A_95,B_94)
      | ~ v1_funct_1(C_93)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_95,B_94))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_305,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_302])).

tff(c_308,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_305])).

tff(c_310,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_200,c_308])).

tff(c_311,plain,(
    k2_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_199])).

tff(c_455,plain,(
    ! [B_109,A_110] :
      ( k9_relat_1(B_109,k10_relat_1(B_109,A_110)) = A_110
      | ~ r1_tarski(A_110,k2_relat_1(B_109))
      | ~ v1_funct_1(B_109)
      | ~ v1_relat_1(B_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_459,plain,(
    ! [A_110] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_110)) = A_110
      | ~ r1_tarski(A_110,'#skF_1')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_311,c_455])).

tff(c_491,plain,(
    ! [A_116] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_116)) = A_116
      | ~ r1_tarski(A_116,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_68,c_459])).

tff(c_477,plain,(
    ! [A_111,B_112,C_113,D_114] :
      ( k7_relset_1(A_111,B_112,C_113,D_114) = k9_relat_1(C_113,D_114)
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k2_zfmisc_1(A_111,B_112))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_480,plain,(
    ! [D_114] : k7_relset_1('#skF_1','#skF_1','#skF_3',D_114) = k9_relat_1('#skF_3',D_114) ),
    inference(resolution,[status(thm)],[c_62,c_477])).

tff(c_434,plain,(
    ! [A_101,B_102,C_103,D_104] :
      ( k8_relset_1(A_101,B_102,C_103,D_104) = k10_relat_1(C_103,D_104)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1(A_101,B_102))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_437,plain,(
    ! [D_104] : k8_relset_1('#skF_1','#skF_1','#skF_3',D_104) = k10_relat_1('#skF_3',D_104) ),
    inference(resolution,[status(thm)],[c_62,c_434])).

tff(c_58,plain,
    ( k8_relset_1('#skF_1','#skF_1','#skF_3',k7_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2'
    | k7_relset_1('#skF_1','#skF_1','#skF_3',k8_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_79,plain,(
    k7_relset_1('#skF_1','#skF_1','#skF_3',k8_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_438,plain,(
    k7_relset_1('#skF_1','#skF_1','#skF_3',k10_relat_1('#skF_3','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_437,c_79])).

tff(c_481,plain,(
    k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_480,c_438])).

tff(c_497,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_491,c_481])).

tff(c_515,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_497])).

tff(c_516,plain,(
    k8_relset_1('#skF_1','#skF_1','#skF_3',k7_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_945,plain,(
    k10_relat_1('#skF_3',k7_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_943,c_516])).

tff(c_963,plain,(
    k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_962,c_945])).

tff(c_3666,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3625,c_963])).

tff(c_3744,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_3666])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:11:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.69/2.90  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.08/2.92  
% 8.08/2.92  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.08/2.93  %$ v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_funct_2 > k10_relat_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 8.08/2.93  
% 8.08/2.93  %Foreground sorts:
% 8.08/2.93  
% 8.08/2.93  
% 8.08/2.93  %Background operators:
% 8.08/2.93  
% 8.08/2.93  
% 8.08/2.93  %Foreground operators:
% 8.08/2.93  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.08/2.93  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 8.08/2.93  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 8.08/2.93  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.08/2.93  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 8.08/2.93  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 8.08/2.93  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 8.08/2.93  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.08/2.93  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.08/2.93  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 8.08/2.93  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.08/2.93  tff('#skF_2', type, '#skF_2': $i).
% 8.08/2.93  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 8.08/2.93  tff('#skF_3', type, '#skF_3': $i).
% 8.08/2.93  tff('#skF_1', type, '#skF_1': $i).
% 8.08/2.93  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 8.08/2.93  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 8.08/2.93  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.08/2.93  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.08/2.93  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 8.08/2.93  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.08/2.93  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.08/2.93  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.08/2.93  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 8.08/2.93  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 8.08/2.93  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.08/2.93  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.08/2.93  
% 8.08/2.97  tff(f_167, negated_conjecture, ~(![A, B, C]: ((((v1_funct_1(C) & v1_funct_2(C, A, A)) & v3_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r1_tarski(B, A) => ((k7_relset_1(A, A, C, k8_relset_1(A, A, C, B)) = B) & (k8_relset_1(A, A, C, k7_relset_1(A, A, C, B)) = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_funct_2)).
% 8.08/2.97  tff(f_46, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 8.08/2.97  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 8.08/2.97  tff(f_118, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_2)).
% 8.08/2.97  tff(f_98, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 8.08/2.97  tff(f_126, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 8.08/2.97  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 8.08/2.97  tff(f_60, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 8.08/2.97  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 8.08/2.97  tff(f_152, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 8.08/2.97  tff(f_142, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 8.08/2.97  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.08/2.97  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 8.08/2.97  tff(f_66, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_funct_1)).
% 8.08/2.97  tff(f_82, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k9_relat_1(B, A) = k10_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t154_funct_1)).
% 8.08/2.97  tff(f_92, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((r1_tarski(A, k1_relat_1(B)) & v2_funct_1(B)) => (k10_relat_1(B, k9_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t164_funct_1)).
% 8.08/2.97  tff(f_102, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 8.08/2.97  tff(f_106, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 8.08/2.97  tff(f_74, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_funct_1)).
% 8.08/2.97  tff(c_60, plain, (r1_tarski('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_167])).
% 8.08/2.97  tff(c_14, plain, (![A_8, B_9]: (v1_relat_1(k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 8.08/2.97  tff(c_62, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_167])).
% 8.08/2.97  tff(c_72, plain, (![B_46, A_47]: (v1_relat_1(B_46) | ~m1_subset_1(B_46, k1_zfmisc_1(A_47)) | ~v1_relat_1(A_47))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.08/2.97  tff(c_75, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_62, c_72])).
% 8.08/2.97  tff(c_78, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_75])).
% 8.08/2.97  tff(c_68, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_167])).
% 8.08/2.97  tff(c_64, plain, (v3_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_167])).
% 8.08/2.97  tff(c_989, plain, (![C_183, A_184, B_185]: (v2_funct_1(C_183) | ~v3_funct_2(C_183, A_184, B_185) | ~v1_funct_1(C_183) | ~m1_subset_1(C_183, k1_zfmisc_1(k2_zfmisc_1(A_184, B_185))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 8.08/2.97  tff(c_992, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_62, c_989])).
% 8.08/2.97  tff(c_995, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_992])).
% 8.08/2.97  tff(c_538, plain, (![C_120, B_121, A_122]: (v5_relat_1(C_120, B_121) | ~m1_subset_1(C_120, k1_zfmisc_1(k2_zfmisc_1(A_122, B_121))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 8.08/2.97  tff(c_542, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_62, c_538])).
% 8.08/2.97  tff(c_628, plain, (![B_138, A_139]: (k2_relat_1(B_138)=A_139 | ~v2_funct_2(B_138, A_139) | ~v5_relat_1(B_138, A_139) | ~v1_relat_1(B_138))), inference(cnfTransformation, [status(thm)], [f_126])).
% 8.08/2.97  tff(c_631, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_542, c_628])).
% 8.08/2.97  tff(c_634, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_631])).
% 8.08/2.97  tff(c_635, plain, (~v2_funct_2('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_634])).
% 8.08/2.97  tff(c_801, plain, (![C_163, B_164, A_165]: (v2_funct_2(C_163, B_164) | ~v3_funct_2(C_163, A_165, B_164) | ~v1_funct_1(C_163) | ~m1_subset_1(C_163, k1_zfmisc_1(k2_zfmisc_1(A_165, B_164))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 8.08/2.97  tff(c_804, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_62, c_801])).
% 8.08/2.97  tff(c_807, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_804])).
% 8.08/2.97  tff(c_809, plain, $false, inference(negUnitSimplification, [status(thm)], [c_635, c_807])).
% 8.08/2.97  tff(c_810, plain, (k2_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_634])).
% 8.08/2.97  tff(c_18, plain, (![A_12]: (k10_relat_1(A_12, k2_relat_1(A_12))=k1_relat_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_54])).
% 8.08/2.97  tff(c_819, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_810, c_18])).
% 8.08/2.97  tff(c_825, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_819])).
% 8.08/2.97  tff(c_544, plain, (![C_125, A_126, B_127]: (v4_relat_1(C_125, A_126) | ~m1_subset_1(C_125, k1_zfmisc_1(k2_zfmisc_1(A_126, B_127))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 8.08/2.97  tff(c_548, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_62, c_544])).
% 8.08/2.97  tff(c_20, plain, (![B_14, A_13]: (k7_relat_1(B_14, A_13)=B_14 | ~v4_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.08/2.97  tff(c_551, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_548, c_20])).
% 8.08/2.97  tff(c_554, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_551])).
% 8.08/2.97  tff(c_563, plain, (![B_128, A_129]: (k2_relat_1(k7_relat_1(B_128, A_129))=k9_relat_1(B_128, A_129) | ~v1_relat_1(B_128))), inference(cnfTransformation, [status(thm)], [f_50])).
% 8.08/2.97  tff(c_575, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_554, c_563])).
% 8.08/2.97  tff(c_579, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_575])).
% 8.08/2.97  tff(c_812, plain, (k9_relat_1('#skF_3', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_810, c_579])).
% 8.08/2.97  tff(c_66, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_167])).
% 8.08/2.97  tff(c_1343, plain, (![A_206, B_207]: (k2_funct_2(A_206, B_207)=k2_funct_1(B_207) | ~m1_subset_1(B_207, k1_zfmisc_1(k2_zfmisc_1(A_206, A_206))) | ~v3_funct_2(B_207, A_206, A_206) | ~v1_funct_2(B_207, A_206, A_206) | ~v1_funct_1(B_207))), inference(cnfTransformation, [status(thm)], [f_152])).
% 8.08/2.97  tff(c_1346, plain, (k2_funct_2('#skF_1', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_62, c_1343])).
% 8.08/2.97  tff(c_1349, plain, (k2_funct_2('#skF_1', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_1346])).
% 8.08/2.97  tff(c_1646, plain, (![A_218, B_219]: (m1_subset_1(k2_funct_2(A_218, B_219), k1_zfmisc_1(k2_zfmisc_1(A_218, A_218))) | ~m1_subset_1(B_219, k1_zfmisc_1(k2_zfmisc_1(A_218, A_218))) | ~v3_funct_2(B_219, A_218, A_218) | ~v1_funct_2(B_219, A_218, A_218) | ~v1_funct_1(B_219))), inference(cnfTransformation, [status(thm)], [f_142])).
% 8.08/2.97  tff(c_1678, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1349, c_1646])).
% 8.08/2.97  tff(c_1693, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_62, c_1678])).
% 8.08/2.97  tff(c_8, plain, (![B_5, A_3]: (v1_relat_1(B_5) | ~m1_subset_1(B_5, k1_zfmisc_1(A_3)) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.08/2.97  tff(c_1722, plain, (v1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_1693, c_8])).
% 8.08/2.97  tff(c_1747, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1722])).
% 8.08/2.97  tff(c_1238, plain, (![A_201, B_202]: (v1_funct_1(k2_funct_2(A_201, B_202)) | ~m1_subset_1(B_202, k1_zfmisc_1(k2_zfmisc_1(A_201, A_201))) | ~v3_funct_2(B_202, A_201, A_201) | ~v1_funct_2(B_202, A_201, A_201) | ~v1_funct_1(B_202))), inference(cnfTransformation, [status(thm)], [f_142])).
% 8.08/2.97  tff(c_1241, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_62, c_1238])).
% 8.08/2.97  tff(c_1244, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_1241])).
% 8.08/2.97  tff(c_1350, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1349, c_1244])).
% 8.08/2.97  tff(c_1495, plain, (![A_209, B_210]: (v3_funct_2(k2_funct_2(A_209, B_210), A_209, A_209) | ~m1_subset_1(B_210, k1_zfmisc_1(k2_zfmisc_1(A_209, A_209))) | ~v3_funct_2(B_210, A_209, A_209) | ~v1_funct_2(B_210, A_209, A_209) | ~v1_funct_1(B_210))), inference(cnfTransformation, [status(thm)], [f_142])).
% 8.08/2.97  tff(c_1497, plain, (v3_funct_2(k2_funct_2('#skF_1', '#skF_3'), '#skF_1', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_62, c_1495])).
% 8.08/2.97  tff(c_1500, plain, (v3_funct_2(k2_funct_1('#skF_3'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_1349, c_1497])).
% 8.08/2.97  tff(c_38, plain, (![C_36, B_35, A_34]: (v2_funct_2(C_36, B_35) | ~v3_funct_2(C_36, A_34, B_35) | ~v1_funct_1(C_36) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 8.08/2.97  tff(c_1706, plain, (v2_funct_2(k2_funct_1('#skF_3'), '#skF_1') | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_1693, c_38])).
% 8.08/2.97  tff(c_1737, plain, (v2_funct_2(k2_funct_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1350, c_1500, c_1706])).
% 8.08/2.97  tff(c_30, plain, (![C_25, B_24, A_23]: (v5_relat_1(C_25, B_24) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 8.08/2.97  tff(c_1744, plain, (v5_relat_1(k2_funct_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_1693, c_30])).
% 8.08/2.97  tff(c_46, plain, (![B_38, A_37]: (k2_relat_1(B_38)=A_37 | ~v2_funct_2(B_38, A_37) | ~v5_relat_1(B_38, A_37) | ~v1_relat_1(B_38))), inference(cnfTransformation, [status(thm)], [f_126])).
% 8.08/2.97  tff(c_1756, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1' | ~v2_funct_2(k2_funct_1('#skF_3'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_1744, c_46])).
% 8.08/2.97  tff(c_1759, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1' | ~v2_funct_2(k2_funct_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1747, c_1756])).
% 8.08/2.97  tff(c_1857, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1737, c_1759])).
% 8.08/2.97  tff(c_32, plain, (![C_25, A_23, B_24]: (v4_relat_1(C_25, A_23) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 8.08/2.97  tff(c_1743, plain, (v4_relat_1(k2_funct_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_1693, c_32])).
% 8.08/2.97  tff(c_1750, plain, (k7_relat_1(k2_funct_1('#skF_3'), '#skF_1')=k2_funct_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_1743, c_20])).
% 8.08/2.97  tff(c_1753, plain, (k7_relat_1(k2_funct_1('#skF_3'), '#skF_1')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1747, c_1750])).
% 8.08/2.97  tff(c_16, plain, (![B_11, A_10]: (k2_relat_1(k7_relat_1(B_11, A_10))=k9_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_50])).
% 8.08/2.97  tff(c_1766, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_1')=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1753, c_16])).
% 8.08/2.97  tff(c_1772, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_1')=k2_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1747, c_1766])).
% 8.08/2.97  tff(c_1858, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1857, c_1772])).
% 8.08/2.97  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.08/2.97  tff(c_588, plain, (![B_132, A_133]: (v4_relat_1(B_132, A_133) | ~r1_tarski(k1_relat_1(B_132), A_133) | ~v1_relat_1(B_132))), inference(cnfTransformation, [status(thm)], [f_44])).
% 8.08/2.97  tff(c_602, plain, (![B_135]: (v4_relat_1(B_135, k1_relat_1(B_135)) | ~v1_relat_1(B_135))), inference(resolution, [status(thm)], [c_6, c_588])).
% 8.08/2.97  tff(c_607, plain, (![B_136]: (k7_relat_1(B_136, k1_relat_1(B_136))=B_136 | ~v1_relat_1(B_136))), inference(resolution, [status(thm)], [c_602, c_20])).
% 8.08/2.97  tff(c_613, plain, (![B_136]: (k9_relat_1(B_136, k1_relat_1(B_136))=k2_relat_1(B_136) | ~v1_relat_1(B_136) | ~v1_relat_1(B_136))), inference(superposition, [status(thm), theory('equality')], [c_607, c_16])).
% 8.08/2.97  tff(c_22, plain, (![B_16, A_15]: (r1_tarski(k9_relat_1(B_16, k10_relat_1(B_16, A_15)), A_15) | ~v1_funct_1(B_16) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_66])).
% 8.08/2.97  tff(c_842, plain, (r1_tarski(k9_relat_1('#skF_3', k1_relat_1('#skF_3')), '#skF_1') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_825, c_22])).
% 8.08/2.97  tff(c_846, plain, (r1_tarski(k9_relat_1('#skF_3', k1_relat_1('#skF_3')), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_68, c_842])).
% 8.08/2.97  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.08/2.97  tff(c_853, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_1' | ~r1_tarski('#skF_1', k9_relat_1('#skF_3', k1_relat_1('#skF_3')))), inference(resolution, [status(thm)], [c_846, c_2])).
% 8.08/2.97  tff(c_856, plain, (~r1_tarski('#skF_1', k9_relat_1('#skF_3', k1_relat_1('#skF_3')))), inference(splitLeft, [status(thm)], [c_853])).
% 8.08/2.97  tff(c_859, plain, (~r1_tarski('#skF_1', k2_relat_1('#skF_3')) | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_613, c_856])).
% 8.08/2.97  tff(c_862, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_78, c_6, c_810, c_859])).
% 8.08/2.97  tff(c_863, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_1'), inference(splitRight, [status(thm)], [c_853])).
% 8.08/2.97  tff(c_899, plain, (![B_170, A_171]: (k10_relat_1(k2_funct_1(B_170), A_171)=k9_relat_1(B_170, A_171) | ~v2_funct_1(B_170) | ~v1_funct_1(B_170) | ~v1_relat_1(B_170))), inference(cnfTransformation, [status(thm)], [f_82])).
% 8.08/2.97  tff(c_1964, plain, (![B_223, A_224]: (r1_tarski(k9_relat_1(k2_funct_1(B_223), k9_relat_1(B_223, A_224)), A_224) | ~v1_funct_1(k2_funct_1(B_223)) | ~v1_relat_1(k2_funct_1(B_223)) | ~v2_funct_1(B_223) | ~v1_funct_1(B_223) | ~v1_relat_1(B_223))), inference(superposition, [status(thm), theory('equality')], [c_899, c_22])).
% 8.08/2.97  tff(c_2007, plain, (r1_tarski(k9_relat_1(k2_funct_1('#skF_3'), '#skF_1'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_863, c_1964])).
% 8.08/2.97  tff(c_2026, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_68, c_995, c_1747, c_1350, c_1858, c_2007])).
% 8.08/2.97  tff(c_28, plain, (![B_22, A_21]: (k10_relat_1(B_22, k9_relat_1(B_22, A_21))=A_21 | ~v2_funct_1(B_22) | ~r1_tarski(A_21, k1_relat_1(B_22)) | ~v1_funct_1(B_22) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_92])).
% 8.08/2.97  tff(c_2033, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1'))='#skF_1' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2026, c_28])).
% 8.08/2.97  tff(c_2044, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_68, c_995, c_825, c_812, c_2033])).
% 8.08/2.97  tff(c_2076, plain, (![A_21]: (k10_relat_1('#skF_3', k9_relat_1('#skF_3', A_21))=A_21 | ~v2_funct_1('#skF_3') | ~r1_tarski(A_21, '#skF_1') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2044, c_28])).
% 8.08/2.97  tff(c_3625, plain, (![A_258]: (k10_relat_1('#skF_3', k9_relat_1('#skF_3', A_258))=A_258 | ~r1_tarski(A_258, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_68, c_995, c_2076])).
% 8.08/2.97  tff(c_959, plain, (![A_178, B_179, C_180, D_181]: (k7_relset_1(A_178, B_179, C_180, D_181)=k9_relat_1(C_180, D_181) | ~m1_subset_1(C_180, k1_zfmisc_1(k2_zfmisc_1(A_178, B_179))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 8.08/2.97  tff(c_962, plain, (![D_181]: (k7_relset_1('#skF_1', '#skF_1', '#skF_3', D_181)=k9_relat_1('#skF_3', D_181))), inference(resolution, [status(thm)], [c_62, c_959])).
% 8.08/2.97  tff(c_940, plain, (![A_173, B_174, C_175, D_176]: (k8_relset_1(A_173, B_174, C_175, D_176)=k10_relat_1(C_175, D_176) | ~m1_subset_1(C_175, k1_zfmisc_1(k2_zfmisc_1(A_173, B_174))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 8.08/2.97  tff(c_943, plain, (![D_176]: (k8_relset_1('#skF_1', '#skF_1', '#skF_3', D_176)=k10_relat_1('#skF_3', D_176))), inference(resolution, [status(thm)], [c_62, c_940])).
% 8.08/2.97  tff(c_100, plain, (![C_51, B_52, A_53]: (v5_relat_1(C_51, B_52) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_53, B_52))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 8.08/2.97  tff(c_104, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_62, c_100])).
% 8.08/2.97  tff(c_193, plain, (![B_71, A_72]: (k2_relat_1(B_71)=A_72 | ~v2_funct_2(B_71, A_72) | ~v5_relat_1(B_71, A_72) | ~v1_relat_1(B_71))), inference(cnfTransformation, [status(thm)], [f_126])).
% 8.08/2.97  tff(c_196, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_104, c_193])).
% 8.08/2.97  tff(c_199, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_196])).
% 8.08/2.97  tff(c_200, plain, (~v2_funct_2('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_199])).
% 8.08/2.97  tff(c_302, plain, (![C_93, B_94, A_95]: (v2_funct_2(C_93, B_94) | ~v3_funct_2(C_93, A_95, B_94) | ~v1_funct_1(C_93) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_95, B_94))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 8.08/2.97  tff(c_305, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_62, c_302])).
% 8.08/2.97  tff(c_308, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_305])).
% 8.08/2.97  tff(c_310, plain, $false, inference(negUnitSimplification, [status(thm)], [c_200, c_308])).
% 8.08/2.97  tff(c_311, plain, (k2_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_199])).
% 8.08/2.97  tff(c_455, plain, (![B_109, A_110]: (k9_relat_1(B_109, k10_relat_1(B_109, A_110))=A_110 | ~r1_tarski(A_110, k2_relat_1(B_109)) | ~v1_funct_1(B_109) | ~v1_relat_1(B_109))), inference(cnfTransformation, [status(thm)], [f_74])).
% 8.08/2.97  tff(c_459, plain, (![A_110]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_110))=A_110 | ~r1_tarski(A_110, '#skF_1') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_311, c_455])).
% 8.08/2.97  tff(c_491, plain, (![A_116]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_116))=A_116 | ~r1_tarski(A_116, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_68, c_459])).
% 8.08/2.97  tff(c_477, plain, (![A_111, B_112, C_113, D_114]: (k7_relset_1(A_111, B_112, C_113, D_114)=k9_relat_1(C_113, D_114) | ~m1_subset_1(C_113, k1_zfmisc_1(k2_zfmisc_1(A_111, B_112))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 8.08/2.97  tff(c_480, plain, (![D_114]: (k7_relset_1('#skF_1', '#skF_1', '#skF_3', D_114)=k9_relat_1('#skF_3', D_114))), inference(resolution, [status(thm)], [c_62, c_477])).
% 8.08/2.97  tff(c_434, plain, (![A_101, B_102, C_103, D_104]: (k8_relset_1(A_101, B_102, C_103, D_104)=k10_relat_1(C_103, D_104) | ~m1_subset_1(C_103, k1_zfmisc_1(k2_zfmisc_1(A_101, B_102))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 8.08/2.97  tff(c_437, plain, (![D_104]: (k8_relset_1('#skF_1', '#skF_1', '#skF_3', D_104)=k10_relat_1('#skF_3', D_104))), inference(resolution, [status(thm)], [c_62, c_434])).
% 8.08/2.97  tff(c_58, plain, (k8_relset_1('#skF_1', '#skF_1', '#skF_3', k7_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2' | k7_relset_1('#skF_1', '#skF_1', '#skF_3', k8_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_167])).
% 8.08/2.97  tff(c_79, plain, (k7_relset_1('#skF_1', '#skF_1', '#skF_3', k8_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_58])).
% 8.08/2.97  tff(c_438, plain, (k7_relset_1('#skF_1', '#skF_1', '#skF_3', k10_relat_1('#skF_3', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_437, c_79])).
% 8.08/2.97  tff(c_481, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_480, c_438])).
% 8.08/2.97  tff(c_497, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_491, c_481])).
% 8.08/2.97  tff(c_515, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_497])).
% 8.08/2.97  tff(c_516, plain, (k8_relset_1('#skF_1', '#skF_1', '#skF_3', k7_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2'), inference(splitRight, [status(thm)], [c_58])).
% 8.08/2.97  tff(c_945, plain, (k10_relat_1('#skF_3', k7_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_943, c_516])).
% 8.08/2.97  tff(c_963, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_962, c_945])).
% 8.08/2.97  tff(c_3666, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3625, c_963])).
% 8.08/2.97  tff(c_3744, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_3666])).
% 8.08/2.97  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.08/2.97  
% 8.08/2.97  Inference rules
% 8.08/2.97  ----------------------
% 8.08/2.97  #Ref     : 0
% 8.08/2.97  #Sup     : 784
% 8.08/2.97  #Fact    : 0
% 8.08/2.97  #Define  : 0
% 8.08/2.97  #Split   : 10
% 8.08/2.97  #Chain   : 0
% 8.08/2.97  #Close   : 0
% 8.08/2.97  
% 8.08/2.97  Ordering : KBO
% 8.08/2.97  
% 8.08/2.97  Simplification rules
% 8.08/2.97  ----------------------
% 8.08/2.97  #Subsume      : 40
% 8.08/2.97  #Demod        : 1419
% 8.08/2.97  #Tautology    : 395
% 8.08/2.97  #SimpNegUnit  : 2
% 8.08/2.97  #BackRed      : 37
% 8.08/2.97  
% 8.08/2.97  #Partial instantiations: 0
% 8.08/2.97  #Strategies tried      : 1
% 8.08/2.97  
% 8.08/2.97  Timing (in seconds)
% 8.08/2.97  ----------------------
% 8.08/2.97  Preprocessing        : 0.58
% 8.08/2.97  Parsing              : 0.30
% 8.08/2.97  CNF conversion       : 0.04
% 8.08/2.97  Main loop            : 1.51
% 8.08/2.98  Inferencing          : 0.52
% 8.08/2.98  Reduction            : 0.55
% 8.08/2.98  Demodulation         : 0.42
% 8.08/2.98  BG Simplification    : 0.07
% 8.08/2.98  Subsumption          : 0.25
% 8.08/2.98  Abstraction          : 0.07
% 8.08/2.98  MUC search           : 0.00
% 8.08/2.98  Cooper               : 0.00
% 8.08/2.98  Total                : 2.18
% 8.08/2.98  Index Insertion      : 0.00
% 8.08/2.98  Index Deletion       : 0.00
% 8.08/2.98  Index Matching       : 0.00
% 8.08/2.98  BG Taut test         : 0.00
%------------------------------------------------------------------------------
