%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:15 EST 2020

% Result     : Theorem 4.87s
% Output     : CNFRefutation 5.21s
% Verified   : 
% Statistics : Number of formulae       :  174 (1178 expanded)
%              Number of leaves         :   44 ( 430 expanded)
%              Depth                    :   19
%              Number of atoms          :  341 (3332 expanded)
%              Number of equality atoms :   79 ( 684 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

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

tff(f_158,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,A)
          & v3_funct_2(C,A,A)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( r1_tarski(B,A)
         => ( k7_relset_1(A,A,C,k8_relset_1(A,A,C,B)) = B
            & k8_relset_1(A,A,C,k7_relset_1(A,A,C,B)) = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_funct_2)).

tff(f_40,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_109,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_143,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_133,axiom,(
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

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_117,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_83,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v2_funct_1(A)
            & r1_tarski(B,k1_relat_1(A)) )
         => k9_relat_1(k2_funct_1(A),k9_relat_1(A,B)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t177_funct_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( ( r1_tarski(A,k1_relat_1(B))
          & v2_funct_1(B) )
       => k10_relat_1(B,k9_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).

tff(f_93,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_97,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(c_54,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_10,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_56,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_324,plain,(
    ! [B_94,A_95] :
      ( v1_relat_1(B_94)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(A_95))
      | ~ v1_relat_1(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_327,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_56,c_324])).

tff(c_330,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_327])).

tff(c_62,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_58,plain,(
    v3_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_649,plain,(
    ! [C_144,A_145,B_146] :
      ( v2_funct_1(C_144)
      | ~ v3_funct_2(C_144,A_145,B_146)
      | ~ v1_funct_1(C_144)
      | ~ m1_subset_1(C_144,k1_zfmisc_1(k2_zfmisc_1(A_145,B_146))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_652,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_649])).

tff(c_655,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_652])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_60,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_1904,plain,(
    ! [A_214,B_215] :
      ( k2_funct_2(A_214,B_215) = k2_funct_1(B_215)
      | ~ m1_subset_1(B_215,k1_zfmisc_1(k2_zfmisc_1(A_214,A_214)))
      | ~ v3_funct_2(B_215,A_214,A_214)
      | ~ v1_funct_2(B_215,A_214,A_214)
      | ~ v1_funct_1(B_215) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_1907,plain,
    ( k2_funct_2('#skF_1','#skF_3') = k2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_1904])).

tff(c_1910,plain,(
    k2_funct_2('#skF_1','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_1907])).

tff(c_721,plain,(
    ! [A_154,B_155] :
      ( v1_funct_1(k2_funct_2(A_154,B_155))
      | ~ m1_subset_1(B_155,k1_zfmisc_1(k2_zfmisc_1(A_154,A_154)))
      | ~ v3_funct_2(B_155,A_154,A_154)
      | ~ v1_funct_2(B_155,A_154,A_154)
      | ~ v1_funct_1(B_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_724,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_721])).

tff(c_727,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_724])).

tff(c_1911,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1910,c_727])).

tff(c_2457,plain,(
    ! [A_242,B_243] :
      ( v3_funct_2(k2_funct_2(A_242,B_243),A_242,A_242)
      | ~ m1_subset_1(B_243,k1_zfmisc_1(k2_zfmisc_1(A_242,A_242)))
      | ~ v3_funct_2(B_243,A_242,A_242)
      | ~ v1_funct_2(B_243,A_242,A_242)
      | ~ v1_funct_1(B_243) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_2459,plain,
    ( v3_funct_2(k2_funct_2('#skF_1','#skF_3'),'#skF_1','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_2457])).

tff(c_2462,plain,(
    v3_funct_2(k2_funct_1('#skF_3'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_1910,c_2459])).

tff(c_2877,plain,(
    ! [A_255,B_256] :
      ( m1_subset_1(k2_funct_2(A_255,B_256),k1_zfmisc_1(k2_zfmisc_1(A_255,A_255)))
      | ~ m1_subset_1(B_256,k1_zfmisc_1(k2_zfmisc_1(A_255,A_255)))
      | ~ v3_funct_2(B_256,A_255,A_255)
      | ~ v1_funct_2(B_256,A_255,A_255)
      | ~ v1_funct_1(B_256) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_2909,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1910,c_2877])).

tff(c_2924,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_56,c_2909])).

tff(c_32,plain,(
    ! [C_33,B_32,A_31] :
      ( v2_funct_2(C_33,B_32)
      | ~ v3_funct_2(C_33,A_31,B_32)
      | ~ v1_funct_1(C_33)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_2986,plain,
    ( v2_funct_2(k2_funct_1('#skF_3'),'#skF_1')
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2924,c_32])).

tff(c_3017,plain,(
    v2_funct_2(k2_funct_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1911,c_2462,c_2986])).

tff(c_344,plain,(
    ! [C_100,B_101,A_102] :
      ( v5_relat_1(C_100,B_101)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(A_102,B_101))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_348,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_344])).

tff(c_381,plain,(
    ! [B_107,A_108] :
      ( k2_relat_1(B_107) = A_108
      | ~ v2_funct_2(B_107,A_108)
      | ~ v5_relat_1(B_107,A_108)
      | ~ v1_relat_1(B_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_384,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_348,c_381])).

tff(c_387,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_330,c_384])).

tff(c_388,plain,(
    ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_387])).

tff(c_471,plain,(
    ! [C_126,B_127,A_128] :
      ( v2_funct_2(C_126,B_127)
      | ~ v3_funct_2(C_126,A_128,B_127)
      | ~ v1_funct_1(C_126)
      | ~ m1_subset_1(C_126,k1_zfmisc_1(k2_zfmisc_1(A_128,B_127))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_474,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_471])).

tff(c_477,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_474])).

tff(c_479,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_388,c_477])).

tff(c_480,plain,(
    k2_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_387])).

tff(c_14,plain,(
    ! [A_10] :
      ( k10_relat_1(A_10,k2_relat_1(A_10)) = k1_relat_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_493,plain,
    ( k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_480,c_14])).

tff(c_499,plain,(
    k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_330,c_493])).

tff(c_529,plain,(
    ! [B_138,A_139] :
      ( k9_relat_1(B_138,k10_relat_1(B_138,A_139)) = A_139
      | ~ r1_tarski(A_139,k2_relat_1(B_138))
      | ~ v1_funct_1(B_138)
      | ~ v1_relat_1(B_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_531,plain,(
    ! [A_139] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_139)) = A_139
      | ~ r1_tarski(A_139,'#skF_1')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_480,c_529])).

tff(c_561,plain,(
    ! [A_141] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_141)) = A_141
      | ~ r1_tarski(A_141,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_330,c_62,c_531])).

tff(c_576,plain,
    ( k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_499,c_561])).

tff(c_590,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_576])).

tff(c_668,plain,(
    ! [A_152,B_153] :
      ( k9_relat_1(k2_funct_1(A_152),k9_relat_1(A_152,B_153)) = B_153
      | ~ r1_tarski(B_153,k1_relat_1(A_152))
      | ~ v2_funct_1(A_152)
      | ~ v1_funct_1(A_152)
      | ~ v1_relat_1(A_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_689,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),'#skF_1') = k1_relat_1('#skF_3')
    | ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_590,c_668])).

tff(c_704,plain,(
    k9_relat_1(k2_funct_1('#skF_3'),'#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_330,c_62,c_655,c_6,c_689])).

tff(c_332,plain,(
    ! [B_98,A_99] :
      ( k2_relat_1(k7_relat_1(B_98,A_99)) = k9_relat_1(B_98,A_99)
      | ~ v1_relat_1(B_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_789,plain,(
    ! [B_159,A_160] :
      ( k10_relat_1(k7_relat_1(B_159,A_160),k9_relat_1(B_159,A_160)) = k1_relat_1(k7_relat_1(B_159,A_160))
      | ~ v1_relat_1(k7_relat_1(B_159,A_160))
      | ~ v1_relat_1(B_159) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_332,c_14])).

tff(c_801,plain,
    ( k10_relat_1(k7_relat_1(k2_funct_1('#skF_3'),'#skF_1'),k1_relat_1('#skF_3')) = k1_relat_1(k7_relat_1(k2_funct_1('#skF_3'),'#skF_1'))
    | ~ v1_relat_1(k7_relat_1(k2_funct_1('#skF_3'),'#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_704,c_789])).

tff(c_1921,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_801])).

tff(c_2008,plain,(
    ! [A_225,B_226] :
      ( m1_subset_1(k2_funct_2(A_225,B_226),k1_zfmisc_1(k2_zfmisc_1(A_225,A_225)))
      | ~ m1_subset_1(B_226,k1_zfmisc_1(k2_zfmisc_1(A_225,A_225)))
      | ~ v3_funct_2(B_226,A_225,A_225)
      | ~ v1_funct_2(B_226,A_225,A_225)
      | ~ v1_funct_1(B_226) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_2040,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1910,c_2008])).

tff(c_2055,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_56,c_2040])).

tff(c_8,plain,(
    ! [B_5,A_3] :
      ( v1_relat_1(B_5)
      | ~ m1_subset_1(B_5,k1_zfmisc_1(A_3))
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2084,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_2055,c_8])).

tff(c_2109,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_2084])).

tff(c_2111,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1921,c_2109])).

tff(c_2113,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_801])).

tff(c_26,plain,(
    ! [C_22,A_20,B_21] :
      ( v4_relat_1(C_22,A_20)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(A_20,B_21))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_3023,plain,(
    v4_relat_1(k2_funct_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_2924,c_26])).

tff(c_16,plain,(
    ! [B_12,A_11] :
      ( k7_relat_1(B_12,A_11) = B_12
      | ~ v4_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_3030,plain,
    ( k7_relat_1(k2_funct_1('#skF_3'),'#skF_1') = k2_funct_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_3023,c_16])).

tff(c_3033,plain,(
    k7_relat_1(k2_funct_1('#skF_3'),'#skF_1') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2113,c_3030])).

tff(c_12,plain,(
    ! [B_9,A_8] :
      ( k2_relat_1(k7_relat_1(B_9,A_8)) = k9_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_3058,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),'#skF_1') = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3033,c_12])).

tff(c_3070,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2113,c_704,c_3058])).

tff(c_24,plain,(
    ! [C_22,B_21,A_20] :
      ( v5_relat_1(C_22,B_21)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(A_20,B_21))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_3024,plain,(
    v5_relat_1(k2_funct_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_2924,c_24])).

tff(c_40,plain,(
    ! [B_35,A_34] :
      ( k2_relat_1(B_35) = A_34
      | ~ v2_funct_2(B_35,A_34)
      | ~ v5_relat_1(B_35,A_34)
      | ~ v1_relat_1(B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_3036,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1'
    | ~ v2_funct_2(k2_funct_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_3024,c_40])).

tff(c_3039,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1'
    | ~ v2_funct_2(k2_funct_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2113,c_3036])).

tff(c_3280,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3017,c_3070,c_3039])).

tff(c_349,plain,(
    ! [C_103,A_104,B_105] :
      ( v4_relat_1(C_103,A_104)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1(A_104,B_105))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_353,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_349])).

tff(c_356,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_353,c_16])).

tff(c_359,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_330,c_356])).

tff(c_363,plain,
    ( k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_359,c_12])).

tff(c_367,plain,(
    k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_330,c_363])).

tff(c_486,plain,(
    k9_relat_1('#skF_3','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_480,c_367])).

tff(c_698,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),'#skF_1') = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_486,c_668])).

tff(c_710,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),'#skF_1') = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_330,c_62,c_655,c_698])).

tff(c_718,plain,
    ( k1_relat_1('#skF_3') = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_704,c_710])).

tff(c_719,plain,(
    ~ r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_718])).

tff(c_3289,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3280,c_719])).

tff(c_3300,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_3289])).

tff(c_3301,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_718])).

tff(c_20,plain,(
    ! [B_16,A_15] :
      ( k10_relat_1(B_16,k9_relat_1(B_16,A_15)) = A_15
      | ~ v2_funct_1(B_16)
      | ~ r1_tarski(A_15,k1_relat_1(B_16))
      | ~ v1_funct_1(B_16)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_3309,plain,(
    ! [A_15] :
      ( k10_relat_1('#skF_3',k9_relat_1('#skF_3',A_15)) = A_15
      | ~ v2_funct_1('#skF_3')
      | ~ r1_tarski(A_15,'#skF_1')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3301,c_20])).

tff(c_3337,plain,(
    ! [A_265] :
      ( k10_relat_1('#skF_3',k9_relat_1('#skF_3',A_265)) = A_265
      | ~ r1_tarski(A_265,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_330,c_62,c_655,c_3309])).

tff(c_525,plain,(
    ! [A_134,B_135,C_136,D_137] :
      ( k7_relset_1(A_134,B_135,C_136,D_137) = k9_relat_1(C_136,D_137)
      | ~ m1_subset_1(C_136,k1_zfmisc_1(k2_zfmisc_1(A_134,B_135))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_528,plain,(
    ! [D_137] : k7_relset_1('#skF_1','#skF_1','#skF_3',D_137) = k9_relat_1('#skF_3',D_137) ),
    inference(resolution,[status(thm)],[c_56,c_525])).

tff(c_482,plain,(
    ! [A_129,B_130,C_131,D_132] :
      ( k8_relset_1(A_129,B_130,C_131,D_132) = k10_relat_1(C_131,D_132)
      | ~ m1_subset_1(C_131,k1_zfmisc_1(k2_zfmisc_1(A_129,B_130))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_485,plain,(
    ! [D_132] : k8_relset_1('#skF_1','#skF_1','#skF_3',D_132) = k10_relat_1('#skF_3',D_132) ),
    inference(resolution,[status(thm)],[c_56,c_482])).

tff(c_87,plain,(
    ! [B_46,A_47] :
      ( v1_relat_1(B_46)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(A_47))
      | ~ v1_relat_1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_90,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_56,c_87])).

tff(c_93,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_90])).

tff(c_95,plain,(
    ! [C_50,B_51,A_52] :
      ( v5_relat_1(C_50,B_51)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_52,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_99,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_95])).

tff(c_140,plain,(
    ! [B_59,A_60] :
      ( k2_relat_1(B_59) = A_60
      | ~ v2_funct_2(B_59,A_60)
      | ~ v5_relat_1(B_59,A_60)
      | ~ v1_relat_1(B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_143,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_99,c_140])).

tff(c_146,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_143])).

tff(c_151,plain,(
    ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_146])).

tff(c_214,plain,(
    ! [C_78,B_79,A_80] :
      ( v2_funct_2(C_78,B_79)
      | ~ v3_funct_2(C_78,A_80,B_79)
      | ~ v1_funct_1(C_78)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_80,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_217,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_214])).

tff(c_220,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_217])).

tff(c_222,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_151,c_220])).

tff(c_223,plain,(
    k2_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_146])).

tff(c_280,plain,(
    ! [B_90,A_91] :
      ( k9_relat_1(B_90,k10_relat_1(B_90,A_91)) = A_91
      | ~ r1_tarski(A_91,k2_relat_1(B_90))
      | ~ v1_funct_1(B_90)
      | ~ v1_relat_1(B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_282,plain,(
    ! [A_91] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_91)) = A_91
      | ~ r1_tarski(A_91,'#skF_1')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_223,c_280])).

tff(c_291,plain,(
    ! [A_92] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_92)) = A_92
      | ~ r1_tarski(A_92,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_62,c_282])).

tff(c_259,plain,(
    ! [A_82,B_83,C_84,D_85] :
      ( k8_relset_1(A_82,B_83,C_84,D_85) = k10_relat_1(C_84,D_85)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_262,plain,(
    ! [D_85] : k8_relset_1('#skF_1','#skF_1','#skF_3',D_85) = k10_relat_1('#skF_3',D_85) ),
    inference(resolution,[status(thm)],[c_56,c_259])).

tff(c_147,plain,(
    ! [A_61,B_62,C_63,D_64] :
      ( k7_relset_1(A_61,B_62,C_63,D_64) = k9_relat_1(C_63,D_64)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_150,plain,(
    ! [D_64] : k7_relset_1('#skF_1','#skF_1','#skF_3',D_64) = k9_relat_1('#skF_3',D_64) ),
    inference(resolution,[status(thm)],[c_56,c_147])).

tff(c_52,plain,
    ( k8_relset_1('#skF_1','#skF_1','#skF_3',k7_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2'
    | k7_relset_1('#skF_1','#skF_1','#skF_3',k8_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_77,plain,(
    k7_relset_1('#skF_1','#skF_1','#skF_3',k8_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_225,plain,(
    k9_relat_1('#skF_3',k8_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_77])).

tff(c_272,plain,(
    k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_262,c_225])).

tff(c_297,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_291,c_272])).

tff(c_312,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_297])).

tff(c_313,plain,(
    k8_relset_1('#skF_1','#skF_1','#skF_3',k7_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_503,plain,(
    k10_relat_1('#skF_3',k7_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_485,c_313])).

tff(c_540,plain,(
    k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_528,c_503])).

tff(c_3346,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3337,c_540])).

tff(c_3372,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_3346])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 15:36:05 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.87/1.98  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.87/1.99  
% 4.87/1.99  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.87/1.99  %$ v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_funct_2 > k10_relat_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 4.87/1.99  
% 4.87/1.99  %Foreground sorts:
% 4.87/1.99  
% 4.87/1.99  
% 4.87/1.99  %Background operators:
% 4.87/1.99  
% 4.87/1.99  
% 4.87/1.99  %Foreground operators:
% 4.87/1.99  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.87/1.99  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.87/1.99  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.87/1.99  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.87/1.99  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.87/1.99  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 4.87/1.99  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 4.87/1.99  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.87/1.99  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.87/1.99  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 4.87/1.99  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.87/1.99  tff('#skF_2', type, '#skF_2': $i).
% 4.87/1.99  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.87/1.99  tff('#skF_3', type, '#skF_3': $i).
% 4.87/1.99  tff('#skF_1', type, '#skF_1': $i).
% 4.87/1.99  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 4.87/1.99  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.87/1.99  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.87/1.99  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.87/1.99  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.87/1.99  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.87/1.99  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.87/1.99  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.87/1.99  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.87/1.99  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 4.87/1.99  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.87/1.99  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.87/1.99  
% 5.21/2.02  tff(f_158, negated_conjecture, ~(![A, B, C]: ((((v1_funct_1(C) & v1_funct_2(C, A, A)) & v3_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r1_tarski(B, A) => ((k7_relset_1(A, A, C, k8_relset_1(A, A, C, B)) = B) & (k8_relset_1(A, A, C, k7_relset_1(A, A, C, B)) = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_funct_2)).
% 5.21/2.02  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 5.21/2.02  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.21/2.02  tff(f_109, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_2)).
% 5.21/2.02  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.21/2.02  tff(f_143, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 5.21/2.02  tff(f_133, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 5.21/2.02  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.21/2.02  tff(f_117, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 5.21/2.02  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 5.21/2.02  tff(f_62, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_funct_1)).
% 5.21/2.02  tff(f_83, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v2_funct_1(A) & r1_tarski(B, k1_relat_1(A))) => (k9_relat_1(k2_funct_1(A), k9_relat_1(A, B)) = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t177_funct_1)).
% 5.21/2.02  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 5.21/2.02  tff(f_54, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 5.21/2.02  tff(f_72, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((r1_tarski(A, k1_relat_1(B)) & v2_funct_1(B)) => (k10_relat_1(B, k9_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t164_funct_1)).
% 5.21/2.02  tff(f_93, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 5.21/2.02  tff(f_97, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 5.21/2.02  tff(c_54, plain, (r1_tarski('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_158])).
% 5.21/2.02  tff(c_10, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.21/2.02  tff(c_56, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_158])).
% 5.21/2.02  tff(c_324, plain, (![B_94, A_95]: (v1_relat_1(B_94) | ~m1_subset_1(B_94, k1_zfmisc_1(A_95)) | ~v1_relat_1(A_95))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.21/2.02  tff(c_327, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_56, c_324])).
% 5.21/2.02  tff(c_330, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_327])).
% 5.21/2.02  tff(c_62, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_158])).
% 5.21/2.02  tff(c_58, plain, (v3_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_158])).
% 5.21/2.02  tff(c_649, plain, (![C_144, A_145, B_146]: (v2_funct_1(C_144) | ~v3_funct_2(C_144, A_145, B_146) | ~v1_funct_1(C_144) | ~m1_subset_1(C_144, k1_zfmisc_1(k2_zfmisc_1(A_145, B_146))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.21/2.02  tff(c_652, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_649])).
% 5.21/2.02  tff(c_655, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_652])).
% 5.21/2.02  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.21/2.02  tff(c_60, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_158])).
% 5.21/2.02  tff(c_1904, plain, (![A_214, B_215]: (k2_funct_2(A_214, B_215)=k2_funct_1(B_215) | ~m1_subset_1(B_215, k1_zfmisc_1(k2_zfmisc_1(A_214, A_214))) | ~v3_funct_2(B_215, A_214, A_214) | ~v1_funct_2(B_215, A_214, A_214) | ~v1_funct_1(B_215))), inference(cnfTransformation, [status(thm)], [f_143])).
% 5.21/2.02  tff(c_1907, plain, (k2_funct_2('#skF_1', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_1904])).
% 5.21/2.02  tff(c_1910, plain, (k2_funct_2('#skF_1', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_1907])).
% 5.21/2.02  tff(c_721, plain, (![A_154, B_155]: (v1_funct_1(k2_funct_2(A_154, B_155)) | ~m1_subset_1(B_155, k1_zfmisc_1(k2_zfmisc_1(A_154, A_154))) | ~v3_funct_2(B_155, A_154, A_154) | ~v1_funct_2(B_155, A_154, A_154) | ~v1_funct_1(B_155))), inference(cnfTransformation, [status(thm)], [f_133])).
% 5.21/2.02  tff(c_724, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_721])).
% 5.21/2.02  tff(c_727, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_724])).
% 5.21/2.02  tff(c_1911, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1910, c_727])).
% 5.21/2.02  tff(c_2457, plain, (![A_242, B_243]: (v3_funct_2(k2_funct_2(A_242, B_243), A_242, A_242) | ~m1_subset_1(B_243, k1_zfmisc_1(k2_zfmisc_1(A_242, A_242))) | ~v3_funct_2(B_243, A_242, A_242) | ~v1_funct_2(B_243, A_242, A_242) | ~v1_funct_1(B_243))), inference(cnfTransformation, [status(thm)], [f_133])).
% 5.21/2.02  tff(c_2459, plain, (v3_funct_2(k2_funct_2('#skF_1', '#skF_3'), '#skF_1', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_2457])).
% 5.21/2.02  tff(c_2462, plain, (v3_funct_2(k2_funct_1('#skF_3'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_1910, c_2459])).
% 5.21/2.02  tff(c_2877, plain, (![A_255, B_256]: (m1_subset_1(k2_funct_2(A_255, B_256), k1_zfmisc_1(k2_zfmisc_1(A_255, A_255))) | ~m1_subset_1(B_256, k1_zfmisc_1(k2_zfmisc_1(A_255, A_255))) | ~v3_funct_2(B_256, A_255, A_255) | ~v1_funct_2(B_256, A_255, A_255) | ~v1_funct_1(B_256))), inference(cnfTransformation, [status(thm)], [f_133])).
% 5.21/2.02  tff(c_2909, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1910, c_2877])).
% 5.21/2.02  tff(c_2924, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_56, c_2909])).
% 5.21/2.02  tff(c_32, plain, (![C_33, B_32, A_31]: (v2_funct_2(C_33, B_32) | ~v3_funct_2(C_33, A_31, B_32) | ~v1_funct_1(C_33) | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.21/2.02  tff(c_2986, plain, (v2_funct_2(k2_funct_1('#skF_3'), '#skF_1') | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2924, c_32])).
% 5.21/2.02  tff(c_3017, plain, (v2_funct_2(k2_funct_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1911, c_2462, c_2986])).
% 5.21/2.02  tff(c_344, plain, (![C_100, B_101, A_102]: (v5_relat_1(C_100, B_101) | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(A_102, B_101))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.21/2.02  tff(c_348, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_56, c_344])).
% 5.21/2.02  tff(c_381, plain, (![B_107, A_108]: (k2_relat_1(B_107)=A_108 | ~v2_funct_2(B_107, A_108) | ~v5_relat_1(B_107, A_108) | ~v1_relat_1(B_107))), inference(cnfTransformation, [status(thm)], [f_117])).
% 5.21/2.02  tff(c_384, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_348, c_381])).
% 5.21/2.02  tff(c_387, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_330, c_384])).
% 5.21/2.02  tff(c_388, plain, (~v2_funct_2('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_387])).
% 5.21/2.02  tff(c_471, plain, (![C_126, B_127, A_128]: (v2_funct_2(C_126, B_127) | ~v3_funct_2(C_126, A_128, B_127) | ~v1_funct_1(C_126) | ~m1_subset_1(C_126, k1_zfmisc_1(k2_zfmisc_1(A_128, B_127))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.21/2.02  tff(c_474, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_471])).
% 5.21/2.02  tff(c_477, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_474])).
% 5.21/2.02  tff(c_479, plain, $false, inference(negUnitSimplification, [status(thm)], [c_388, c_477])).
% 5.21/2.02  tff(c_480, plain, (k2_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_387])).
% 5.21/2.02  tff(c_14, plain, (![A_10]: (k10_relat_1(A_10, k2_relat_1(A_10))=k1_relat_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.21/2.02  tff(c_493, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_480, c_14])).
% 5.21/2.02  tff(c_499, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_330, c_493])).
% 5.21/2.02  tff(c_529, plain, (![B_138, A_139]: (k9_relat_1(B_138, k10_relat_1(B_138, A_139))=A_139 | ~r1_tarski(A_139, k2_relat_1(B_138)) | ~v1_funct_1(B_138) | ~v1_relat_1(B_138))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.21/2.02  tff(c_531, plain, (![A_139]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_139))=A_139 | ~r1_tarski(A_139, '#skF_1') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_480, c_529])).
% 5.21/2.02  tff(c_561, plain, (![A_141]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_141))=A_141 | ~r1_tarski(A_141, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_330, c_62, c_531])).
% 5.21/2.02  tff(c_576, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_1' | ~r1_tarski('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_499, c_561])).
% 5.21/2.02  tff(c_590, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_6, c_576])).
% 5.21/2.02  tff(c_668, plain, (![A_152, B_153]: (k9_relat_1(k2_funct_1(A_152), k9_relat_1(A_152, B_153))=B_153 | ~r1_tarski(B_153, k1_relat_1(A_152)) | ~v2_funct_1(A_152) | ~v1_funct_1(A_152) | ~v1_relat_1(A_152))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.21/2.02  tff(c_689, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_1')=k1_relat_1('#skF_3') | ~r1_tarski(k1_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_590, c_668])).
% 5.21/2.02  tff(c_704, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_330, c_62, c_655, c_6, c_689])).
% 5.21/2.02  tff(c_332, plain, (![B_98, A_99]: (k2_relat_1(k7_relat_1(B_98, A_99))=k9_relat_1(B_98, A_99) | ~v1_relat_1(B_98))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.21/2.02  tff(c_789, plain, (![B_159, A_160]: (k10_relat_1(k7_relat_1(B_159, A_160), k9_relat_1(B_159, A_160))=k1_relat_1(k7_relat_1(B_159, A_160)) | ~v1_relat_1(k7_relat_1(B_159, A_160)) | ~v1_relat_1(B_159))), inference(superposition, [status(thm), theory('equality')], [c_332, c_14])).
% 5.21/2.02  tff(c_801, plain, (k10_relat_1(k7_relat_1(k2_funct_1('#skF_3'), '#skF_1'), k1_relat_1('#skF_3'))=k1_relat_1(k7_relat_1(k2_funct_1('#skF_3'), '#skF_1')) | ~v1_relat_1(k7_relat_1(k2_funct_1('#skF_3'), '#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_704, c_789])).
% 5.21/2.02  tff(c_1921, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_801])).
% 5.21/2.02  tff(c_2008, plain, (![A_225, B_226]: (m1_subset_1(k2_funct_2(A_225, B_226), k1_zfmisc_1(k2_zfmisc_1(A_225, A_225))) | ~m1_subset_1(B_226, k1_zfmisc_1(k2_zfmisc_1(A_225, A_225))) | ~v3_funct_2(B_226, A_225, A_225) | ~v1_funct_2(B_226, A_225, A_225) | ~v1_funct_1(B_226))), inference(cnfTransformation, [status(thm)], [f_133])).
% 5.21/2.02  tff(c_2040, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1910, c_2008])).
% 5.21/2.02  tff(c_2055, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_56, c_2040])).
% 5.21/2.02  tff(c_8, plain, (![B_5, A_3]: (v1_relat_1(B_5) | ~m1_subset_1(B_5, k1_zfmisc_1(A_3)) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.21/2.02  tff(c_2084, plain, (v1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_2055, c_8])).
% 5.21/2.02  tff(c_2109, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_2084])).
% 5.21/2.02  tff(c_2111, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1921, c_2109])).
% 5.21/2.02  tff(c_2113, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_801])).
% 5.21/2.02  tff(c_26, plain, (![C_22, A_20, B_21]: (v4_relat_1(C_22, A_20) | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(A_20, B_21))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.21/2.02  tff(c_3023, plain, (v4_relat_1(k2_funct_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_2924, c_26])).
% 5.21/2.02  tff(c_16, plain, (![B_12, A_11]: (k7_relat_1(B_12, A_11)=B_12 | ~v4_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.21/2.02  tff(c_3030, plain, (k7_relat_1(k2_funct_1('#skF_3'), '#skF_1')=k2_funct_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_3023, c_16])).
% 5.21/2.02  tff(c_3033, plain, (k7_relat_1(k2_funct_1('#skF_3'), '#skF_1')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2113, c_3030])).
% 5.21/2.02  tff(c_12, plain, (![B_9, A_8]: (k2_relat_1(k7_relat_1(B_9, A_8))=k9_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.21/2.02  tff(c_3058, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_1')=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_3033, c_12])).
% 5.21/2.02  tff(c_3070, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2113, c_704, c_3058])).
% 5.21/2.02  tff(c_24, plain, (![C_22, B_21, A_20]: (v5_relat_1(C_22, B_21) | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(A_20, B_21))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.21/2.02  tff(c_3024, plain, (v5_relat_1(k2_funct_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_2924, c_24])).
% 5.21/2.02  tff(c_40, plain, (![B_35, A_34]: (k2_relat_1(B_35)=A_34 | ~v2_funct_2(B_35, A_34) | ~v5_relat_1(B_35, A_34) | ~v1_relat_1(B_35))), inference(cnfTransformation, [status(thm)], [f_117])).
% 5.21/2.02  tff(c_3036, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1' | ~v2_funct_2(k2_funct_1('#skF_3'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_3024, c_40])).
% 5.21/2.02  tff(c_3039, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1' | ~v2_funct_2(k2_funct_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2113, c_3036])).
% 5.21/2.02  tff(c_3280, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3017, c_3070, c_3039])).
% 5.21/2.02  tff(c_349, plain, (![C_103, A_104, B_105]: (v4_relat_1(C_103, A_104) | ~m1_subset_1(C_103, k1_zfmisc_1(k2_zfmisc_1(A_104, B_105))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.21/2.02  tff(c_353, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_56, c_349])).
% 5.21/2.02  tff(c_356, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_353, c_16])).
% 5.21/2.02  tff(c_359, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_330, c_356])).
% 5.21/2.02  tff(c_363, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_359, c_12])).
% 5.21/2.02  tff(c_367, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_330, c_363])).
% 5.21/2.02  tff(c_486, plain, (k9_relat_1('#skF_3', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_480, c_367])).
% 5.21/2.02  tff(c_698, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_1')='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_486, c_668])).
% 5.21/2.02  tff(c_710, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_1')='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_330, c_62, c_655, c_698])).
% 5.21/2.02  tff(c_718, plain, (k1_relat_1('#skF_3')='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_704, c_710])).
% 5.21/2.02  tff(c_719, plain, (~r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_718])).
% 5.21/2.02  tff(c_3289, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3280, c_719])).
% 5.21/2.02  tff(c_3300, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_3289])).
% 5.21/2.02  tff(c_3301, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_718])).
% 5.21/2.02  tff(c_20, plain, (![B_16, A_15]: (k10_relat_1(B_16, k9_relat_1(B_16, A_15))=A_15 | ~v2_funct_1(B_16) | ~r1_tarski(A_15, k1_relat_1(B_16)) | ~v1_funct_1(B_16) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.21/2.02  tff(c_3309, plain, (![A_15]: (k10_relat_1('#skF_3', k9_relat_1('#skF_3', A_15))=A_15 | ~v2_funct_1('#skF_3') | ~r1_tarski(A_15, '#skF_1') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_3301, c_20])).
% 5.21/2.02  tff(c_3337, plain, (![A_265]: (k10_relat_1('#skF_3', k9_relat_1('#skF_3', A_265))=A_265 | ~r1_tarski(A_265, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_330, c_62, c_655, c_3309])).
% 5.21/2.02  tff(c_525, plain, (![A_134, B_135, C_136, D_137]: (k7_relset_1(A_134, B_135, C_136, D_137)=k9_relat_1(C_136, D_137) | ~m1_subset_1(C_136, k1_zfmisc_1(k2_zfmisc_1(A_134, B_135))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.21/2.02  tff(c_528, plain, (![D_137]: (k7_relset_1('#skF_1', '#skF_1', '#skF_3', D_137)=k9_relat_1('#skF_3', D_137))), inference(resolution, [status(thm)], [c_56, c_525])).
% 5.21/2.02  tff(c_482, plain, (![A_129, B_130, C_131, D_132]: (k8_relset_1(A_129, B_130, C_131, D_132)=k10_relat_1(C_131, D_132) | ~m1_subset_1(C_131, k1_zfmisc_1(k2_zfmisc_1(A_129, B_130))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.21/2.02  tff(c_485, plain, (![D_132]: (k8_relset_1('#skF_1', '#skF_1', '#skF_3', D_132)=k10_relat_1('#skF_3', D_132))), inference(resolution, [status(thm)], [c_56, c_482])).
% 5.21/2.02  tff(c_87, plain, (![B_46, A_47]: (v1_relat_1(B_46) | ~m1_subset_1(B_46, k1_zfmisc_1(A_47)) | ~v1_relat_1(A_47))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.21/2.02  tff(c_90, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_56, c_87])).
% 5.21/2.02  tff(c_93, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_90])).
% 5.21/2.02  tff(c_95, plain, (![C_50, B_51, A_52]: (v5_relat_1(C_50, B_51) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_52, B_51))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.21/2.02  tff(c_99, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_56, c_95])).
% 5.21/2.02  tff(c_140, plain, (![B_59, A_60]: (k2_relat_1(B_59)=A_60 | ~v2_funct_2(B_59, A_60) | ~v5_relat_1(B_59, A_60) | ~v1_relat_1(B_59))), inference(cnfTransformation, [status(thm)], [f_117])).
% 5.21/2.02  tff(c_143, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_99, c_140])).
% 5.21/2.02  tff(c_146, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_93, c_143])).
% 5.21/2.02  tff(c_151, plain, (~v2_funct_2('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_146])).
% 5.21/2.02  tff(c_214, plain, (![C_78, B_79, A_80]: (v2_funct_2(C_78, B_79) | ~v3_funct_2(C_78, A_80, B_79) | ~v1_funct_1(C_78) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_80, B_79))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.21/2.02  tff(c_217, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_214])).
% 5.21/2.02  tff(c_220, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_217])).
% 5.21/2.02  tff(c_222, plain, $false, inference(negUnitSimplification, [status(thm)], [c_151, c_220])).
% 5.21/2.02  tff(c_223, plain, (k2_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_146])).
% 5.21/2.02  tff(c_280, plain, (![B_90, A_91]: (k9_relat_1(B_90, k10_relat_1(B_90, A_91))=A_91 | ~r1_tarski(A_91, k2_relat_1(B_90)) | ~v1_funct_1(B_90) | ~v1_relat_1(B_90))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.21/2.02  tff(c_282, plain, (![A_91]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_91))=A_91 | ~r1_tarski(A_91, '#skF_1') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_223, c_280])).
% 5.21/2.02  tff(c_291, plain, (![A_92]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_92))=A_92 | ~r1_tarski(A_92, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_62, c_282])).
% 5.21/2.02  tff(c_259, plain, (![A_82, B_83, C_84, D_85]: (k8_relset_1(A_82, B_83, C_84, D_85)=k10_relat_1(C_84, D_85) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.21/2.02  tff(c_262, plain, (![D_85]: (k8_relset_1('#skF_1', '#skF_1', '#skF_3', D_85)=k10_relat_1('#skF_3', D_85))), inference(resolution, [status(thm)], [c_56, c_259])).
% 5.21/2.02  tff(c_147, plain, (![A_61, B_62, C_63, D_64]: (k7_relset_1(A_61, B_62, C_63, D_64)=k9_relat_1(C_63, D_64) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.21/2.02  tff(c_150, plain, (![D_64]: (k7_relset_1('#skF_1', '#skF_1', '#skF_3', D_64)=k9_relat_1('#skF_3', D_64))), inference(resolution, [status(thm)], [c_56, c_147])).
% 5.21/2.02  tff(c_52, plain, (k8_relset_1('#skF_1', '#skF_1', '#skF_3', k7_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2' | k7_relset_1('#skF_1', '#skF_1', '#skF_3', k8_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_158])).
% 5.21/2.02  tff(c_77, plain, (k7_relset_1('#skF_1', '#skF_1', '#skF_3', k8_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_52])).
% 5.21/2.02  tff(c_225, plain, (k9_relat_1('#skF_3', k8_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_150, c_77])).
% 5.21/2.02  tff(c_272, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_262, c_225])).
% 5.21/2.02  tff(c_297, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_291, c_272])).
% 5.21/2.02  tff(c_312, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_297])).
% 5.21/2.02  tff(c_313, plain, (k8_relset_1('#skF_1', '#skF_1', '#skF_3', k7_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2'), inference(splitRight, [status(thm)], [c_52])).
% 5.21/2.02  tff(c_503, plain, (k10_relat_1('#skF_3', k7_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_485, c_313])).
% 5.21/2.02  tff(c_540, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_528, c_503])).
% 5.21/2.02  tff(c_3346, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3337, c_540])).
% 5.21/2.02  tff(c_3372, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_3346])).
% 5.21/2.02  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.21/2.02  
% 5.21/2.02  Inference rules
% 5.21/2.02  ----------------------
% 5.21/2.02  #Ref     : 0
% 5.21/2.02  #Sup     : 724
% 5.21/2.02  #Fact    : 0
% 5.21/2.02  #Define  : 0
% 5.21/2.02  #Split   : 27
% 5.21/2.02  #Chain   : 0
% 5.21/2.02  #Close   : 0
% 5.21/2.02  
% 5.21/2.02  Ordering : KBO
% 5.21/2.02  
% 5.21/2.02  Simplification rules
% 5.21/2.02  ----------------------
% 5.21/2.02  #Subsume      : 34
% 5.21/2.02  #Demod        : 1366
% 5.21/2.02  #Tautology    : 229
% 5.21/2.02  #SimpNegUnit  : 8
% 5.21/2.02  #BackRed      : 58
% 5.21/2.02  
% 5.21/2.02  #Partial instantiations: 0
% 5.21/2.02  #Strategies tried      : 1
% 5.21/2.02  
% 5.21/2.02  Timing (in seconds)
% 5.21/2.02  ----------------------
% 5.21/2.03  Preprocessing        : 0.36
% 5.21/2.03  Parsing              : 0.20
% 5.21/2.03  CNF conversion       : 0.02
% 5.21/2.03  Main loop            : 0.79
% 5.21/2.03  Inferencing          : 0.26
% 5.21/2.03  Reduction            : 0.31
% 5.21/2.03  Demodulation         : 0.23
% 5.21/2.03  BG Simplification    : 0.03
% 5.21/2.03  Subsumption          : 0.13
% 5.21/2.03  Abstraction          : 0.04
% 5.21/2.03  MUC search           : 0.00
% 5.21/2.03  Cooper               : 0.00
% 5.21/2.03  Total                : 1.21
% 5.21/2.03  Index Insertion      : 0.00
% 5.21/2.03  Index Deletion       : 0.00
% 5.21/2.03  Index Matching       : 0.00
% 5.21/2.03  BG Taut test         : 0.00
%------------------------------------------------------------------------------
