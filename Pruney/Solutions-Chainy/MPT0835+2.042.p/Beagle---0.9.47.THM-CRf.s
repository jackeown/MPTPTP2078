%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:01 EST 2020

% Result     : Theorem 2.87s
% Output     : CNFRefutation 2.87s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 185 expanded)
%              Number of leaves         :   41 (  78 expanded)
%              Depth                    :   11
%              Number of atoms          :  160 ( 309 expanded)
%              Number of equality atoms :   65 ( 111 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_108,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( k7_relset_1(B,A,C,k8_relset_1(B,A,C,A)) = k2_relset_1(B,A,C)
          & k8_relset_1(B,A,C,k7_relset_1(B,A,C,B)) = k1_relset_1(B,A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_relset_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_40,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_71,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_95,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_67,axiom,(
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

tff(f_91,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(c_10,plain,(
    ! [A_7,B_8] : v1_relat_1(k2_zfmisc_1(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_44,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_483,plain,(
    ! [B_96,A_97] :
      ( v1_relat_1(B_96)
      | ~ m1_subset_1(B_96,k1_zfmisc_1(A_97))
      | ~ v1_relat_1(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_486,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_44,c_483])).

tff(c_489,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_486])).

tff(c_16,plain,(
    ! [A_12] :
      ( k10_relat_1(A_12,k2_relat_1(A_12)) = k1_relat_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_490,plain,(
    ! [C_98,B_99,A_100] :
      ( v5_relat_1(C_98,B_99)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_100,B_99))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_494,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_490])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k2_relat_1(B_5),A_4)
      | ~ v5_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_564,plain,(
    ! [B_116,A_117] :
      ( k5_relat_1(B_116,k6_relat_1(A_117)) = B_116
      | ~ r1_tarski(k2_relat_1(B_116),A_117)
      | ~ v1_relat_1(B_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_574,plain,(
    ! [B_5,A_4] :
      ( k5_relat_1(B_5,k6_relat_1(A_4)) = B_5
      | ~ v5_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(resolution,[status(thm)],[c_6,c_564])).

tff(c_8,plain,(
    ! [A_6] : v1_relat_1(k6_relat_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_22,plain,(
    ! [A_18] : k1_relat_1(k6_relat_1(A_18)) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_613,plain,(
    ! [A_125,B_126] :
      ( k10_relat_1(A_125,k1_relat_1(B_126)) = k1_relat_1(k5_relat_1(A_125,B_126))
      | ~ v1_relat_1(B_126)
      | ~ v1_relat_1(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_630,plain,(
    ! [A_125,A_18] :
      ( k1_relat_1(k5_relat_1(A_125,k6_relat_1(A_18))) = k10_relat_1(A_125,A_18)
      | ~ v1_relat_1(k6_relat_1(A_18))
      | ~ v1_relat_1(A_125) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_613])).

tff(c_644,plain,(
    ! [A_127,A_128] :
      ( k1_relat_1(k5_relat_1(A_127,k6_relat_1(A_128))) = k10_relat_1(A_127,A_128)
      | ~ v1_relat_1(A_127) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_630])).

tff(c_807,plain,(
    ! [B_133,A_134] :
      ( k10_relat_1(B_133,A_134) = k1_relat_1(B_133)
      | ~ v1_relat_1(B_133)
      | ~ v5_relat_1(B_133,A_134)
      | ~ v1_relat_1(B_133) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_574,c_644])).

tff(c_813,plain,
    ( k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_494,c_807])).

tff(c_819,plain,(
    k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_489,c_813])).

tff(c_913,plain,(
    ! [A_142,B_143,C_144,D_145] :
      ( k8_relset_1(A_142,B_143,C_144,D_145) = k10_relat_1(C_144,D_145)
      | ~ m1_subset_1(C_144,k1_zfmisc_1(k2_zfmisc_1(A_142,B_143))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_916,plain,(
    ! [D_145] : k8_relset_1('#skF_2','#skF_1','#skF_3',D_145) = k10_relat_1('#skF_3',D_145) ),
    inference(resolution,[status(thm)],[c_44,c_913])).

tff(c_947,plain,(
    ! [A_147,B_148,C_149] :
      ( k8_relset_1(A_147,B_148,C_149,B_148) = k1_relset_1(A_147,B_148,C_149)
      | ~ m1_subset_1(C_149,k1_zfmisc_1(k2_zfmisc_1(A_147,B_148))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_949,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1') = k1_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_947])).

tff(c_951,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_819,c_916,c_949])).

tff(c_522,plain,(
    ! [C_109,A_110,B_111] :
      ( v4_relat_1(C_109,A_110)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_110,B_111))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_526,plain,(
    v4_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_522])).

tff(c_20,plain,(
    ! [B_17,A_16] :
      ( k7_relat_1(B_17,A_16) = B_17
      | ~ v4_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_542,plain,
    ( k7_relat_1('#skF_3','#skF_2') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_526,c_20])).

tff(c_545,plain,(
    k7_relat_1('#skF_3','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_489,c_542])).

tff(c_14,plain,(
    ! [B_11,A_10] :
      ( k2_relat_1(k7_relat_1(B_11,A_10)) = k9_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_549,plain,
    ( k9_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_545,c_14])).

tff(c_553,plain,(
    k9_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_489,c_549])).

tff(c_824,plain,(
    ! [A_135,B_136,C_137,D_138] :
      ( k7_relset_1(A_135,B_136,C_137,D_138) = k9_relat_1(C_137,D_138)
      | ~ m1_subset_1(C_137,k1_zfmisc_1(k2_zfmisc_1(A_135,B_136))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_827,plain,(
    ! [D_138] : k7_relset_1('#skF_2','#skF_1','#skF_3',D_138) = k9_relat_1('#skF_3',D_138) ),
    inference(resolution,[status(thm)],[c_44,c_824])).

tff(c_112,plain,(
    ! [B_47,A_48] :
      ( v1_relat_1(B_47)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(A_48))
      | ~ v1_relat_1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_115,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_44,c_112])).

tff(c_118,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_115])).

tff(c_12,plain,(
    ! [A_9] :
      ( k9_relat_1(A_9,k1_relat_1(A_9)) = k2_relat_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_119,plain,(
    ! [C_49,B_50,A_51] :
      ( v5_relat_1(C_49,B_50)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_51,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_123,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_119])).

tff(c_189,plain,(
    ! [B_67,A_68] :
      ( k5_relat_1(B_67,k6_relat_1(A_68)) = B_67
      | ~ r1_tarski(k2_relat_1(B_67),A_68)
      | ~ v1_relat_1(B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_199,plain,(
    ! [B_5,A_4] :
      ( k5_relat_1(B_5,k6_relat_1(A_4)) = B_5
      | ~ v5_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(resolution,[status(thm)],[c_6,c_189])).

tff(c_233,plain,(
    ! [A_73,B_74] :
      ( k10_relat_1(A_73,k1_relat_1(B_74)) = k1_relat_1(k5_relat_1(A_73,B_74))
      | ~ v1_relat_1(B_74)
      | ~ v1_relat_1(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_250,plain,(
    ! [A_73,A_18] :
      ( k1_relat_1(k5_relat_1(A_73,k6_relat_1(A_18))) = k10_relat_1(A_73,A_18)
      | ~ v1_relat_1(k6_relat_1(A_18))
      | ~ v1_relat_1(A_73) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_233])).

tff(c_269,plain,(
    ! [A_78,A_79] :
      ( k1_relat_1(k5_relat_1(A_78,k6_relat_1(A_79))) = k10_relat_1(A_78,A_79)
      | ~ v1_relat_1(A_78) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_250])).

tff(c_456,plain,(
    ! [B_94,A_95] :
      ( k10_relat_1(B_94,A_95) = k1_relat_1(B_94)
      | ~ v1_relat_1(B_94)
      | ~ v5_relat_1(B_94,A_95)
      | ~ v1_relat_1(B_94) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_199,c_269])).

tff(c_462,plain,
    ( k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_123,c_456])).

tff(c_468,plain,(
    k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_462])).

tff(c_442,plain,(
    ! [A_89,B_90,C_91,D_92] :
      ( k7_relset_1(A_89,B_90,C_91,D_92) = k9_relat_1(C_91,D_92)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_445,plain,(
    ! [D_92] : k7_relset_1('#skF_2','#skF_1','#skF_3',D_92) = k9_relat_1('#skF_3',D_92) ),
    inference(resolution,[status(thm)],[c_44,c_442])).

tff(c_428,plain,(
    ! [A_84,B_85,C_86,D_87] :
      ( k8_relset_1(A_84,B_85,C_86,D_87) = k10_relat_1(C_86,D_87)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_431,plain,(
    ! [D_87] : k8_relset_1('#skF_2','#skF_1','#skF_3',D_87) = k10_relat_1('#skF_3',D_87) ),
    inference(resolution,[status(thm)],[c_44,c_428])).

tff(c_259,plain,(
    ! [A_75,B_76,C_77] :
      ( k2_relset_1(A_75,B_76,C_77) = k2_relat_1(C_77)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_263,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_259])).

tff(c_42,plain,
    ( k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relset_1('#skF_2','#skF_1','#skF_3')
    | k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_111,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_264,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_263,c_111])).

tff(c_441,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k10_relat_1('#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_431,c_264])).

tff(c_446,plain,(
    k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_445,c_441])).

tff(c_469,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_468,c_446])).

tff(c_476,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_469])).

tff(c_480,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_476])).

tff(c_481,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_828,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k9_relat_1('#skF_3','#skF_2')) != k1_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_827,c_481])).

tff(c_829,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k2_relat_1('#skF_3')) != k1_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_553,c_828])).

tff(c_917,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) != k1_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_916,c_829])).

tff(c_957,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_951,c_917])).

tff(c_960,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_957])).

tff(c_964,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_489,c_960])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n005.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 13:29:47 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.87/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.87/1.43  
% 2.87/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.87/1.43  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.87/1.43  
% 2.87/1.43  %Foreground sorts:
% 2.87/1.43  
% 2.87/1.43  
% 2.87/1.43  %Background operators:
% 2.87/1.43  
% 2.87/1.43  
% 2.87/1.43  %Foreground operators:
% 2.87/1.43  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.87/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.87/1.43  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.87/1.43  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.87/1.43  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.87/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.87/1.43  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.87/1.43  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.87/1.43  tff('#skF_2', type, '#skF_2': $i).
% 2.87/1.43  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.87/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.87/1.43  tff('#skF_1', type, '#skF_1': $i).
% 2.87/1.43  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.87/1.43  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.87/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.87/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.87/1.43  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.87/1.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.87/1.43  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.87/1.43  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.87/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.87/1.43  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.87/1.43  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.87/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.87/1.43  
% 2.87/1.45  tff(f_42, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.87/1.45  tff(f_108, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((k7_relset_1(B, A, C, k8_relset_1(B, A, C, A)) = k2_relset_1(B, A, C)) & (k8_relset_1(B, A, C, k7_relset_1(B, A, C, B)) = k1_relset_1(B, A, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_relset_1)).
% 2.87/1.45  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.87/1.45  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 2.87/1.45  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.87/1.45  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 2.87/1.45  tff(f_77, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 2.87/1.45  tff(f_40, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.87/1.45  tff(f_71, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 2.87/1.45  tff(f_61, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 2.87/1.45  tff(f_95, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.87/1.45  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_relset_1)).
% 2.87/1.45  tff(f_67, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 2.87/1.45  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 2.87/1.45  tff(f_91, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.87/1.45  tff(f_46, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 2.87/1.45  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.87/1.45  tff(c_10, plain, (![A_7, B_8]: (v1_relat_1(k2_zfmisc_1(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.87/1.45  tff(c_44, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.87/1.45  tff(c_483, plain, (![B_96, A_97]: (v1_relat_1(B_96) | ~m1_subset_1(B_96, k1_zfmisc_1(A_97)) | ~v1_relat_1(A_97))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.87/1.45  tff(c_486, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_44, c_483])).
% 2.87/1.45  tff(c_489, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_486])).
% 2.87/1.45  tff(c_16, plain, (![A_12]: (k10_relat_1(A_12, k2_relat_1(A_12))=k1_relat_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.87/1.45  tff(c_490, plain, (![C_98, B_99, A_100]: (v5_relat_1(C_98, B_99) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_100, B_99))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.87/1.45  tff(c_494, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_44, c_490])).
% 2.87/1.45  tff(c_6, plain, (![B_5, A_4]: (r1_tarski(k2_relat_1(B_5), A_4) | ~v5_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.87/1.45  tff(c_564, plain, (![B_116, A_117]: (k5_relat_1(B_116, k6_relat_1(A_117))=B_116 | ~r1_tarski(k2_relat_1(B_116), A_117) | ~v1_relat_1(B_116))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.87/1.45  tff(c_574, plain, (![B_5, A_4]: (k5_relat_1(B_5, k6_relat_1(A_4))=B_5 | ~v5_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(resolution, [status(thm)], [c_6, c_564])).
% 2.87/1.45  tff(c_8, plain, (![A_6]: (v1_relat_1(k6_relat_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.87/1.45  tff(c_22, plain, (![A_18]: (k1_relat_1(k6_relat_1(A_18))=A_18)), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.87/1.45  tff(c_613, plain, (![A_125, B_126]: (k10_relat_1(A_125, k1_relat_1(B_126))=k1_relat_1(k5_relat_1(A_125, B_126)) | ~v1_relat_1(B_126) | ~v1_relat_1(A_125))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.87/1.45  tff(c_630, plain, (![A_125, A_18]: (k1_relat_1(k5_relat_1(A_125, k6_relat_1(A_18)))=k10_relat_1(A_125, A_18) | ~v1_relat_1(k6_relat_1(A_18)) | ~v1_relat_1(A_125))), inference(superposition, [status(thm), theory('equality')], [c_22, c_613])).
% 2.87/1.45  tff(c_644, plain, (![A_127, A_128]: (k1_relat_1(k5_relat_1(A_127, k6_relat_1(A_128)))=k10_relat_1(A_127, A_128) | ~v1_relat_1(A_127))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_630])).
% 2.87/1.45  tff(c_807, plain, (![B_133, A_134]: (k10_relat_1(B_133, A_134)=k1_relat_1(B_133) | ~v1_relat_1(B_133) | ~v5_relat_1(B_133, A_134) | ~v1_relat_1(B_133))), inference(superposition, [status(thm), theory('equality')], [c_574, c_644])).
% 2.87/1.45  tff(c_813, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_494, c_807])).
% 2.87/1.45  tff(c_819, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_489, c_813])).
% 2.87/1.45  tff(c_913, plain, (![A_142, B_143, C_144, D_145]: (k8_relset_1(A_142, B_143, C_144, D_145)=k10_relat_1(C_144, D_145) | ~m1_subset_1(C_144, k1_zfmisc_1(k2_zfmisc_1(A_142, B_143))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.87/1.45  tff(c_916, plain, (![D_145]: (k8_relset_1('#skF_2', '#skF_1', '#skF_3', D_145)=k10_relat_1('#skF_3', D_145))), inference(resolution, [status(thm)], [c_44, c_913])).
% 2.87/1.45  tff(c_947, plain, (![A_147, B_148, C_149]: (k8_relset_1(A_147, B_148, C_149, B_148)=k1_relset_1(A_147, B_148, C_149) | ~m1_subset_1(C_149, k1_zfmisc_1(k2_zfmisc_1(A_147, B_148))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.87/1.45  tff(c_949, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1')=k1_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_44, c_947])).
% 2.87/1.45  tff(c_951, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_819, c_916, c_949])).
% 2.87/1.45  tff(c_522, plain, (![C_109, A_110, B_111]: (v4_relat_1(C_109, A_110) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_110, B_111))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.87/1.45  tff(c_526, plain, (v4_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_44, c_522])).
% 2.87/1.45  tff(c_20, plain, (![B_17, A_16]: (k7_relat_1(B_17, A_16)=B_17 | ~v4_relat_1(B_17, A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.87/1.45  tff(c_542, plain, (k7_relat_1('#skF_3', '#skF_2')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_526, c_20])).
% 2.87/1.45  tff(c_545, plain, (k7_relat_1('#skF_3', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_489, c_542])).
% 2.87/1.45  tff(c_14, plain, (![B_11, A_10]: (k2_relat_1(k7_relat_1(B_11, A_10))=k9_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.87/1.45  tff(c_549, plain, (k9_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_545, c_14])).
% 2.87/1.45  tff(c_553, plain, (k9_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_489, c_549])).
% 2.87/1.45  tff(c_824, plain, (![A_135, B_136, C_137, D_138]: (k7_relset_1(A_135, B_136, C_137, D_138)=k9_relat_1(C_137, D_138) | ~m1_subset_1(C_137, k1_zfmisc_1(k2_zfmisc_1(A_135, B_136))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.87/1.45  tff(c_827, plain, (![D_138]: (k7_relset_1('#skF_2', '#skF_1', '#skF_3', D_138)=k9_relat_1('#skF_3', D_138))), inference(resolution, [status(thm)], [c_44, c_824])).
% 2.87/1.45  tff(c_112, plain, (![B_47, A_48]: (v1_relat_1(B_47) | ~m1_subset_1(B_47, k1_zfmisc_1(A_48)) | ~v1_relat_1(A_48))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.87/1.45  tff(c_115, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_44, c_112])).
% 2.87/1.45  tff(c_118, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_115])).
% 2.87/1.45  tff(c_12, plain, (![A_9]: (k9_relat_1(A_9, k1_relat_1(A_9))=k2_relat_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.87/1.45  tff(c_119, plain, (![C_49, B_50, A_51]: (v5_relat_1(C_49, B_50) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_51, B_50))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.87/1.45  tff(c_123, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_44, c_119])).
% 2.87/1.45  tff(c_189, plain, (![B_67, A_68]: (k5_relat_1(B_67, k6_relat_1(A_68))=B_67 | ~r1_tarski(k2_relat_1(B_67), A_68) | ~v1_relat_1(B_67))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.87/1.45  tff(c_199, plain, (![B_5, A_4]: (k5_relat_1(B_5, k6_relat_1(A_4))=B_5 | ~v5_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(resolution, [status(thm)], [c_6, c_189])).
% 2.87/1.45  tff(c_233, plain, (![A_73, B_74]: (k10_relat_1(A_73, k1_relat_1(B_74))=k1_relat_1(k5_relat_1(A_73, B_74)) | ~v1_relat_1(B_74) | ~v1_relat_1(A_73))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.87/1.45  tff(c_250, plain, (![A_73, A_18]: (k1_relat_1(k5_relat_1(A_73, k6_relat_1(A_18)))=k10_relat_1(A_73, A_18) | ~v1_relat_1(k6_relat_1(A_18)) | ~v1_relat_1(A_73))), inference(superposition, [status(thm), theory('equality')], [c_22, c_233])).
% 2.87/1.45  tff(c_269, plain, (![A_78, A_79]: (k1_relat_1(k5_relat_1(A_78, k6_relat_1(A_79)))=k10_relat_1(A_78, A_79) | ~v1_relat_1(A_78))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_250])).
% 2.87/1.45  tff(c_456, plain, (![B_94, A_95]: (k10_relat_1(B_94, A_95)=k1_relat_1(B_94) | ~v1_relat_1(B_94) | ~v5_relat_1(B_94, A_95) | ~v1_relat_1(B_94))), inference(superposition, [status(thm), theory('equality')], [c_199, c_269])).
% 2.87/1.45  tff(c_462, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_123, c_456])).
% 2.87/1.45  tff(c_468, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_118, c_462])).
% 2.87/1.45  tff(c_442, plain, (![A_89, B_90, C_91, D_92]: (k7_relset_1(A_89, B_90, C_91, D_92)=k9_relat_1(C_91, D_92) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.87/1.45  tff(c_445, plain, (![D_92]: (k7_relset_1('#skF_2', '#skF_1', '#skF_3', D_92)=k9_relat_1('#skF_3', D_92))), inference(resolution, [status(thm)], [c_44, c_442])).
% 2.87/1.45  tff(c_428, plain, (![A_84, B_85, C_86, D_87]: (k8_relset_1(A_84, B_85, C_86, D_87)=k10_relat_1(C_86, D_87) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.87/1.45  tff(c_431, plain, (![D_87]: (k8_relset_1('#skF_2', '#skF_1', '#skF_3', D_87)=k10_relat_1('#skF_3', D_87))), inference(resolution, [status(thm)], [c_44, c_428])).
% 2.87/1.45  tff(c_259, plain, (![A_75, B_76, C_77]: (k2_relset_1(A_75, B_76, C_77)=k2_relat_1(C_77) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.87/1.45  tff(c_263, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_259])).
% 2.87/1.45  tff(c_42, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relset_1('#skF_2', '#skF_1', '#skF_3') | k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.87/1.45  tff(c_111, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_42])).
% 2.87/1.45  tff(c_264, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_263, c_111])).
% 2.87/1.45  tff(c_441, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k10_relat_1('#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_431, c_264])).
% 2.87/1.45  tff(c_446, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_445, c_441])).
% 2.87/1.45  tff(c_469, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_468, c_446])).
% 2.87/1.45  tff(c_476, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_12, c_469])).
% 2.87/1.45  tff(c_480, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_118, c_476])).
% 2.87/1.45  tff(c_481, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_42])).
% 2.87/1.45  tff(c_828, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k9_relat_1('#skF_3', '#skF_2'))!=k1_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_827, c_481])).
% 2.87/1.45  tff(c_829, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k2_relat_1('#skF_3'))!=k1_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_553, c_828])).
% 2.87/1.45  tff(c_917, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))!=k1_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_916, c_829])).
% 2.87/1.45  tff(c_957, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_951, c_917])).
% 2.87/1.45  tff(c_960, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_16, c_957])).
% 2.87/1.45  tff(c_964, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_489, c_960])).
% 2.87/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.87/1.45  
% 2.87/1.45  Inference rules
% 2.87/1.45  ----------------------
% 2.87/1.45  #Ref     : 0
% 2.87/1.45  #Sup     : 204
% 2.87/1.45  #Fact    : 0
% 2.87/1.45  #Define  : 0
% 2.87/1.45  #Split   : 1
% 2.87/1.45  #Chain   : 0
% 2.87/1.45  #Close   : 0
% 2.87/1.45  
% 2.87/1.45  Ordering : KBO
% 2.87/1.45  
% 2.87/1.45  Simplification rules
% 2.87/1.45  ----------------------
% 2.87/1.45  #Subsume      : 7
% 2.87/1.45  #Demod        : 148
% 2.87/1.45  #Tautology    : 122
% 2.87/1.45  #SimpNegUnit  : 0
% 2.87/1.45  #BackRed      : 8
% 2.87/1.45  
% 2.87/1.45  #Partial instantiations: 0
% 2.87/1.45  #Strategies tried      : 1
% 2.87/1.45  
% 2.87/1.45  Timing (in seconds)
% 2.87/1.45  ----------------------
% 2.87/1.45  Preprocessing        : 0.33
% 2.87/1.45  Parsing              : 0.18
% 2.87/1.45  CNF conversion       : 0.02
% 2.87/1.45  Main loop            : 0.37
% 2.87/1.45  Inferencing          : 0.15
% 2.87/1.45  Reduction            : 0.12
% 2.87/1.45  Demodulation         : 0.09
% 2.87/1.45  BG Simplification    : 0.02
% 2.87/1.45  Subsumption          : 0.05
% 2.87/1.45  Abstraction          : 0.02
% 2.87/1.45  MUC search           : 0.00
% 2.87/1.45  Cooper               : 0.00
% 2.87/1.45  Total                : 0.74
% 2.87/1.45  Index Insertion      : 0.00
% 2.87/1.45  Index Deletion       : 0.00
% 2.87/1.45  Index Matching       : 0.00
% 2.87/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
