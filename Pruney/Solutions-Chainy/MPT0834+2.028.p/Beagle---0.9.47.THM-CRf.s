%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:53 EST 2020

% Result     : Theorem 3.24s
% Output     : CNFRefutation 3.27s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 247 expanded)
%              Number of leaves         :   40 (  99 expanded)
%              Depth                    :   13
%              Number of atoms          :  160 ( 441 expanded)
%              Number of equality atoms :   54 ( 121 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(f_109,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
          & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_96,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_50,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_92,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_102,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => ( r1_tarski(k1_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relset_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k10_relat_1(B,A) = k10_relat_1(B,k3_xboole_0(k2_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_relat_1)).

tff(c_44,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_521,plain,(
    ! [A_131,B_132,C_133,D_134] :
      ( k8_relset_1(A_131,B_132,C_133,D_134) = k10_relat_1(C_133,D_134)
      | ~ m1_subset_1(C_133,k1_zfmisc_1(k2_zfmisc_1(A_131,B_132))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_524,plain,(
    ! [D_134] : k8_relset_1('#skF_1','#skF_2','#skF_3',D_134) = k10_relat_1('#skF_3',D_134) ),
    inference(resolution,[status(thm)],[c_44,c_521])).

tff(c_463,plain,(
    ! [A_121,B_122,C_123] :
      ( k1_relset_1(A_121,B_122,C_123) = k1_relat_1(C_123)
      | ~ m1_subset_1(C_123,k1_zfmisc_1(k2_zfmisc_1(A_121,B_122))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_467,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_463])).

tff(c_16,plain,(
    ! [A_10,B_11] : v1_relat_1(k2_zfmisc_1(A_10,B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_62,plain,(
    ! [B_49,A_50] :
      ( v1_relat_1(B_49)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(A_50))
      | ~ v1_relat_1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_65,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_44,c_62])).

tff(c_68,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_65])).

tff(c_99,plain,(
    ! [C_62,A_63,B_64] :
      ( v4_relat_1(C_62,A_63)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_103,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_99])).

tff(c_24,plain,(
    ! [B_19,A_18] :
      ( k7_relat_1(B_19,A_18) = B_19
      | ~ v4_relat_1(B_19,A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_118,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_103,c_24])).

tff(c_121,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_118])).

tff(c_18,plain,(
    ! [B_13,A_12] :
      ( k2_relat_1(k7_relat_1(B_13,A_12)) = k9_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_125,plain,
    ( k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_18])).

tff(c_129,plain,(
    k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_125])).

tff(c_325,plain,(
    ! [A_96,B_97,C_98,D_99] :
      ( k7_relset_1(A_96,B_97,C_98,D_99) = k9_relat_1(C_98,D_99)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_328,plain,(
    ! [D_99] : k7_relset_1('#skF_1','#skF_2','#skF_3',D_99) = k9_relat_1('#skF_3',D_99) ),
    inference(resolution,[status(thm)],[c_44,c_325])).

tff(c_209,plain,(
    ! [A_76,B_77,C_78] :
      ( k2_relset_1(A_76,B_77,C_78) = k2_relat_1(C_78)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_213,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_209])).

tff(c_42,plain,
    ( k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != k1_relset_1('#skF_1','#skF_2','#skF_3')
    | k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_84,plain,(
    k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_214,plain,(
    k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_213,c_84])).

tff(c_329,plain,(
    k9_relat_1('#skF_3','#skF_1') != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_328,c_214])).

tff(c_332,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_329])).

tff(c_333,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != k1_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_468,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_467,c_333])).

tff(c_525,plain,(
    k10_relat_1('#skF_3','#skF_2') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_524,c_468])).

tff(c_374,plain,(
    ! [C_110,B_111,A_112] :
      ( v5_relat_1(C_110,B_111)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(A_112,B_111))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_378,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_374])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_606,plain,(
    ! [D_146,B_147,C_148,A_149] :
      ( m1_subset_1(D_146,k1_zfmisc_1(k2_zfmisc_1(B_147,C_148)))
      | ~ r1_tarski(k1_relat_1(D_146),B_147)
      | ~ m1_subset_1(D_146,k1_zfmisc_1(k2_zfmisc_1(A_149,C_148))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_610,plain,(
    ! [B_150] :
      ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(B_150,'#skF_2')))
      | ~ r1_tarski(k1_relat_1('#skF_3'),B_150) ) ),
    inference(resolution,[status(thm)],[c_44,c_606])).

tff(c_30,plain,(
    ! [C_24,A_22,B_23] :
      ( v4_relat_1(C_24,A_22)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_643,plain,(
    ! [B_151] :
      ( v4_relat_1('#skF_3',B_151)
      | ~ r1_tarski(k1_relat_1('#skF_3'),B_151) ) ),
    inference(resolution,[status(thm)],[c_610,c_30])).

tff(c_653,plain,(
    v4_relat_1('#skF_3',k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_6,c_643])).

tff(c_656,plain,
    ( k7_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_653,c_24])).

tff(c_659,plain,(
    k7_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_656])).

tff(c_666,plain,
    ( k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_659,c_18])).

tff(c_672,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_666])).

tff(c_26,plain,(
    ! [A_20,B_21] :
      ( r1_tarski(A_20,k10_relat_1(B_21,k9_relat_1(B_21,A_20)))
      | ~ r1_tarski(A_20,k1_relat_1(B_21))
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_20,plain,(
    ! [B_15,A_14] :
      ( r1_tarski(k10_relat_1(B_15,A_14),k1_relat_1(B_15))
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_74,plain,(
    ! [B_53,A_54] :
      ( B_53 = A_54
      | ~ r1_tarski(B_53,A_54)
      | ~ r1_tarski(A_54,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_535,plain,(
    ! [B_136,A_137] :
      ( k10_relat_1(B_136,A_137) = k1_relat_1(B_136)
      | ~ r1_tarski(k1_relat_1(B_136),k10_relat_1(B_136,A_137))
      | ~ v1_relat_1(B_136) ) ),
    inference(resolution,[status(thm)],[c_20,c_74])).

tff(c_539,plain,(
    ! [B_21] :
      ( k10_relat_1(B_21,k9_relat_1(B_21,k1_relat_1(B_21))) = k1_relat_1(B_21)
      | ~ r1_tarski(k1_relat_1(B_21),k1_relat_1(B_21))
      | ~ v1_relat_1(B_21) ) ),
    inference(resolution,[status(thm)],[c_26,c_535])).

tff(c_545,plain,(
    ! [B_21] :
      ( k10_relat_1(B_21,k9_relat_1(B_21,k1_relat_1(B_21))) = k1_relat_1(B_21)
      | ~ v1_relat_1(B_21) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_539])).

tff(c_718,plain,
    ( k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_672,c_545])).

tff(c_729,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_718])).

tff(c_359,plain,(
    ! [C_107,A_108,B_109] :
      ( v4_relat_1(C_107,A_108)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(A_108,B_109))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_363,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_359])).

tff(c_366,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_363,c_24])).

tff(c_369,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_366])).

tff(c_379,plain,(
    ! [B_113,A_114] :
      ( k2_relat_1(k7_relat_1(B_113,A_114)) = k9_relat_1(B_113,A_114)
      | ~ v1_relat_1(B_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_397,plain,
    ( k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_369,c_379])).

tff(c_401,plain,(
    k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_397])).

tff(c_14,plain,(
    ! [B_9,A_8] :
      ( r1_tarski(k2_relat_1(B_9),A_8)
      | ~ v5_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_793,plain,(
    ! [B_158,A_159,A_160] :
      ( r1_tarski(k9_relat_1(B_158,A_159),A_160)
      | ~ v5_relat_1(k7_relat_1(B_158,A_159),A_160)
      | ~ v1_relat_1(k7_relat_1(B_158,A_159))
      | ~ v1_relat_1(B_158) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_379,c_14])).

tff(c_802,plain,(
    ! [A_160] :
      ( r1_tarski(k9_relat_1('#skF_3','#skF_1'),A_160)
      | ~ v5_relat_1('#skF_3',A_160)
      | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_369,c_793])).

tff(c_814,plain,(
    ! [A_161] :
      ( r1_tarski(k2_relat_1('#skF_3'),A_161)
      | ~ v5_relat_1('#skF_3',A_161) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_68,c_369,c_401,c_802])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = A_3
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_860,plain,(
    ! [A_166] :
      ( k3_xboole_0(k2_relat_1('#skF_3'),A_166) = k2_relat_1('#skF_3')
      | ~ v5_relat_1('#skF_3',A_166) ) ),
    inference(resolution,[status(thm)],[c_814,c_8])).

tff(c_22,plain,(
    ! [B_17,A_16] :
      ( k10_relat_1(B_17,k3_xboole_0(k2_relat_1(B_17),A_16)) = k10_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_873,plain,(
    ! [A_166] :
      ( k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k10_relat_1('#skF_3',A_166)
      | ~ v1_relat_1('#skF_3')
      | ~ v5_relat_1('#skF_3',A_166) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_860,c_22])).

tff(c_911,plain,(
    ! [A_167] :
      ( k10_relat_1('#skF_3',A_167) = k1_relat_1('#skF_3')
      | ~ v5_relat_1('#skF_3',A_167) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_729,c_873])).

tff(c_917,plain,(
    k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_378,c_911])).

tff(c_927,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_525,c_917])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:59:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.24/1.52  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.27/1.53  
% 3.27/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.27/1.53  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.27/1.53  
% 3.27/1.53  %Foreground sorts:
% 3.27/1.53  
% 3.27/1.53  
% 3.27/1.53  %Background operators:
% 3.27/1.53  
% 3.27/1.53  
% 3.27/1.53  %Foreground operators:
% 3.27/1.53  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.27/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.27/1.53  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.27/1.53  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.27/1.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.27/1.53  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.27/1.53  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.27/1.53  tff('#skF_2', type, '#skF_2': $i).
% 3.27/1.53  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.27/1.53  tff('#skF_3', type, '#skF_3': $i).
% 3.27/1.53  tff('#skF_1', type, '#skF_1': $i).
% 3.27/1.53  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.27/1.53  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.27/1.53  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.27/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.27/1.54  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.27/1.54  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.27/1.54  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.27/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.27/1.54  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.27/1.54  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.27/1.54  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.27/1.54  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.27/1.54  
% 3.27/1.55  tff(f_109, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_relset_1)).
% 3.27/1.55  tff(f_96, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.27/1.55  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.27/1.55  tff(f_50, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.27/1.55  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.27/1.55  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.27/1.55  tff(f_68, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 3.27/1.55  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 3.27/1.55  tff(f_92, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.27/1.55  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.27/1.55  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.27/1.55  tff(f_102, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (r1_tarski(k1_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_relset_1)).
% 3.27/1.55  tff(f_74, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_funct_1)).
% 3.27/1.55  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_relat_1)).
% 3.27/1.55  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 3.27/1.55  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.27/1.55  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => (k10_relat_1(B, A) = k10_relat_1(B, k3_xboole_0(k2_relat_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t168_relat_1)).
% 3.27/1.55  tff(c_44, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.27/1.55  tff(c_521, plain, (![A_131, B_132, C_133, D_134]: (k8_relset_1(A_131, B_132, C_133, D_134)=k10_relat_1(C_133, D_134) | ~m1_subset_1(C_133, k1_zfmisc_1(k2_zfmisc_1(A_131, B_132))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.27/1.55  tff(c_524, plain, (![D_134]: (k8_relset_1('#skF_1', '#skF_2', '#skF_3', D_134)=k10_relat_1('#skF_3', D_134))), inference(resolution, [status(thm)], [c_44, c_521])).
% 3.27/1.55  tff(c_463, plain, (![A_121, B_122, C_123]: (k1_relset_1(A_121, B_122, C_123)=k1_relat_1(C_123) | ~m1_subset_1(C_123, k1_zfmisc_1(k2_zfmisc_1(A_121, B_122))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.27/1.55  tff(c_467, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_463])).
% 3.27/1.55  tff(c_16, plain, (![A_10, B_11]: (v1_relat_1(k2_zfmisc_1(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.27/1.55  tff(c_62, plain, (![B_49, A_50]: (v1_relat_1(B_49) | ~m1_subset_1(B_49, k1_zfmisc_1(A_50)) | ~v1_relat_1(A_50))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.27/1.55  tff(c_65, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_44, c_62])).
% 3.27/1.55  tff(c_68, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_65])).
% 3.27/1.55  tff(c_99, plain, (![C_62, A_63, B_64]: (v4_relat_1(C_62, A_63) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.27/1.55  tff(c_103, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_44, c_99])).
% 3.27/1.55  tff(c_24, plain, (![B_19, A_18]: (k7_relat_1(B_19, A_18)=B_19 | ~v4_relat_1(B_19, A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.27/1.55  tff(c_118, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_103, c_24])).
% 3.27/1.55  tff(c_121, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_118])).
% 3.27/1.55  tff(c_18, plain, (![B_13, A_12]: (k2_relat_1(k7_relat_1(B_13, A_12))=k9_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.27/1.55  tff(c_125, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_121, c_18])).
% 3.27/1.55  tff(c_129, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_125])).
% 3.27/1.55  tff(c_325, plain, (![A_96, B_97, C_98, D_99]: (k7_relset_1(A_96, B_97, C_98, D_99)=k9_relat_1(C_98, D_99) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.27/1.55  tff(c_328, plain, (![D_99]: (k7_relset_1('#skF_1', '#skF_2', '#skF_3', D_99)=k9_relat_1('#skF_3', D_99))), inference(resolution, [status(thm)], [c_44, c_325])).
% 3.27/1.55  tff(c_209, plain, (![A_76, B_77, C_78]: (k2_relset_1(A_76, B_77, C_78)=k2_relat_1(C_78) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.27/1.55  tff(c_213, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_209])).
% 3.27/1.55  tff(c_42, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!=k1_relset_1('#skF_1', '#skF_2', '#skF_3') | k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.27/1.55  tff(c_84, plain, (k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_42])).
% 3.27/1.55  tff(c_214, plain, (k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_213, c_84])).
% 3.27/1.55  tff(c_329, plain, (k9_relat_1('#skF_3', '#skF_1')!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_328, c_214])).
% 3.27/1.55  tff(c_332, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_129, c_329])).
% 3.27/1.55  tff(c_333, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!=k1_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_42])).
% 3.27/1.55  tff(c_468, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_467, c_333])).
% 3.27/1.55  tff(c_525, plain, (k10_relat_1('#skF_3', '#skF_2')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_524, c_468])).
% 3.27/1.55  tff(c_374, plain, (![C_110, B_111, A_112]: (v5_relat_1(C_110, B_111) | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(A_112, B_111))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.27/1.55  tff(c_378, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_44, c_374])).
% 3.27/1.55  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.27/1.55  tff(c_606, plain, (![D_146, B_147, C_148, A_149]: (m1_subset_1(D_146, k1_zfmisc_1(k2_zfmisc_1(B_147, C_148))) | ~r1_tarski(k1_relat_1(D_146), B_147) | ~m1_subset_1(D_146, k1_zfmisc_1(k2_zfmisc_1(A_149, C_148))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.27/1.55  tff(c_610, plain, (![B_150]: (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(B_150, '#skF_2'))) | ~r1_tarski(k1_relat_1('#skF_3'), B_150))), inference(resolution, [status(thm)], [c_44, c_606])).
% 3.27/1.55  tff(c_30, plain, (![C_24, A_22, B_23]: (v4_relat_1(C_24, A_22) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.27/1.55  tff(c_643, plain, (![B_151]: (v4_relat_1('#skF_3', B_151) | ~r1_tarski(k1_relat_1('#skF_3'), B_151))), inference(resolution, [status(thm)], [c_610, c_30])).
% 3.27/1.55  tff(c_653, plain, (v4_relat_1('#skF_3', k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_6, c_643])).
% 3.27/1.55  tff(c_656, plain, (k7_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_653, c_24])).
% 3.27/1.55  tff(c_659, plain, (k7_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_656])).
% 3.27/1.55  tff(c_666, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_659, c_18])).
% 3.27/1.55  tff(c_672, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_666])).
% 3.27/1.55  tff(c_26, plain, (![A_20, B_21]: (r1_tarski(A_20, k10_relat_1(B_21, k9_relat_1(B_21, A_20))) | ~r1_tarski(A_20, k1_relat_1(B_21)) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.27/1.55  tff(c_20, plain, (![B_15, A_14]: (r1_tarski(k10_relat_1(B_15, A_14), k1_relat_1(B_15)) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.27/1.55  tff(c_74, plain, (![B_53, A_54]: (B_53=A_54 | ~r1_tarski(B_53, A_54) | ~r1_tarski(A_54, B_53))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.27/1.55  tff(c_535, plain, (![B_136, A_137]: (k10_relat_1(B_136, A_137)=k1_relat_1(B_136) | ~r1_tarski(k1_relat_1(B_136), k10_relat_1(B_136, A_137)) | ~v1_relat_1(B_136))), inference(resolution, [status(thm)], [c_20, c_74])).
% 3.27/1.55  tff(c_539, plain, (![B_21]: (k10_relat_1(B_21, k9_relat_1(B_21, k1_relat_1(B_21)))=k1_relat_1(B_21) | ~r1_tarski(k1_relat_1(B_21), k1_relat_1(B_21)) | ~v1_relat_1(B_21))), inference(resolution, [status(thm)], [c_26, c_535])).
% 3.27/1.55  tff(c_545, plain, (![B_21]: (k10_relat_1(B_21, k9_relat_1(B_21, k1_relat_1(B_21)))=k1_relat_1(B_21) | ~v1_relat_1(B_21))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_539])).
% 3.27/1.55  tff(c_718, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_672, c_545])).
% 3.27/1.55  tff(c_729, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_718])).
% 3.27/1.55  tff(c_359, plain, (![C_107, A_108, B_109]: (v4_relat_1(C_107, A_108) | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1(A_108, B_109))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.27/1.55  tff(c_363, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_44, c_359])).
% 3.27/1.55  tff(c_366, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_363, c_24])).
% 3.27/1.55  tff(c_369, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_366])).
% 3.27/1.55  tff(c_379, plain, (![B_113, A_114]: (k2_relat_1(k7_relat_1(B_113, A_114))=k9_relat_1(B_113, A_114) | ~v1_relat_1(B_113))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.27/1.55  tff(c_397, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_369, c_379])).
% 3.27/1.55  tff(c_401, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_397])).
% 3.27/1.55  tff(c_14, plain, (![B_9, A_8]: (r1_tarski(k2_relat_1(B_9), A_8) | ~v5_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.27/1.55  tff(c_793, plain, (![B_158, A_159, A_160]: (r1_tarski(k9_relat_1(B_158, A_159), A_160) | ~v5_relat_1(k7_relat_1(B_158, A_159), A_160) | ~v1_relat_1(k7_relat_1(B_158, A_159)) | ~v1_relat_1(B_158))), inference(superposition, [status(thm), theory('equality')], [c_379, c_14])).
% 3.27/1.55  tff(c_802, plain, (![A_160]: (r1_tarski(k9_relat_1('#skF_3', '#skF_1'), A_160) | ~v5_relat_1('#skF_3', A_160) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_369, c_793])).
% 3.27/1.55  tff(c_814, plain, (![A_161]: (r1_tarski(k2_relat_1('#skF_3'), A_161) | ~v5_relat_1('#skF_3', A_161))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_68, c_369, c_401, c_802])).
% 3.27/1.55  tff(c_8, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=A_3 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.27/1.55  tff(c_860, plain, (![A_166]: (k3_xboole_0(k2_relat_1('#skF_3'), A_166)=k2_relat_1('#skF_3') | ~v5_relat_1('#skF_3', A_166))), inference(resolution, [status(thm)], [c_814, c_8])).
% 3.27/1.55  tff(c_22, plain, (![B_17, A_16]: (k10_relat_1(B_17, k3_xboole_0(k2_relat_1(B_17), A_16))=k10_relat_1(B_17, A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.27/1.55  tff(c_873, plain, (![A_166]: (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k10_relat_1('#skF_3', A_166) | ~v1_relat_1('#skF_3') | ~v5_relat_1('#skF_3', A_166))), inference(superposition, [status(thm), theory('equality')], [c_860, c_22])).
% 3.27/1.55  tff(c_911, plain, (![A_167]: (k10_relat_1('#skF_3', A_167)=k1_relat_1('#skF_3') | ~v5_relat_1('#skF_3', A_167))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_729, c_873])).
% 3.27/1.56  tff(c_917, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_378, c_911])).
% 3.27/1.56  tff(c_927, plain, $false, inference(negUnitSimplification, [status(thm)], [c_525, c_917])).
% 3.27/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.27/1.56  
% 3.27/1.56  Inference rules
% 3.27/1.56  ----------------------
% 3.27/1.56  #Ref     : 0
% 3.27/1.56  #Sup     : 201
% 3.27/1.56  #Fact    : 0
% 3.27/1.56  #Define  : 0
% 3.27/1.56  #Split   : 3
% 3.27/1.56  #Chain   : 0
% 3.27/1.56  #Close   : 0
% 3.27/1.56  
% 3.27/1.56  Ordering : KBO
% 3.27/1.56  
% 3.27/1.56  Simplification rules
% 3.27/1.56  ----------------------
% 3.27/1.56  #Subsume      : 9
% 3.27/1.56  #Demod        : 99
% 3.27/1.56  #Tautology    : 107
% 3.27/1.56  #SimpNegUnit  : 1
% 3.27/1.56  #BackRed      : 6
% 3.27/1.56  
% 3.27/1.56  #Partial instantiations: 0
% 3.27/1.56  #Strategies tried      : 1
% 3.27/1.56  
% 3.27/1.56  Timing (in seconds)
% 3.27/1.56  ----------------------
% 3.27/1.56  Preprocessing        : 0.35
% 3.27/1.56  Parsing              : 0.19
% 3.27/1.56  CNF conversion       : 0.02
% 3.27/1.56  Main loop            : 0.38
% 3.27/1.56  Inferencing          : 0.15
% 3.27/1.56  Reduction            : 0.12
% 3.27/1.56  Demodulation         : 0.08
% 3.27/1.56  BG Simplification    : 0.02
% 3.27/1.56  Subsumption          : 0.06
% 3.27/1.56  Abstraction          : 0.02
% 3.27/1.56  MUC search           : 0.00
% 3.27/1.56  Cooper               : 0.00
% 3.27/1.56  Total                : 0.77
% 3.27/1.56  Index Insertion      : 0.00
% 3.27/1.56  Index Deletion       : 0.00
% 3.27/1.56  Index Matching       : 0.00
% 3.27/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
