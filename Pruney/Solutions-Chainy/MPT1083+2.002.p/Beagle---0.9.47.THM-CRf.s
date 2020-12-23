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
% DateTime   : Thu Dec  3 10:18:17 EST 2020

% Result     : Theorem 2.99s
% Output     : CNFRefutation 2.99s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 234 expanded)
%              Number of leaves         :   35 (  94 expanded)
%              Depth                    :   10
%              Number of atoms          :  198 ( 663 expanded)
%              Number of equality atoms :   50 ( 134 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_147,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ( v1_funct_1(B)
              & v1_funct_2(B,A,A)
              & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
           => ! [C] :
                ( ( v1_relat_1(C)
                  & v5_relat_1(C,A)
                  & v1_funct_1(C) )
               => k1_relat_1(k5_relat_1(C,B)) = k1_relat_1(C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t200_funct_2)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_103,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_127,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_115,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( B = k1_xboole_0
         => A = k1_xboole_0 )
       => k8_relset_1(A,B,C,B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_2)).

tff(f_61,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_60,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_54,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_73,plain,(
    ! [C_38,A_39,B_40] :
      ( v1_relat_1(C_38)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1(A_39,B_40))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_77,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_73])).

tff(c_89,plain,(
    ! [C_43,A_44,B_45] :
      ( v4_relat_1(C_43,A_44)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_93,plain,(
    v4_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_89])).

tff(c_105,plain,(
    ! [B_52,A_53] :
      ( k1_relat_1(B_52) = A_53
      | ~ v1_partfun1(B_52,A_53)
      | ~ v4_relat_1(B_52,A_53)
      | ~ v1_relat_1(B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_108,plain,
    ( k1_relat_1('#skF_2') = '#skF_1'
    | ~ v1_partfun1('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_93,c_105])).

tff(c_111,plain,
    ( k1_relat_1('#skF_2') = '#skF_1'
    | ~ v1_partfun1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_108])).

tff(c_112,plain,(
    ~ v1_partfun1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_111])).

tff(c_58,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_56,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_193,plain,(
    ! [C_69,A_70,B_71] :
      ( v1_partfun1(C_69,A_70)
      | ~ v1_funct_2(C_69,A_70,B_71)
      | ~ v1_funct_1(C_69)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71)))
      | v1_xboole_0(B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_199,plain,
    ( v1_partfun1('#skF_2','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_193])).

tff(c_203,plain,
    ( v1_partfun1('#skF_2','#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_199])).

tff(c_205,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_112,c_203])).

tff(c_206,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_111])).

tff(c_12,plain,(
    ! [A_6] :
      ( k1_relat_1(A_6) != k1_xboole_0
      | k1_xboole_0 = A_6
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_84,plain,
    ( k1_relat_1('#skF_2') != k1_xboole_0
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_77,c_12])).

tff(c_86,plain,(
    k1_relat_1('#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_208,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_206,c_86])).

tff(c_52,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_218,plain,(
    ! [A_72,B_73] :
      ( k10_relat_1(A_72,k1_relat_1(B_73)) = k1_relat_1(k5_relat_1(A_72,B_73))
      | ~ v1_relat_1(B_73)
      | ~ v1_relat_1(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_227,plain,(
    ! [A_72] :
      ( k1_relat_1(k5_relat_1(A_72,'#skF_2')) = k10_relat_1(A_72,'#skF_1')
      | ~ v1_relat_1('#skF_2')
      | ~ v1_relat_1(A_72) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_206,c_218])).

tff(c_233,plain,(
    ! [A_74] :
      ( k1_relat_1(k5_relat_1(A_74,'#skF_2')) = k10_relat_1(A_74,'#skF_1')
      | ~ v1_relat_1(A_74) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_227])).

tff(c_46,plain,(
    k1_relat_1(k5_relat_1('#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_245,plain,
    ( k10_relat_1('#skF_3','#skF_1') != k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_233,c_46])).

tff(c_251,plain,(
    k10_relat_1('#skF_3','#skF_1') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_245])).

tff(c_50,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_48,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_6,plain,(
    ! [B_2,A_1] :
      ( r1_tarski(k2_relat_1(B_2),A_1)
      | ~ v5_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_42,plain,(
    ! [B_31,A_30] :
      ( v1_funct_2(B_31,k1_relat_1(B_31),A_30)
      | ~ r1_tarski(k2_relat_1(B_31),A_30)
      | ~ v1_funct_1(B_31)
      | ~ v1_relat_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_40,plain,(
    ! [B_31,A_30] :
      ( m1_subset_1(B_31,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_31),A_30)))
      | ~ r1_tarski(k2_relat_1(B_31),A_30)
      | ~ v1_funct_1(B_31)
      | ~ v1_relat_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_487,plain,(
    ! [B_118,A_119,C_120] :
      ( k1_xboole_0 = B_118
      | k8_relset_1(A_119,B_118,C_120,B_118) = A_119
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_zfmisc_1(A_119,B_118)))
      | ~ v1_funct_2(C_120,A_119,B_118)
      | ~ v1_funct_1(C_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_569,plain,(
    ! [A_131,B_132] :
      ( k1_xboole_0 = A_131
      | k8_relset_1(k1_relat_1(B_132),A_131,B_132,A_131) = k1_relat_1(B_132)
      | ~ v1_funct_2(B_132,k1_relat_1(B_132),A_131)
      | ~ r1_tarski(k2_relat_1(B_132),A_131)
      | ~ v1_funct_1(B_132)
      | ~ v1_relat_1(B_132) ) ),
    inference(resolution,[status(thm)],[c_40,c_487])).

tff(c_581,plain,(
    ! [A_133,B_134] :
      ( k1_xboole_0 = A_133
      | k8_relset_1(k1_relat_1(B_134),A_133,B_134,A_133) = k1_relat_1(B_134)
      | ~ r1_tarski(k2_relat_1(B_134),A_133)
      | ~ v1_funct_1(B_134)
      | ~ v1_relat_1(B_134) ) ),
    inference(resolution,[status(thm)],[c_42,c_569])).

tff(c_586,plain,(
    ! [A_135,B_136] :
      ( k1_xboole_0 = A_135
      | k8_relset_1(k1_relat_1(B_136),A_135,B_136,A_135) = k1_relat_1(B_136)
      | ~ v1_funct_1(B_136)
      | ~ v5_relat_1(B_136,A_135)
      | ~ v1_relat_1(B_136) ) ),
    inference(resolution,[status(thm)],[c_6,c_581])).

tff(c_284,plain,(
    ! [B_84,A_85] :
      ( m1_subset_1(B_84,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_84),A_85)))
      | ~ r1_tarski(k2_relat_1(B_84),A_85)
      | ~ v1_funct_1(B_84)
      | ~ v1_relat_1(B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_20,plain,(
    ! [A_13,B_14,C_15,D_16] :
      ( k8_relset_1(A_13,B_14,C_15,D_16) = k10_relat_1(C_15,D_16)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_393,plain,(
    ! [B_101,A_102,D_103] :
      ( k8_relset_1(k1_relat_1(B_101),A_102,B_101,D_103) = k10_relat_1(B_101,D_103)
      | ~ r1_tarski(k2_relat_1(B_101),A_102)
      | ~ v1_funct_1(B_101)
      | ~ v1_relat_1(B_101) ) ),
    inference(resolution,[status(thm)],[c_284,c_20])).

tff(c_396,plain,(
    ! [B_2,A_1,D_103] :
      ( k8_relset_1(k1_relat_1(B_2),A_1,B_2,D_103) = k10_relat_1(B_2,D_103)
      | ~ v1_funct_1(B_2)
      | ~ v5_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_393])).

tff(c_620,plain,(
    ! [B_138,A_139] :
      ( k10_relat_1(B_138,A_139) = k1_relat_1(B_138)
      | ~ v1_funct_1(B_138)
      | ~ v5_relat_1(B_138,A_139)
      | ~ v1_relat_1(B_138)
      | k1_xboole_0 = A_139
      | ~ v1_funct_1(B_138)
      | ~ v5_relat_1(B_138,A_139)
      | ~ v1_relat_1(B_138) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_586,c_396])).

tff(c_624,plain,
    ( k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3')
    | k1_xboole_0 = '#skF_1'
    | ~ v1_funct_1('#skF_3')
    | ~ v5_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_620])).

tff(c_631,plain,
    ( k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3')
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_624])).

tff(c_633,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_208,c_251,c_631])).

tff(c_634,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_635,plain,(
    k1_relat_1('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_646,plain,(
    k1_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_634,c_635])).

tff(c_684,plain,(
    ! [C_149,A_150,B_151] :
      ( v4_relat_1(C_149,A_150)
      | ~ m1_subset_1(C_149,k1_zfmisc_1(k2_zfmisc_1(A_150,B_151))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_688,plain,(
    v4_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_684])).

tff(c_696,plain,(
    ! [B_153,A_154] :
      ( k1_relat_1(B_153) = A_154
      | ~ v1_partfun1(B_153,A_154)
      | ~ v4_relat_1(B_153,A_154)
      | ~ v1_relat_1(B_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_699,plain,
    ( k1_relat_1('#skF_2') = '#skF_1'
    | ~ v1_partfun1('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_688,c_696])).

tff(c_702,plain,
    ( '#skF_2' = '#skF_1'
    | ~ v1_partfun1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_646,c_699])).

tff(c_703,plain,(
    ~ v1_partfun1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_702])).

tff(c_841,plain,(
    ! [C_173,A_174,B_175] :
      ( v1_partfun1(C_173,A_174)
      | ~ v1_funct_2(C_173,A_174,B_175)
      | ~ v1_funct_1(C_173)
      | ~ m1_subset_1(C_173,k1_zfmisc_1(k2_zfmisc_1(A_174,B_175)))
      | v1_xboole_0(B_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_847,plain,
    ( v1_partfun1('#skF_2','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_841])).

tff(c_851,plain,
    ( v1_partfun1('#skF_2','#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_847])).

tff(c_853,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_703,c_851])).

tff(c_854,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_702])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_640,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_634,c_2])).

tff(c_864,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_854,c_640])).

tff(c_872,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_864])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:19:40 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.99/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.99/1.43  
% 2.99/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.99/1.43  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.99/1.43  
% 2.99/1.43  %Foreground sorts:
% 2.99/1.43  
% 2.99/1.43  
% 2.99/1.43  %Background operators:
% 2.99/1.43  
% 2.99/1.43  
% 2.99/1.43  %Foreground operators:
% 2.99/1.43  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.99/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.99/1.43  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.99/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.99/1.43  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.99/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.99/1.43  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.99/1.43  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.99/1.43  tff('#skF_2', type, '#skF_2': $i).
% 2.99/1.43  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.99/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.99/1.43  tff('#skF_1', type, '#skF_1': $i).
% 2.99/1.43  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.99/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.99/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.99/1.43  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.99/1.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.99/1.43  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.99/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.99/1.43  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.99/1.43  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.99/1.43  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.99/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.99/1.43  
% 2.99/1.45  tff(f_147, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: (((v1_relat_1(C) & v5_relat_1(C, A)) & v1_funct_1(C)) => (k1_relat_1(k5_relat_1(C, B)) = k1_relat_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t200_funct_2)).
% 2.99/1.45  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.99/1.45  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.99/1.45  tff(f_103, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 2.99/1.45  tff(f_75, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 2.99/1.45  tff(f_47, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 2.99/1.45  tff(f_39, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 2.99/1.45  tff(f_32, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 2.99/1.45  tff(f_127, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 2.99/1.45  tff(f_115, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => (k8_relset_1(A, B, C, B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_funct_2)).
% 2.99/1.45  tff(f_61, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.99/1.45  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.99/1.45  tff(c_60, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_147])).
% 2.99/1.45  tff(c_54, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_147])).
% 2.99/1.45  tff(c_73, plain, (![C_38, A_39, B_40]: (v1_relat_1(C_38) | ~m1_subset_1(C_38, k1_zfmisc_1(k2_zfmisc_1(A_39, B_40))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.99/1.45  tff(c_77, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_54, c_73])).
% 2.99/1.45  tff(c_89, plain, (![C_43, A_44, B_45]: (v4_relat_1(C_43, A_44) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.99/1.45  tff(c_93, plain, (v4_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_54, c_89])).
% 2.99/1.45  tff(c_105, plain, (![B_52, A_53]: (k1_relat_1(B_52)=A_53 | ~v1_partfun1(B_52, A_53) | ~v4_relat_1(B_52, A_53) | ~v1_relat_1(B_52))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.99/1.45  tff(c_108, plain, (k1_relat_1('#skF_2')='#skF_1' | ~v1_partfun1('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_93, c_105])).
% 2.99/1.45  tff(c_111, plain, (k1_relat_1('#skF_2')='#skF_1' | ~v1_partfun1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_77, c_108])).
% 2.99/1.45  tff(c_112, plain, (~v1_partfun1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_111])).
% 2.99/1.45  tff(c_58, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_147])).
% 2.99/1.45  tff(c_56, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_147])).
% 2.99/1.45  tff(c_193, plain, (![C_69, A_70, B_71]: (v1_partfun1(C_69, A_70) | ~v1_funct_2(C_69, A_70, B_71) | ~v1_funct_1(C_69) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))) | v1_xboole_0(B_71))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.99/1.45  tff(c_199, plain, (v1_partfun1('#skF_2', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_54, c_193])).
% 2.99/1.45  tff(c_203, plain, (v1_partfun1('#skF_2', '#skF_1') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_199])).
% 2.99/1.45  tff(c_205, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_112, c_203])).
% 2.99/1.45  tff(c_206, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_111])).
% 2.99/1.45  tff(c_12, plain, (![A_6]: (k1_relat_1(A_6)!=k1_xboole_0 | k1_xboole_0=A_6 | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.99/1.45  tff(c_84, plain, (k1_relat_1('#skF_2')!=k1_xboole_0 | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_77, c_12])).
% 2.99/1.45  tff(c_86, plain, (k1_relat_1('#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_84])).
% 2.99/1.45  tff(c_208, plain, (k1_xboole_0!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_206, c_86])).
% 2.99/1.45  tff(c_52, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_147])).
% 2.99/1.45  tff(c_218, plain, (![A_72, B_73]: (k10_relat_1(A_72, k1_relat_1(B_73))=k1_relat_1(k5_relat_1(A_72, B_73)) | ~v1_relat_1(B_73) | ~v1_relat_1(A_72))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.99/1.45  tff(c_227, plain, (![A_72]: (k1_relat_1(k5_relat_1(A_72, '#skF_2'))=k10_relat_1(A_72, '#skF_1') | ~v1_relat_1('#skF_2') | ~v1_relat_1(A_72))), inference(superposition, [status(thm), theory('equality')], [c_206, c_218])).
% 2.99/1.45  tff(c_233, plain, (![A_74]: (k1_relat_1(k5_relat_1(A_74, '#skF_2'))=k10_relat_1(A_74, '#skF_1') | ~v1_relat_1(A_74))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_227])).
% 2.99/1.45  tff(c_46, plain, (k1_relat_1(k5_relat_1('#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_147])).
% 2.99/1.45  tff(c_245, plain, (k10_relat_1('#skF_3', '#skF_1')!=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_233, c_46])).
% 2.99/1.45  tff(c_251, plain, (k10_relat_1('#skF_3', '#skF_1')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_245])).
% 2.99/1.45  tff(c_50, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_147])).
% 2.99/1.45  tff(c_48, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_147])).
% 2.99/1.45  tff(c_6, plain, (![B_2, A_1]: (r1_tarski(k2_relat_1(B_2), A_1) | ~v5_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.99/1.45  tff(c_42, plain, (![B_31, A_30]: (v1_funct_2(B_31, k1_relat_1(B_31), A_30) | ~r1_tarski(k2_relat_1(B_31), A_30) | ~v1_funct_1(B_31) | ~v1_relat_1(B_31))), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.99/1.45  tff(c_40, plain, (![B_31, A_30]: (m1_subset_1(B_31, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_31), A_30))) | ~r1_tarski(k2_relat_1(B_31), A_30) | ~v1_funct_1(B_31) | ~v1_relat_1(B_31))), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.99/1.45  tff(c_487, plain, (![B_118, A_119, C_120]: (k1_xboole_0=B_118 | k8_relset_1(A_119, B_118, C_120, B_118)=A_119 | ~m1_subset_1(C_120, k1_zfmisc_1(k2_zfmisc_1(A_119, B_118))) | ~v1_funct_2(C_120, A_119, B_118) | ~v1_funct_1(C_120))), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.99/1.45  tff(c_569, plain, (![A_131, B_132]: (k1_xboole_0=A_131 | k8_relset_1(k1_relat_1(B_132), A_131, B_132, A_131)=k1_relat_1(B_132) | ~v1_funct_2(B_132, k1_relat_1(B_132), A_131) | ~r1_tarski(k2_relat_1(B_132), A_131) | ~v1_funct_1(B_132) | ~v1_relat_1(B_132))), inference(resolution, [status(thm)], [c_40, c_487])).
% 2.99/1.45  tff(c_581, plain, (![A_133, B_134]: (k1_xboole_0=A_133 | k8_relset_1(k1_relat_1(B_134), A_133, B_134, A_133)=k1_relat_1(B_134) | ~r1_tarski(k2_relat_1(B_134), A_133) | ~v1_funct_1(B_134) | ~v1_relat_1(B_134))), inference(resolution, [status(thm)], [c_42, c_569])).
% 2.99/1.45  tff(c_586, plain, (![A_135, B_136]: (k1_xboole_0=A_135 | k8_relset_1(k1_relat_1(B_136), A_135, B_136, A_135)=k1_relat_1(B_136) | ~v1_funct_1(B_136) | ~v5_relat_1(B_136, A_135) | ~v1_relat_1(B_136))), inference(resolution, [status(thm)], [c_6, c_581])).
% 2.99/1.45  tff(c_284, plain, (![B_84, A_85]: (m1_subset_1(B_84, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_84), A_85))) | ~r1_tarski(k2_relat_1(B_84), A_85) | ~v1_funct_1(B_84) | ~v1_relat_1(B_84))), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.99/1.45  tff(c_20, plain, (![A_13, B_14, C_15, D_16]: (k8_relset_1(A_13, B_14, C_15, D_16)=k10_relat_1(C_15, D_16) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.99/1.45  tff(c_393, plain, (![B_101, A_102, D_103]: (k8_relset_1(k1_relat_1(B_101), A_102, B_101, D_103)=k10_relat_1(B_101, D_103) | ~r1_tarski(k2_relat_1(B_101), A_102) | ~v1_funct_1(B_101) | ~v1_relat_1(B_101))), inference(resolution, [status(thm)], [c_284, c_20])).
% 2.99/1.45  tff(c_396, plain, (![B_2, A_1, D_103]: (k8_relset_1(k1_relat_1(B_2), A_1, B_2, D_103)=k10_relat_1(B_2, D_103) | ~v1_funct_1(B_2) | ~v5_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(resolution, [status(thm)], [c_6, c_393])).
% 2.99/1.45  tff(c_620, plain, (![B_138, A_139]: (k10_relat_1(B_138, A_139)=k1_relat_1(B_138) | ~v1_funct_1(B_138) | ~v5_relat_1(B_138, A_139) | ~v1_relat_1(B_138) | k1_xboole_0=A_139 | ~v1_funct_1(B_138) | ~v5_relat_1(B_138, A_139) | ~v1_relat_1(B_138))), inference(superposition, [status(thm), theory('equality')], [c_586, c_396])).
% 2.99/1.45  tff(c_624, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3') | k1_xboole_0='#skF_1' | ~v1_funct_1('#skF_3') | ~v5_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_620])).
% 2.99/1.45  tff(c_631, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3') | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_624])).
% 2.99/1.45  tff(c_633, plain, $false, inference(negUnitSimplification, [status(thm)], [c_208, c_251, c_631])).
% 2.99/1.45  tff(c_634, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_84])).
% 2.99/1.45  tff(c_635, plain, (k1_relat_1('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_84])).
% 2.99/1.45  tff(c_646, plain, (k1_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_634, c_635])).
% 2.99/1.45  tff(c_684, plain, (![C_149, A_150, B_151]: (v4_relat_1(C_149, A_150) | ~m1_subset_1(C_149, k1_zfmisc_1(k2_zfmisc_1(A_150, B_151))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.99/1.45  tff(c_688, plain, (v4_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_54, c_684])).
% 2.99/1.45  tff(c_696, plain, (![B_153, A_154]: (k1_relat_1(B_153)=A_154 | ~v1_partfun1(B_153, A_154) | ~v4_relat_1(B_153, A_154) | ~v1_relat_1(B_153))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.99/1.45  tff(c_699, plain, (k1_relat_1('#skF_2')='#skF_1' | ~v1_partfun1('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_688, c_696])).
% 2.99/1.45  tff(c_702, plain, ('#skF_2'='#skF_1' | ~v1_partfun1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_77, c_646, c_699])).
% 2.99/1.45  tff(c_703, plain, (~v1_partfun1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_702])).
% 2.99/1.45  tff(c_841, plain, (![C_173, A_174, B_175]: (v1_partfun1(C_173, A_174) | ~v1_funct_2(C_173, A_174, B_175) | ~v1_funct_1(C_173) | ~m1_subset_1(C_173, k1_zfmisc_1(k2_zfmisc_1(A_174, B_175))) | v1_xboole_0(B_175))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.99/1.45  tff(c_847, plain, (v1_partfun1('#skF_2', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_54, c_841])).
% 2.99/1.45  tff(c_851, plain, (v1_partfun1('#skF_2', '#skF_1') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_847])).
% 2.99/1.45  tff(c_853, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_703, c_851])).
% 2.99/1.45  tff(c_854, plain, ('#skF_2'='#skF_1'), inference(splitRight, [status(thm)], [c_702])).
% 2.99/1.45  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.99/1.45  tff(c_640, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_634, c_2])).
% 2.99/1.45  tff(c_864, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_854, c_640])).
% 2.99/1.45  tff(c_872, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_864])).
% 2.99/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.99/1.45  
% 2.99/1.45  Inference rules
% 2.99/1.45  ----------------------
% 2.99/1.45  #Ref     : 0
% 2.99/1.45  #Sup     : 164
% 2.99/1.45  #Fact    : 0
% 2.99/1.45  #Define  : 0
% 2.99/1.45  #Split   : 9
% 2.99/1.45  #Chain   : 0
% 2.99/1.45  #Close   : 0
% 2.99/1.45  
% 2.99/1.45  Ordering : KBO
% 2.99/1.45  
% 2.99/1.45  Simplification rules
% 2.99/1.45  ----------------------
% 2.99/1.45  #Subsume      : 17
% 2.99/1.45  #Demod        : 138
% 2.99/1.45  #Tautology    : 62
% 2.99/1.45  #SimpNegUnit  : 17
% 2.99/1.45  #BackRed      : 21
% 2.99/1.45  
% 2.99/1.45  #Partial instantiations: 0
% 2.99/1.45  #Strategies tried      : 1
% 2.99/1.45  
% 2.99/1.45  Timing (in seconds)
% 2.99/1.45  ----------------------
% 2.99/1.45  Preprocessing        : 0.32
% 2.99/1.45  Parsing              : 0.17
% 2.99/1.45  CNF conversion       : 0.02
% 2.99/1.45  Main loop            : 0.37
% 2.99/1.45  Inferencing          : 0.14
% 2.99/1.45  Reduction            : 0.11
% 2.99/1.45  Demodulation         : 0.08
% 2.99/1.45  BG Simplification    : 0.02
% 2.99/1.45  Subsumption          : 0.05
% 2.99/1.45  Abstraction          : 0.02
% 2.99/1.45  MUC search           : 0.00
% 2.99/1.45  Cooper               : 0.00
% 2.99/1.45  Total                : 0.73
% 2.99/1.45  Index Insertion      : 0.00
% 2.99/1.45  Index Deletion       : 0.00
% 2.99/1.45  Index Matching       : 0.00
% 2.99/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
