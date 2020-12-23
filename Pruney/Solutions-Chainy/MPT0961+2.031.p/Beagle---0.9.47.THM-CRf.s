%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:45 EST 2020

% Result     : Theorem 2.96s
% Output     : CNFRefutation 3.08s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 421 expanded)
%              Number of leaves         :   26 ( 147 expanded)
%              Depth                    :   12
%              Number of atoms          :  183 (1028 expanded)
%              Number of equality atoms :   59 ( 259 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_88,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v1_funct_1(A)
          & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
          & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_relat_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_40,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1081,plain,(
    ! [A_154] :
      ( r1_tarski(A_154,k2_zfmisc_1(k1_relat_1(A_154),k2_relat_1(A_154)))
      | ~ v1_relat_1(A_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_14,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(A_4,k1_zfmisc_1(B_5))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_18,plain,(
    ! [A_7] :
      ( r1_tarski(A_7,k2_zfmisc_1(k1_relat_1(A_7),k2_relat_1(A_7)))
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_480,plain,(
    ! [A_89,B_90,C_91] :
      ( k1_relset_1(A_89,B_90,C_91) = k1_relat_1(C_91)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_617,plain,(
    ! [A_113,B_114,A_115] :
      ( k1_relset_1(A_113,B_114,A_115) = k1_relat_1(A_115)
      | ~ r1_tarski(A_115,k2_zfmisc_1(A_113,B_114)) ) ),
    inference(resolution,[status(thm)],[c_14,c_480])).

tff(c_627,plain,(
    ! [A_7] :
      ( k1_relset_1(k1_relat_1(A_7),k2_relat_1(A_7),A_7) = k1_relat_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(resolution,[status(thm)],[c_18,c_617])).

tff(c_550,plain,(
    ! [B_100,C_101,A_102] :
      ( k1_xboole_0 = B_100
      | v1_funct_2(C_101,A_102,B_100)
      | k1_relset_1(A_102,B_100,C_101) != A_102
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_102,B_100))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_738,plain,(
    ! [B_133,A_134,A_135] :
      ( k1_xboole_0 = B_133
      | v1_funct_2(A_134,A_135,B_133)
      | k1_relset_1(A_135,B_133,A_134) != A_135
      | ~ r1_tarski(A_134,k2_zfmisc_1(A_135,B_133)) ) ),
    inference(resolution,[status(thm)],[c_14,c_550])).

tff(c_813,plain,(
    ! [A_143] :
      ( k2_relat_1(A_143) = k1_xboole_0
      | v1_funct_2(A_143,k1_relat_1(A_143),k2_relat_1(A_143))
      | k1_relset_1(k1_relat_1(A_143),k2_relat_1(A_143),A_143) != k1_relat_1(A_143)
      | ~ v1_relat_1(A_143) ) ),
    inference(resolution,[status(thm)],[c_18,c_738])).

tff(c_38,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_36,plain,
    ( ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))))
    | ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))
    | ~ v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_42,plain,
    ( ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))))
    | ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36])).

tff(c_98,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_816,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_813,c_98])).

tff(c_825,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_816])).

tff(c_828,plain,(
    k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_825])).

tff(c_831,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_627,c_828])).

tff(c_835,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_831])).

tff(c_836,plain,(
    k2_relat_1('#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_825])).

tff(c_454,plain,(
    ! [C_84,B_85,A_86] :
      ( v1_xboole_0(C_84)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(B_85,A_86)))
      | ~ v1_xboole_0(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_492,plain,(
    ! [A_92,A_93,B_94] :
      ( v1_xboole_0(A_92)
      | ~ v1_xboole_0(A_93)
      | ~ r1_tarski(A_92,k2_zfmisc_1(B_94,A_93)) ) ),
    inference(resolution,[status(thm)],[c_14,c_454])).

tff(c_502,plain,(
    ! [A_7] :
      ( v1_xboole_0(A_7)
      | ~ v1_xboole_0(k2_relat_1(A_7))
      | ~ v1_relat_1(A_7) ) ),
    inference(resolution,[status(thm)],[c_18,c_492])).

tff(c_848,plain,
    ( v1_xboole_0('#skF_1')
    | ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_836,c_502])).

tff(c_859,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2,c_848])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_870,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_859,c_4])).

tff(c_75,plain,(
    ! [A_21] :
      ( v1_xboole_0(k1_relat_1(A_21))
      | ~ v1_xboole_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_80,plain,(
    ! [A_22] :
      ( k1_relat_1(A_22) = k1_xboole_0
      | ~ v1_xboole_0(A_22) ) ),
    inference(resolution,[status(thm)],[c_75,c_4])).

tff(c_88,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_80])).

tff(c_206,plain,(
    ! [A_43,B_44,C_45] :
      ( k1_relset_1(A_43,B_44,C_45) = k1_relat_1(C_45)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_236,plain,(
    ! [A_54,B_55,A_56] :
      ( k1_relset_1(A_54,B_55,A_56) = k1_relat_1(A_56)
      | ~ r1_tarski(A_56,k2_zfmisc_1(A_54,B_55)) ) ),
    inference(resolution,[status(thm)],[c_14,c_206])).

tff(c_246,plain,(
    ! [A_7] :
      ( k1_relset_1(k1_relat_1(A_7),k2_relat_1(A_7),A_7) = k1_relat_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(resolution,[status(thm)],[c_18,c_236])).

tff(c_283,plain,(
    ! [B_63,C_64,A_65] :
      ( k1_xboole_0 = B_63
      | v1_funct_2(C_64,A_65,B_63)
      | k1_relset_1(A_65,B_63,C_64) != A_65
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_65,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_319,plain,(
    ! [B_72,A_73,A_74] :
      ( k1_xboole_0 = B_72
      | v1_funct_2(A_73,A_74,B_72)
      | k1_relset_1(A_74,B_72,A_73) != A_74
      | ~ r1_tarski(A_73,k2_zfmisc_1(A_74,B_72)) ) ),
    inference(resolution,[status(thm)],[c_14,c_283])).

tff(c_361,plain,(
    ! [A_83] :
      ( k2_relat_1(A_83) = k1_xboole_0
      | v1_funct_2(A_83,k1_relat_1(A_83),k2_relat_1(A_83))
      | k1_relset_1(k1_relat_1(A_83),k2_relat_1(A_83),A_83) != k1_relat_1(A_83)
      | ~ v1_relat_1(A_83) ) ),
    inference(resolution,[status(thm)],[c_18,c_319])).

tff(c_364,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_361,c_98])).

tff(c_373,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_364])).

tff(c_375,plain,(
    k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_373])).

tff(c_378,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_246,c_375])).

tff(c_382,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_378])).

tff(c_383,plain,(
    k2_relat_1('#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_373])).

tff(c_161,plain,(
    ! [C_32,B_33,A_34] :
      ( v1_xboole_0(C_32)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(B_33,A_34)))
      | ~ v1_xboole_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_186,plain,(
    ! [A_37,A_38,B_39] :
      ( v1_xboole_0(A_37)
      | ~ v1_xboole_0(A_38)
      | ~ r1_tarski(A_37,k2_zfmisc_1(B_39,A_38)) ) ),
    inference(resolution,[status(thm)],[c_14,c_161])).

tff(c_196,plain,(
    ! [A_7] :
      ( v1_xboole_0(A_7)
      | ~ v1_xboole_0(k2_relat_1(A_7))
      | ~ v1_relat_1(A_7) ) ),
    inference(resolution,[status(thm)],[c_18,c_186])).

tff(c_395,plain,
    ( v1_xboole_0('#skF_1')
    | ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_383,c_196])).

tff(c_406,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2,c_395])).

tff(c_417,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_406,c_4])).

tff(c_10,plain,(
    ! [B_3] : k2_zfmisc_1(k1_xboole_0,B_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_142,plain,(
    ! [A_30] :
      ( r1_tarski(A_30,k2_zfmisc_1(k1_relat_1(A_30),k2_relat_1(A_30)))
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_148,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k2_relat_1(k1_xboole_0)))
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_142])).

tff(c_150,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_148])).

tff(c_151,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_150])).

tff(c_440,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_417,c_151])).

tff(c_451,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_440])).

tff(c_452,plain,(
    r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_150])).

tff(c_8,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_24,plain,(
    ! [A_15] :
      ( v1_funct_2(k1_xboole_0,A_15,k1_xboole_0)
      | k1_xboole_0 = A_15
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_15,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_45,plain,(
    ! [A_15] :
      ( v1_funct_2(k1_xboole_0,A_15,k1_xboole_0)
      | k1_xboole_0 = A_15
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_24])).

tff(c_520,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_45])).

tff(c_523,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_14,c_520])).

tff(c_527,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_452,c_523])).

tff(c_529,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_45])).

tff(c_578,plain,(
    ! [B_106,C_107] :
      ( k1_relset_1(k1_xboole_0,B_106,C_107) = k1_relat_1(C_107)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_480])).

tff(c_580,plain,(
    ! [B_106] : k1_relset_1(k1_xboole_0,B_106,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_529,c_578])).

tff(c_585,plain,(
    ! [B_106] : k1_relset_1(k1_xboole_0,B_106,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_580])).

tff(c_28,plain,(
    ! [C_17,B_16] :
      ( v1_funct_2(C_17,k1_xboole_0,B_16)
      | k1_relset_1(k1_xboole_0,B_16,C_17) != k1_xboole_0
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_645,plain,(
    ! [C_117,B_118] :
      ( v1_funct_2(C_117,k1_xboole_0,B_118)
      | k1_relset_1(k1_xboole_0,B_118,C_117) != k1_xboole_0
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_28])).

tff(c_647,plain,(
    ! [B_118] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_118)
      | k1_relset_1(k1_xboole_0,B_118,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_529,c_645])).

tff(c_653,plain,(
    ! [B_118] : v1_funct_2(k1_xboole_0,k1_xboole_0,B_118) ),
    inference(demodulation,[status(thm),theory(equality)],[c_585,c_647])).

tff(c_882,plain,(
    ! [B_118] : v1_funct_2('#skF_1','#skF_1',B_118) ),
    inference(demodulation,[status(thm),theory(equality)],[c_870,c_870,c_653])).

tff(c_79,plain,(
    ! [A_21] :
      ( k1_relat_1(A_21) = k1_xboole_0
      | ~ v1_xboole_0(A_21) ) ),
    inference(resolution,[status(thm)],[c_75,c_4])).

tff(c_869,plain,(
    k1_relat_1('#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_859,c_79])).

tff(c_935,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_870,c_869])).

tff(c_838,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_836,c_98])).

tff(c_914,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_870,c_838])).

tff(c_936,plain,(
    ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_935,c_914])).

tff(c_1031,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_882,c_936])).

tff(c_1032,plain,(
    ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_1080,plain,(
    ~ r1_tarski('#skF_1',k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_14,c_1032])).

tff(c_1084,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_1081,c_1080])).

tff(c_1094,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1084])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:14:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.96/1.53  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.08/1.54  
% 3.08/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.08/1.54  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 3.08/1.54  
% 3.08/1.54  %Foreground sorts:
% 3.08/1.54  
% 3.08/1.54  
% 3.08/1.54  %Background operators:
% 3.08/1.54  
% 3.08/1.54  
% 3.08/1.54  %Foreground operators:
% 3.08/1.54  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.08/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.08/1.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.08/1.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.08/1.54  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.08/1.54  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.08/1.54  tff('#skF_1', type, '#skF_1': $i).
% 3.08/1.54  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.08/1.54  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.08/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.08/1.54  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.08/1.54  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.08/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.08/1.54  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.08/1.54  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.08/1.54  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.08/1.54  
% 3.08/1.56  tff(f_88, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 3.08/1.56  tff(f_48, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_relat_1)).
% 3.08/1.56  tff(f_40, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.08/1.56  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.08/1.56  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.08/1.56  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.08/1.56  tff(f_55, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 3.08/1.56  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.08/1.56  tff(f_44, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_relat_1)).
% 3.08/1.56  tff(f_36, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.08/1.56  tff(c_40, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.08/1.56  tff(c_1081, plain, (![A_154]: (r1_tarski(A_154, k2_zfmisc_1(k1_relat_1(A_154), k2_relat_1(A_154))) | ~v1_relat_1(A_154))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.08/1.56  tff(c_14, plain, (![A_4, B_5]: (m1_subset_1(A_4, k1_zfmisc_1(B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.08/1.56  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.08/1.56  tff(c_18, plain, (![A_7]: (r1_tarski(A_7, k2_zfmisc_1(k1_relat_1(A_7), k2_relat_1(A_7))) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.08/1.56  tff(c_480, plain, (![A_89, B_90, C_91]: (k1_relset_1(A_89, B_90, C_91)=k1_relat_1(C_91) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.08/1.56  tff(c_617, plain, (![A_113, B_114, A_115]: (k1_relset_1(A_113, B_114, A_115)=k1_relat_1(A_115) | ~r1_tarski(A_115, k2_zfmisc_1(A_113, B_114)))), inference(resolution, [status(thm)], [c_14, c_480])).
% 3.08/1.56  tff(c_627, plain, (![A_7]: (k1_relset_1(k1_relat_1(A_7), k2_relat_1(A_7), A_7)=k1_relat_1(A_7) | ~v1_relat_1(A_7))), inference(resolution, [status(thm)], [c_18, c_617])).
% 3.08/1.56  tff(c_550, plain, (![B_100, C_101, A_102]: (k1_xboole_0=B_100 | v1_funct_2(C_101, A_102, B_100) | k1_relset_1(A_102, B_100, C_101)!=A_102 | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_102, B_100))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.08/1.56  tff(c_738, plain, (![B_133, A_134, A_135]: (k1_xboole_0=B_133 | v1_funct_2(A_134, A_135, B_133) | k1_relset_1(A_135, B_133, A_134)!=A_135 | ~r1_tarski(A_134, k2_zfmisc_1(A_135, B_133)))), inference(resolution, [status(thm)], [c_14, c_550])).
% 3.08/1.56  tff(c_813, plain, (![A_143]: (k2_relat_1(A_143)=k1_xboole_0 | v1_funct_2(A_143, k1_relat_1(A_143), k2_relat_1(A_143)) | k1_relset_1(k1_relat_1(A_143), k2_relat_1(A_143), A_143)!=k1_relat_1(A_143) | ~v1_relat_1(A_143))), inference(resolution, [status(thm)], [c_18, c_738])).
% 3.08/1.56  tff(c_38, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.08/1.56  tff(c_36, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))) | ~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1')) | ~v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.08/1.56  tff(c_42, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))) | ~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36])).
% 3.08/1.56  tff(c_98, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_42])).
% 3.08/1.56  tff(c_816, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_813, c_98])).
% 3.08/1.56  tff(c_825, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_816])).
% 3.08/1.56  tff(c_828, plain, (k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_825])).
% 3.08/1.56  tff(c_831, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_627, c_828])).
% 3.08/1.56  tff(c_835, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_831])).
% 3.08/1.56  tff(c_836, plain, (k2_relat_1('#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_825])).
% 3.08/1.56  tff(c_454, plain, (![C_84, B_85, A_86]: (v1_xboole_0(C_84) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(B_85, A_86))) | ~v1_xboole_0(A_86))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.08/1.56  tff(c_492, plain, (![A_92, A_93, B_94]: (v1_xboole_0(A_92) | ~v1_xboole_0(A_93) | ~r1_tarski(A_92, k2_zfmisc_1(B_94, A_93)))), inference(resolution, [status(thm)], [c_14, c_454])).
% 3.08/1.56  tff(c_502, plain, (![A_7]: (v1_xboole_0(A_7) | ~v1_xboole_0(k2_relat_1(A_7)) | ~v1_relat_1(A_7))), inference(resolution, [status(thm)], [c_18, c_492])).
% 3.08/1.56  tff(c_848, plain, (v1_xboole_0('#skF_1') | ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_836, c_502])).
% 3.08/1.56  tff(c_859, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_2, c_848])).
% 3.08/1.56  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.08/1.56  tff(c_870, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_859, c_4])).
% 3.08/1.56  tff(c_75, plain, (![A_21]: (v1_xboole_0(k1_relat_1(A_21)) | ~v1_xboole_0(A_21))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.08/1.56  tff(c_80, plain, (![A_22]: (k1_relat_1(A_22)=k1_xboole_0 | ~v1_xboole_0(A_22))), inference(resolution, [status(thm)], [c_75, c_4])).
% 3.08/1.56  tff(c_88, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_80])).
% 3.08/1.56  tff(c_206, plain, (![A_43, B_44, C_45]: (k1_relset_1(A_43, B_44, C_45)=k1_relat_1(C_45) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.08/1.56  tff(c_236, plain, (![A_54, B_55, A_56]: (k1_relset_1(A_54, B_55, A_56)=k1_relat_1(A_56) | ~r1_tarski(A_56, k2_zfmisc_1(A_54, B_55)))), inference(resolution, [status(thm)], [c_14, c_206])).
% 3.08/1.56  tff(c_246, plain, (![A_7]: (k1_relset_1(k1_relat_1(A_7), k2_relat_1(A_7), A_7)=k1_relat_1(A_7) | ~v1_relat_1(A_7))), inference(resolution, [status(thm)], [c_18, c_236])).
% 3.08/1.56  tff(c_283, plain, (![B_63, C_64, A_65]: (k1_xboole_0=B_63 | v1_funct_2(C_64, A_65, B_63) | k1_relset_1(A_65, B_63, C_64)!=A_65 | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_65, B_63))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.08/1.56  tff(c_319, plain, (![B_72, A_73, A_74]: (k1_xboole_0=B_72 | v1_funct_2(A_73, A_74, B_72) | k1_relset_1(A_74, B_72, A_73)!=A_74 | ~r1_tarski(A_73, k2_zfmisc_1(A_74, B_72)))), inference(resolution, [status(thm)], [c_14, c_283])).
% 3.08/1.56  tff(c_361, plain, (![A_83]: (k2_relat_1(A_83)=k1_xboole_0 | v1_funct_2(A_83, k1_relat_1(A_83), k2_relat_1(A_83)) | k1_relset_1(k1_relat_1(A_83), k2_relat_1(A_83), A_83)!=k1_relat_1(A_83) | ~v1_relat_1(A_83))), inference(resolution, [status(thm)], [c_18, c_319])).
% 3.08/1.56  tff(c_364, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_361, c_98])).
% 3.08/1.56  tff(c_373, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_364])).
% 3.08/1.56  tff(c_375, plain, (k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_373])).
% 3.08/1.56  tff(c_378, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_246, c_375])).
% 3.08/1.56  tff(c_382, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_378])).
% 3.08/1.56  tff(c_383, plain, (k2_relat_1('#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_373])).
% 3.08/1.56  tff(c_161, plain, (![C_32, B_33, A_34]: (v1_xboole_0(C_32) | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(B_33, A_34))) | ~v1_xboole_0(A_34))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.08/1.56  tff(c_186, plain, (![A_37, A_38, B_39]: (v1_xboole_0(A_37) | ~v1_xboole_0(A_38) | ~r1_tarski(A_37, k2_zfmisc_1(B_39, A_38)))), inference(resolution, [status(thm)], [c_14, c_161])).
% 3.08/1.56  tff(c_196, plain, (![A_7]: (v1_xboole_0(A_7) | ~v1_xboole_0(k2_relat_1(A_7)) | ~v1_relat_1(A_7))), inference(resolution, [status(thm)], [c_18, c_186])).
% 3.08/1.56  tff(c_395, plain, (v1_xboole_0('#skF_1') | ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_383, c_196])).
% 3.08/1.56  tff(c_406, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_2, c_395])).
% 3.08/1.56  tff(c_417, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_406, c_4])).
% 3.08/1.56  tff(c_10, plain, (![B_3]: (k2_zfmisc_1(k1_xboole_0, B_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.08/1.56  tff(c_142, plain, (![A_30]: (r1_tarski(A_30, k2_zfmisc_1(k1_relat_1(A_30), k2_relat_1(A_30))) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.08/1.56  tff(c_148, plain, (r1_tarski(k1_xboole_0, k2_zfmisc_1(k1_xboole_0, k2_relat_1(k1_xboole_0))) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_88, c_142])).
% 3.08/1.56  tff(c_150, plain, (r1_tarski(k1_xboole_0, k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_148])).
% 3.08/1.56  tff(c_151, plain, (~v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_150])).
% 3.08/1.56  tff(c_440, plain, (~v1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_417, c_151])).
% 3.08/1.56  tff(c_451, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_440])).
% 3.08/1.56  tff(c_452, plain, (r1_tarski(k1_xboole_0, k1_xboole_0)), inference(splitRight, [status(thm)], [c_150])).
% 3.08/1.56  tff(c_8, plain, (![A_2]: (k2_zfmisc_1(A_2, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.08/1.56  tff(c_24, plain, (![A_15]: (v1_funct_2(k1_xboole_0, A_15, k1_xboole_0) | k1_xboole_0=A_15 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_15, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.08/1.56  tff(c_45, plain, (![A_15]: (v1_funct_2(k1_xboole_0, A_15, k1_xboole_0) | k1_xboole_0=A_15 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_24])).
% 3.08/1.56  tff(c_520, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_45])).
% 3.08/1.56  tff(c_523, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_520])).
% 3.08/1.56  tff(c_527, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_452, c_523])).
% 3.08/1.56  tff(c_529, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_45])).
% 3.08/1.56  tff(c_578, plain, (![B_106, C_107]: (k1_relset_1(k1_xboole_0, B_106, C_107)=k1_relat_1(C_107) | ~m1_subset_1(C_107, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_480])).
% 3.08/1.56  tff(c_580, plain, (![B_106]: (k1_relset_1(k1_xboole_0, B_106, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_529, c_578])).
% 3.08/1.56  tff(c_585, plain, (![B_106]: (k1_relset_1(k1_xboole_0, B_106, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_88, c_580])).
% 3.08/1.56  tff(c_28, plain, (![C_17, B_16]: (v1_funct_2(C_17, k1_xboole_0, B_16) | k1_relset_1(k1_xboole_0, B_16, C_17)!=k1_xboole_0 | ~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_16))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.08/1.56  tff(c_645, plain, (![C_117, B_118]: (v1_funct_2(C_117, k1_xboole_0, B_118) | k1_relset_1(k1_xboole_0, B_118, C_117)!=k1_xboole_0 | ~m1_subset_1(C_117, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_28])).
% 3.08/1.56  tff(c_647, plain, (![B_118]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_118) | k1_relset_1(k1_xboole_0, B_118, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_529, c_645])).
% 3.08/1.56  tff(c_653, plain, (![B_118]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_118))), inference(demodulation, [status(thm), theory('equality')], [c_585, c_647])).
% 3.08/1.56  tff(c_882, plain, (![B_118]: (v1_funct_2('#skF_1', '#skF_1', B_118))), inference(demodulation, [status(thm), theory('equality')], [c_870, c_870, c_653])).
% 3.08/1.56  tff(c_79, plain, (![A_21]: (k1_relat_1(A_21)=k1_xboole_0 | ~v1_xboole_0(A_21))), inference(resolution, [status(thm)], [c_75, c_4])).
% 3.08/1.56  tff(c_869, plain, (k1_relat_1('#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_859, c_79])).
% 3.08/1.56  tff(c_935, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_870, c_869])).
% 3.08/1.56  tff(c_838, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_836, c_98])).
% 3.08/1.56  tff(c_914, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_870, c_838])).
% 3.08/1.56  tff(c_936, plain, (~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_935, c_914])).
% 3.08/1.56  tff(c_1031, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_882, c_936])).
% 3.08/1.56  tff(c_1032, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))))), inference(splitRight, [status(thm)], [c_42])).
% 3.08/1.56  tff(c_1080, plain, (~r1_tarski('#skF_1', k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))), inference(resolution, [status(thm)], [c_14, c_1032])).
% 3.08/1.56  tff(c_1084, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_1081, c_1080])).
% 3.08/1.56  tff(c_1094, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_1084])).
% 3.08/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.08/1.56  
% 3.08/1.56  Inference rules
% 3.08/1.56  ----------------------
% 3.08/1.56  #Ref     : 0
% 3.08/1.56  #Sup     : 217
% 3.08/1.56  #Fact    : 0
% 3.08/1.56  #Define  : 0
% 3.08/1.56  #Split   : 6
% 3.08/1.56  #Chain   : 0
% 3.08/1.56  #Close   : 0
% 3.08/1.56  
% 3.08/1.56  Ordering : KBO
% 3.08/1.56  
% 3.08/1.56  Simplification rules
% 3.08/1.56  ----------------------
% 3.08/1.56  #Subsume      : 36
% 3.08/1.56  #Demod        : 295
% 3.08/1.56  #Tautology    : 106
% 3.08/1.56  #SimpNegUnit  : 1
% 3.08/1.57  #BackRed      : 72
% 3.08/1.57  
% 3.08/1.57  #Partial instantiations: 0
% 3.08/1.57  #Strategies tried      : 1
% 3.08/1.57  
% 3.08/1.57  Timing (in seconds)
% 3.08/1.57  ----------------------
% 3.08/1.57  Preprocessing        : 0.31
% 3.08/1.57  Parsing              : 0.17
% 3.08/1.57  CNF conversion       : 0.02
% 3.08/1.57  Main loop            : 0.42
% 3.08/1.57  Inferencing          : 0.16
% 3.08/1.57  Reduction            : 0.13
% 3.08/1.57  Demodulation         : 0.09
% 3.08/1.57  BG Simplification    : 0.02
% 3.08/1.57  Subsumption          : 0.08
% 3.08/1.57  Abstraction          : 0.03
% 3.08/1.57  MUC search           : 0.00
% 3.08/1.57  Cooper               : 0.00
% 3.08/1.57  Total                : 0.78
% 3.08/1.57  Index Insertion      : 0.00
% 3.08/1.57  Index Deletion       : 0.00
% 3.08/1.57  Index Matching       : 0.00
% 3.08/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
