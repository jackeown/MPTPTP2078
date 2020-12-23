%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:29 EST 2020

% Result     : Theorem 9.05s
% Output     : CNFRefutation 9.21s
% Verified   : 
% Statistics : Number of formulae       :  191 ( 948 expanded)
%              Number of leaves         :   40 ( 322 expanded)
%              Depth                    :   13
%              Number of atoms          :  338 (2631 expanded)
%              Number of equality atoms :  113 ( 733 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

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

tff(f_155,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( v2_funct_1(C)
            & k2_relset_1(A,B,C) = B )
         => ( v1_funct_1(k2_funct_1(C))
            & v1_funct_2(k2_funct_1(C),B,A)
            & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_78,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_68,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_115,axiom,(
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

tff(f_138,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc11_relat_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_128,axiom,(
    ! [A,B] :
    ? [C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
      & v1_relat_1(C)
      & v4_relat_1(C,A)
      & v5_relat_1(C,B)
      & v1_funct_1(C)
      & v1_funct_2(C,A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_funct_2)).

tff(f_32,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(c_74,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_273,plain,(
    ! [C_66,A_67,B_68] :
      ( v1_relat_1(C_66)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_281,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_273])).

tff(c_12,plain,(
    ! [A_7] :
      ( k2_relat_1(A_7) != k1_xboole_0
      | k1_xboole_0 = A_7
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_290,plain,
    ( k2_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_281,c_12])).

tff(c_304,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_290])).

tff(c_12565,plain,(
    ! [C_6930,A_6931,B_6932] :
      ( v1_xboole_0(C_6930)
      | ~ m1_subset_1(C_6930,k1_zfmisc_1(k2_zfmisc_1(A_6931,B_6932)))
      | ~ v1_xboole_0(A_6931) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_12581,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_12565])).

tff(c_12584,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_12581])).

tff(c_78,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_72,plain,(
    v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_70,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_13675,plain,(
    ! [A_7006,B_7007,C_7008] :
      ( k2_relset_1(A_7006,B_7007,C_7008) = k2_relat_1(C_7008)
      | ~ m1_subset_1(C_7008,k1_zfmisc_1(k2_zfmisc_1(A_7006,B_7007))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_13687,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_13675])).

tff(c_13696,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_13687])).

tff(c_28,plain,(
    ! [A_11] :
      ( k1_relat_1(k2_funct_1(A_11)) = k2_relat_1(A_11)
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_177,plain,(
    ! [A_52] :
      ( v1_funct_1(k2_funct_1(A_52))
      | ~ v1_funct_1(A_52)
      | ~ v1_relat_1(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_68,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_135,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_180,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_177,c_135])).

tff(c_183,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_180])).

tff(c_203,plain,(
    ! [C_57,A_58,B_59] :
      ( v1_relat_1(C_57)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_209,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_203])).

tff(c_219,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_183,c_209])).

tff(c_220,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_354,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_220])).

tff(c_1154,plain,(
    ! [A_133,B_134,C_135] :
      ( k2_relset_1(A_133,B_134,C_135) = k2_relat_1(C_135)
      | ~ m1_subset_1(C_135,k1_zfmisc_1(k2_zfmisc_1(A_133,B_134))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1163,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_1154])).

tff(c_1171,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1163])).

tff(c_24,plain,(
    ! [A_10] :
      ( v1_relat_1(k2_funct_1(A_10))
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_221,plain,(
    v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_1174,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1171,c_304])).

tff(c_76,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_798,plain,(
    ! [A_116,B_117,C_118] :
      ( k1_relset_1(A_116,B_117,C_118) = k1_relat_1(C_118)
      | ~ m1_subset_1(C_118,k1_zfmisc_1(k2_zfmisc_1(A_116,B_117))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_810,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_798])).

tff(c_2299,plain,(
    ! [B_168,A_169,C_170] :
      ( k1_xboole_0 = B_168
      | k1_relset_1(A_169,B_168,C_170) = A_169
      | ~ v1_funct_2(C_170,A_169,B_168)
      | ~ m1_subset_1(C_170,k1_zfmisc_1(k2_zfmisc_1(A_169,B_168))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_2311,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_2299])).

tff(c_2326,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_810,c_2311])).

tff(c_2327,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_1174,c_2326])).

tff(c_465,plain,(
    ! [A_92] :
      ( k2_relat_1(k2_funct_1(A_92)) = k1_relat_1(A_92)
      | ~ v2_funct_1(A_92)
      | ~ v1_funct_1(A_92)
      | ~ v1_relat_1(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_64,plain,(
    ! [A_31] :
      ( v1_funct_2(A_31,k1_relat_1(A_31),k2_relat_1(A_31))
      | ~ v1_funct_1(A_31)
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_8879,plain,(
    ! [A_1174] :
      ( v1_funct_2(k2_funct_1(A_1174),k1_relat_1(k2_funct_1(A_1174)),k1_relat_1(A_1174))
      | ~ v1_funct_1(k2_funct_1(A_1174))
      | ~ v1_relat_1(k2_funct_1(A_1174))
      | ~ v2_funct_1(A_1174)
      | ~ v1_funct_1(A_1174)
      | ~ v1_relat_1(A_1174) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_465,c_64])).

tff(c_8900,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),k1_relat_1(k2_funct_1('#skF_4')),'#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2327,c_8879])).

tff(c_8938,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),k1_relat_1(k2_funct_1('#skF_4')),'#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_281,c_78,c_72,c_221,c_8900])).

tff(c_8951,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_8938])).

tff(c_8954,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_8951])).

tff(c_8958,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_281,c_78,c_8954])).

tff(c_8960,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_8938])).

tff(c_26,plain,(
    ! [A_11] :
      ( k2_relat_1(k2_funct_1(A_11)) = k1_relat_1(A_11)
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_930,plain,(
    ! [A_127] :
      ( m1_subset_1(A_127,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_127),k2_relat_1(A_127))))
      | ~ v1_funct_1(A_127)
      | ~ v1_relat_1(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_12399,plain,(
    ! [A_6929] :
      ( m1_subset_1(k2_funct_1(A_6929),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_6929)),k1_relat_1(A_6929))))
      | ~ v1_funct_1(k2_funct_1(A_6929))
      | ~ v1_relat_1(k2_funct_1(A_6929))
      | ~ v2_funct_1(A_6929)
      | ~ v1_funct_1(A_6929)
      | ~ v1_relat_1(A_6929) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_930])).

tff(c_12440,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')),'#skF_2')))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2327,c_12399])).

tff(c_12485,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_281,c_78,c_72,c_8960,c_221,c_12440])).

tff(c_12520,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_4'),'#skF_2')))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_12485])).

tff(c_12537,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_281,c_78,c_72,c_1171,c_12520])).

tff(c_12539,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_354,c_12537])).

tff(c_12540,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_220])).

tff(c_12541,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_220])).

tff(c_13234,plain,(
    ! [A_6989,B_6990,C_6991] :
      ( k1_relset_1(A_6989,B_6990,C_6991) = k1_relat_1(C_6991)
      | ~ m1_subset_1(C_6991,k1_zfmisc_1(k2_zfmisc_1(A_6989,B_6990))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_13248,plain,(
    k1_relset_1('#skF_3','#skF_2',k2_funct_1('#skF_4')) = k1_relat_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_12541,c_13234])).

tff(c_14615,plain,(
    ! [B_7032,C_7033,A_7034] :
      ( k1_xboole_0 = B_7032
      | v1_funct_2(C_7033,A_7034,B_7032)
      | k1_relset_1(A_7034,B_7032,C_7033) != A_7034
      | ~ m1_subset_1(C_7033,k1_zfmisc_1(k2_zfmisc_1(A_7034,B_7032))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_14624,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | k1_relset_1('#skF_3','#skF_2',k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_12541,c_14615])).

tff(c_14641,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13248,c_14624])).

tff(c_14642,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_12540,c_14641])).

tff(c_14650,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_14642])).

tff(c_14653,plain,
    ( k2_relat_1('#skF_4') != '#skF_3'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_14650])).

tff(c_14656,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_281,c_78,c_72,c_13696,c_14653])).

tff(c_14657,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_14642])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_14718,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14657,c_2])).

tff(c_14720,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12584,c_14718])).

tff(c_14721,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_12581])).

tff(c_100,plain,(
    ! [A_41] :
      ( v1_xboole_0(k2_relat_1(A_41))
      | ~ v1_xboole_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_108,plain,(
    ! [A_41] :
      ( k2_relat_1(A_41) = k1_xboole_0
      | ~ v1_xboole_0(A_41) ) ),
    inference(resolution,[status(thm)],[c_100,c_4])).

tff(c_14725,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14721,c_108])).

tff(c_14735,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_304,c_14725])).

tff(c_14736,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_290])).

tff(c_14,plain,(
    ! [A_7] :
      ( k1_relat_1(A_7) != k1_xboole_0
      | k1_xboole_0 = A_7
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_289,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_281,c_14])).

tff(c_303,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_289])).

tff(c_14738,plain,(
    k1_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14736,c_303])).

tff(c_112,plain,(
    ! [A_47] :
      ( k2_relat_1(A_47) = k1_xboole_0
      | ~ v1_xboole_0(A_47) ) ),
    inference(resolution,[status(thm)],[c_100,c_4])).

tff(c_120,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_112])).

tff(c_14744,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14736,c_14736,c_120])).

tff(c_16,plain,(
    ! [A_8] :
      ( k1_relat_1(A_8) = k1_xboole_0
      | k2_relat_1(A_8) != k1_xboole_0
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_14757,plain,(
    ! [A_7035] :
      ( k1_relat_1(A_7035) = '#skF_4'
      | k2_relat_1(A_7035) != '#skF_4'
      | ~ v1_relat_1(A_7035) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14736,c_14736,c_16])).

tff(c_14767,plain,
    ( k1_relat_1('#skF_4') = '#skF_4'
    | k2_relat_1('#skF_4') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_281,c_14757])).

tff(c_14851,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14744,c_14767])).

tff(c_14852,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14738,c_14851])).

tff(c_14853,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_289])).

tff(c_14865,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14853,c_2])).

tff(c_60,plain,(
    ! [A_28,B_29] : m1_subset_1('#skF_1'(A_28,B_29),k1_zfmisc_1(k2_zfmisc_1(A_28,B_29))) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_22433,plain,(
    ! [C_7968,A_7969,B_7970] :
      ( v1_xboole_0(C_7968)
      | ~ m1_subset_1(C_7968,k1_zfmisc_1(k2_zfmisc_1(A_7969,B_7970)))
      | ~ v1_xboole_0(A_7969) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_22444,plain,(
    ! [A_7971,B_7972] :
      ( v1_xboole_0('#skF_1'(A_7971,B_7972))
      | ~ v1_xboole_0(A_7971) ) ),
    inference(resolution,[status(thm)],[c_60,c_22433])).

tff(c_14863,plain,(
    ! [A_1] :
      ( A_1 = '#skF_4'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14853,c_4])).

tff(c_22458,plain,(
    ! [A_7973,B_7974] :
      ( '#skF_1'(A_7973,B_7974) = '#skF_4'
      | ~ v1_xboole_0(A_7973) ) ),
    inference(resolution,[status(thm)],[c_22444,c_14863])).

tff(c_22468,plain,(
    ! [B_7975] : '#skF_1'('#skF_4',B_7975) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_14865,c_22458])).

tff(c_50,plain,(
    ! [A_28,B_29] : v1_funct_2('#skF_1'(A_28,B_29),A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_22485,plain,(
    ! [B_7975] : v1_funct_2('#skF_4','#skF_4',B_7975) ),
    inference(superposition,[status(thm),theory(equality)],[c_22468,c_50])).

tff(c_14860,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14853,c_14853,c_120])).

tff(c_6,plain,(
    ! [A_2] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_14864,plain,(
    ! [A_2] : m1_subset_1('#skF_4',k1_zfmisc_1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14853,c_6])).

tff(c_23036,plain,(
    ! [A_8013,B_8014,C_8015] :
      ( k2_relset_1(A_8013,B_8014,C_8015) = k2_relat_1(C_8015)
      | ~ m1_subset_1(C_8015,k1_zfmisc_1(k2_zfmisc_1(A_8013,B_8014))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_23043,plain,(
    ! [A_8013,B_8014] : k2_relset_1(A_8013,B_8014,'#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_14864,c_23036])).

tff(c_23049,plain,(
    ! [A_8013,B_8014] : k2_relset_1(A_8013,B_8014,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14860,c_23043])).

tff(c_23051,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_23049,c_70])).

tff(c_22343,plain,(
    ! [A_7961] :
      ( k1_relat_1(k2_funct_1(A_7961)) = k2_relat_1(A_7961)
      | ~ v2_funct_1(A_7961)
      | ~ v1_funct_1(A_7961)
      | ~ v1_relat_1(A_7961) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_14854,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_289])).

tff(c_14877,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14853,c_14854])).

tff(c_15295,plain,(
    ! [A_7080] :
      ( k2_relat_1(k2_funct_1(A_7080)) = k1_relat_1(A_7080)
      | ~ v2_funct_1(A_7080)
      | ~ v1_funct_1(A_7080)
      | ~ v1_relat_1(A_7080) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_21812,plain,(
    ! [A_7923] :
      ( v1_funct_2(k2_funct_1(A_7923),k1_relat_1(k2_funct_1(A_7923)),k1_relat_1(A_7923))
      | ~ v1_funct_1(k2_funct_1(A_7923))
      | ~ v1_relat_1(k2_funct_1(A_7923))
      | ~ v2_funct_1(A_7923)
      | ~ v1_funct_1(A_7923)
      | ~ v1_relat_1(A_7923) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15295,c_64])).

tff(c_21848,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),k1_relat_1(k2_funct_1('#skF_4')),'#skF_4')
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_14877,c_21812])).

tff(c_21868,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),k1_relat_1(k2_funct_1('#skF_4')),'#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_281,c_78,c_72,c_221,c_21848])).

tff(c_21869,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_21868])).

tff(c_21872,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_21869])).

tff(c_21876,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_281,c_78,c_21872])).

tff(c_21878,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_21868])).

tff(c_14857,plain,(
    ! [A_7] :
      ( k2_relat_1(A_7) != '#skF_4'
      | A_7 = '#skF_4'
      | ~ v1_relat_1(A_7) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14853,c_14853,c_12])).

tff(c_21893,plain,
    ( k2_relat_1(k2_funct_1('#skF_4')) != '#skF_4'
    | k2_funct_1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_21878,c_14857])).

tff(c_21900,plain,(
    k2_relat_1(k2_funct_1('#skF_4')) != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_21893])).

tff(c_21903,plain,
    ( k1_relat_1('#skF_4') != '#skF_4'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_21900])).

tff(c_21906,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_281,c_78,c_72,c_14877,c_21903])).

tff(c_21907,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_21893])).

tff(c_15925,plain,(
    ! [A_7118,B_7119,C_7120] :
      ( k2_relset_1(A_7118,B_7119,C_7120) = k2_relat_1(C_7120)
      | ~ m1_subset_1(C_7120,k1_zfmisc_1(k2_zfmisc_1(A_7118,B_7119))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_15932,plain,(
    ! [A_7118,B_7119] : k2_relset_1(A_7118,B_7119,'#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_14864,c_15925])).

tff(c_15938,plain,(
    ! [A_7118,B_7119] : k2_relset_1(A_7118,B_7119,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14860,c_15932])).

tff(c_15940,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15938,c_70])).

tff(c_14932,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_220])).

tff(c_15948,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15940,c_14932])).

tff(c_21912,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21907,c_15948])).

tff(c_21919,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14864,c_21912])).

tff(c_21921,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_220])).

tff(c_30,plain,(
    ! [C_14,A_12,B_13] :
      ( v1_relat_1(C_14)
      | ~ m1_subset_1(C_14,k1_zfmisc_1(k2_zfmisc_1(A_12,B_13))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_21925,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_21921,c_30])).

tff(c_21997,plain,(
    ! [A_7928] :
      ( k1_relat_1(A_7928) != '#skF_4'
      | A_7928 = '#skF_4'
      | ~ v1_relat_1(A_7928) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14853,c_14853,c_14])).

tff(c_22010,plain,
    ( k1_relat_1(k2_funct_1('#skF_4')) != '#skF_4'
    | k2_funct_1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_21925,c_21997])).

tff(c_22038,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_22010])).

tff(c_22352,plain,
    ( k2_relat_1('#skF_4') != '#skF_4'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_22343,c_22038])).

tff(c_22359,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_281,c_78,c_72,c_14860,c_22352])).

tff(c_22360,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_22010])).

tff(c_21977,plain,(
    ! [A_7927] :
      ( k2_relat_1(A_7927) != '#skF_4'
      | A_7927 = '#skF_4'
      | ~ v1_relat_1(A_7927) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14853,c_14853,c_12])).

tff(c_21990,plain,
    ( k2_relat_1(k2_funct_1('#skF_4')) != '#skF_4'
    | k2_funct_1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_21925,c_21977])).

tff(c_22017,plain,(
    k2_relat_1(k2_funct_1('#skF_4')) != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_21990])).

tff(c_22362,plain,(
    k2_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22360,c_22017])).

tff(c_22369,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14860,c_22362])).

tff(c_22370,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_21990])).

tff(c_21920,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_220])).

tff(c_22374,plain,(
    ~ v1_funct_2('#skF_4','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22370,c_21920])).

tff(c_23059,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_23051,c_22374])).

tff(c_23063,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22485,c_23059])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:14:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.05/3.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.05/3.29  
% 9.05/3.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.05/3.29  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 9.05/3.29  
% 9.05/3.29  %Foreground sorts:
% 9.05/3.29  
% 9.05/3.29  
% 9.05/3.29  %Background operators:
% 9.05/3.29  
% 9.05/3.29  
% 9.05/3.29  %Foreground operators:
% 9.05/3.29  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 9.05/3.29  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.05/3.29  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 9.05/3.29  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 9.05/3.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.05/3.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.05/3.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.05/3.29  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.05/3.29  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.05/3.29  tff('#skF_2', type, '#skF_2': $i).
% 9.05/3.29  tff('#skF_3', type, '#skF_3': $i).
% 9.05/3.29  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 9.05/3.29  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 9.05/3.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.05/3.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.05/3.29  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.05/3.29  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.05/3.29  tff('#skF_4', type, '#skF_4': $i).
% 9.05/3.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.05/3.29  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 9.05/3.29  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 9.05/3.29  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.05/3.29  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.05/3.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.05/3.29  
% 9.21/3.32  tff(f_155, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 9.21/3.32  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 9.21/3.32  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 9.21/3.32  tff(f_89, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_relset_1)).
% 9.21/3.32  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 9.21/3.32  tff(f_78, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 9.21/3.32  tff(f_68, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 9.21/3.32  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 9.21/3.32  tff(f_115, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 9.21/3.32  tff(f_138, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 9.21/3.32  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 9.21/3.32  tff(f_42, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc11_relat_1)).
% 9.21/3.32  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 9.21/3.32  tff(f_56, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 9.21/3.32  tff(f_128, axiom, (![A, B]: (?[C]: (((((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & v1_relat_1(C)) & v4_relat_1(C, A)) & v5_relat_1(C, B)) & v1_funct_1(C)) & v1_funct_2(C, A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_funct_2)).
% 9.21/3.32  tff(f_32, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 9.21/3.32  tff(c_74, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_155])).
% 9.21/3.32  tff(c_273, plain, (![C_66, A_67, B_68]: (v1_relat_1(C_66) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 9.21/3.32  tff(c_281, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_74, c_273])).
% 9.21/3.32  tff(c_12, plain, (![A_7]: (k2_relat_1(A_7)!=k1_xboole_0 | k1_xboole_0=A_7 | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_50])).
% 9.21/3.32  tff(c_290, plain, (k2_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_281, c_12])).
% 9.21/3.32  tff(c_304, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_290])).
% 9.21/3.32  tff(c_12565, plain, (![C_6930, A_6931, B_6932]: (v1_xboole_0(C_6930) | ~m1_subset_1(C_6930, k1_zfmisc_1(k2_zfmisc_1(A_6931, B_6932))) | ~v1_xboole_0(A_6931))), inference(cnfTransformation, [status(thm)], [f_89])).
% 9.21/3.32  tff(c_12581, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_74, c_12565])).
% 9.21/3.32  tff(c_12584, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_12581])).
% 9.21/3.32  tff(c_78, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_155])).
% 9.21/3.32  tff(c_72, plain, (v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_155])).
% 9.21/3.32  tff(c_70, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_155])).
% 9.21/3.32  tff(c_13675, plain, (![A_7006, B_7007, C_7008]: (k2_relset_1(A_7006, B_7007, C_7008)=k2_relat_1(C_7008) | ~m1_subset_1(C_7008, k1_zfmisc_1(k2_zfmisc_1(A_7006, B_7007))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 9.21/3.32  tff(c_13687, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_74, c_13675])).
% 9.21/3.32  tff(c_13696, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_13687])).
% 9.21/3.32  tff(c_28, plain, (![A_11]: (k1_relat_1(k2_funct_1(A_11))=k2_relat_1(A_11) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_78])).
% 9.21/3.32  tff(c_177, plain, (![A_52]: (v1_funct_1(k2_funct_1(A_52)) | ~v1_funct_1(A_52) | ~v1_relat_1(A_52))), inference(cnfTransformation, [status(thm)], [f_68])).
% 9.21/3.32  tff(c_68, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_155])).
% 9.21/3.32  tff(c_135, plain, (~v1_funct_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_68])).
% 9.21/3.32  tff(c_180, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_177, c_135])).
% 9.21/3.32  tff(c_183, plain, (~v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_180])).
% 9.21/3.32  tff(c_203, plain, (![C_57, A_58, B_59]: (v1_relat_1(C_57) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 9.21/3.32  tff(c_209, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_74, c_203])).
% 9.21/3.32  tff(c_219, plain, $false, inference(negUnitSimplification, [status(thm)], [c_183, c_209])).
% 9.21/3.32  tff(c_220, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_68])).
% 9.21/3.32  tff(c_354, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_220])).
% 9.21/3.32  tff(c_1154, plain, (![A_133, B_134, C_135]: (k2_relset_1(A_133, B_134, C_135)=k2_relat_1(C_135) | ~m1_subset_1(C_135, k1_zfmisc_1(k2_zfmisc_1(A_133, B_134))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 9.21/3.32  tff(c_1163, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_74, c_1154])).
% 9.21/3.32  tff(c_1171, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1163])).
% 9.21/3.32  tff(c_24, plain, (![A_10]: (v1_relat_1(k2_funct_1(A_10)) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_68])).
% 9.21/3.32  tff(c_221, plain, (v1_funct_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_68])).
% 9.21/3.32  tff(c_1174, plain, (k1_xboole_0!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1171, c_304])).
% 9.21/3.32  tff(c_76, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_155])).
% 9.21/3.32  tff(c_798, plain, (![A_116, B_117, C_118]: (k1_relset_1(A_116, B_117, C_118)=k1_relat_1(C_118) | ~m1_subset_1(C_118, k1_zfmisc_1(k2_zfmisc_1(A_116, B_117))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 9.21/3.32  tff(c_810, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_74, c_798])).
% 9.21/3.32  tff(c_2299, plain, (![B_168, A_169, C_170]: (k1_xboole_0=B_168 | k1_relset_1(A_169, B_168, C_170)=A_169 | ~v1_funct_2(C_170, A_169, B_168) | ~m1_subset_1(C_170, k1_zfmisc_1(k2_zfmisc_1(A_169, B_168))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 9.21/3.32  tff(c_2311, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_74, c_2299])).
% 9.21/3.32  tff(c_2326, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_810, c_2311])).
% 9.21/3.32  tff(c_2327, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_1174, c_2326])).
% 9.21/3.32  tff(c_465, plain, (![A_92]: (k2_relat_1(k2_funct_1(A_92))=k1_relat_1(A_92) | ~v2_funct_1(A_92) | ~v1_funct_1(A_92) | ~v1_relat_1(A_92))), inference(cnfTransformation, [status(thm)], [f_78])).
% 9.21/3.32  tff(c_64, plain, (![A_31]: (v1_funct_2(A_31, k1_relat_1(A_31), k2_relat_1(A_31)) | ~v1_funct_1(A_31) | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_138])).
% 9.21/3.32  tff(c_8879, plain, (![A_1174]: (v1_funct_2(k2_funct_1(A_1174), k1_relat_1(k2_funct_1(A_1174)), k1_relat_1(A_1174)) | ~v1_funct_1(k2_funct_1(A_1174)) | ~v1_relat_1(k2_funct_1(A_1174)) | ~v2_funct_1(A_1174) | ~v1_funct_1(A_1174) | ~v1_relat_1(A_1174))), inference(superposition, [status(thm), theory('equality')], [c_465, c_64])).
% 9.21/3.32  tff(c_8900, plain, (v1_funct_2(k2_funct_1('#skF_4'), k1_relat_1(k2_funct_1('#skF_4')), '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2327, c_8879])).
% 9.21/3.32  tff(c_8938, plain, (v1_funct_2(k2_funct_1('#skF_4'), k1_relat_1(k2_funct_1('#skF_4')), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_281, c_78, c_72, c_221, c_8900])).
% 9.21/3.32  tff(c_8951, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_8938])).
% 9.21/3.32  tff(c_8954, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_24, c_8951])).
% 9.21/3.32  tff(c_8958, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_281, c_78, c_8954])).
% 9.21/3.32  tff(c_8960, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_8938])).
% 9.21/3.32  tff(c_26, plain, (![A_11]: (k2_relat_1(k2_funct_1(A_11))=k1_relat_1(A_11) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_78])).
% 9.21/3.32  tff(c_930, plain, (![A_127]: (m1_subset_1(A_127, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_127), k2_relat_1(A_127)))) | ~v1_funct_1(A_127) | ~v1_relat_1(A_127))), inference(cnfTransformation, [status(thm)], [f_138])).
% 9.21/3.32  tff(c_12399, plain, (![A_6929]: (m1_subset_1(k2_funct_1(A_6929), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_6929)), k1_relat_1(A_6929)))) | ~v1_funct_1(k2_funct_1(A_6929)) | ~v1_relat_1(k2_funct_1(A_6929)) | ~v2_funct_1(A_6929) | ~v1_funct_1(A_6929) | ~v1_relat_1(A_6929))), inference(superposition, [status(thm), theory('equality')], [c_26, c_930])).
% 9.21/3.32  tff(c_12440, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')), '#skF_2'))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2327, c_12399])).
% 9.21/3.32  tff(c_12485, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_281, c_78, c_72, c_8960, c_221, c_12440])).
% 9.21/3.32  tff(c_12520, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_4'), '#skF_2'))) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_28, c_12485])).
% 9.21/3.32  tff(c_12537, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_281, c_78, c_72, c_1171, c_12520])).
% 9.21/3.32  tff(c_12539, plain, $false, inference(negUnitSimplification, [status(thm)], [c_354, c_12537])).
% 9.21/3.32  tff(c_12540, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_220])).
% 9.21/3.32  tff(c_12541, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_220])).
% 9.21/3.32  tff(c_13234, plain, (![A_6989, B_6990, C_6991]: (k1_relset_1(A_6989, B_6990, C_6991)=k1_relat_1(C_6991) | ~m1_subset_1(C_6991, k1_zfmisc_1(k2_zfmisc_1(A_6989, B_6990))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 9.21/3.32  tff(c_13248, plain, (k1_relset_1('#skF_3', '#skF_2', k2_funct_1('#skF_4'))=k1_relat_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_12541, c_13234])).
% 9.21/3.32  tff(c_14615, plain, (![B_7032, C_7033, A_7034]: (k1_xboole_0=B_7032 | v1_funct_2(C_7033, A_7034, B_7032) | k1_relset_1(A_7034, B_7032, C_7033)!=A_7034 | ~m1_subset_1(C_7033, k1_zfmisc_1(k2_zfmisc_1(A_7034, B_7032))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 9.21/3.32  tff(c_14624, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | k1_relset_1('#skF_3', '#skF_2', k2_funct_1('#skF_4'))!='#skF_3'), inference(resolution, [status(thm)], [c_12541, c_14615])).
% 9.21/3.32  tff(c_14641, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | k1_relat_1(k2_funct_1('#skF_4'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_13248, c_14624])).
% 9.21/3.32  tff(c_14642, plain, (k1_xboole_0='#skF_2' | k1_relat_1(k2_funct_1('#skF_4'))!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_12540, c_14641])).
% 9.21/3.32  tff(c_14650, plain, (k1_relat_1(k2_funct_1('#skF_4'))!='#skF_3'), inference(splitLeft, [status(thm)], [c_14642])).
% 9.21/3.32  tff(c_14653, plain, (k2_relat_1('#skF_4')!='#skF_3' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_28, c_14650])).
% 9.21/3.32  tff(c_14656, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_281, c_78, c_72, c_13696, c_14653])).
% 9.21/3.32  tff(c_14657, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_14642])).
% 9.21/3.32  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 9.21/3.32  tff(c_14718, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_14657, c_2])).
% 9.21/3.32  tff(c_14720, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12584, c_14718])).
% 9.21/3.32  tff(c_14721, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_12581])).
% 9.21/3.32  tff(c_100, plain, (![A_41]: (v1_xboole_0(k2_relat_1(A_41)) | ~v1_xboole_0(A_41))), inference(cnfTransformation, [status(thm)], [f_42])).
% 9.21/3.32  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 9.21/3.32  tff(c_108, plain, (![A_41]: (k2_relat_1(A_41)=k1_xboole_0 | ~v1_xboole_0(A_41))), inference(resolution, [status(thm)], [c_100, c_4])).
% 9.21/3.32  tff(c_14725, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_14721, c_108])).
% 9.21/3.32  tff(c_14735, plain, $false, inference(negUnitSimplification, [status(thm)], [c_304, c_14725])).
% 9.21/3.32  tff(c_14736, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_290])).
% 9.21/3.32  tff(c_14, plain, (![A_7]: (k1_relat_1(A_7)!=k1_xboole_0 | k1_xboole_0=A_7 | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_50])).
% 9.21/3.32  tff(c_289, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_281, c_14])).
% 9.21/3.32  tff(c_303, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_289])).
% 9.21/3.32  tff(c_14738, plain, (k1_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_14736, c_303])).
% 9.21/3.32  tff(c_112, plain, (![A_47]: (k2_relat_1(A_47)=k1_xboole_0 | ~v1_xboole_0(A_47))), inference(resolution, [status(thm)], [c_100, c_4])).
% 9.21/3.32  tff(c_120, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_112])).
% 9.21/3.32  tff(c_14744, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_14736, c_14736, c_120])).
% 9.21/3.32  tff(c_16, plain, (![A_8]: (k1_relat_1(A_8)=k1_xboole_0 | k2_relat_1(A_8)!=k1_xboole_0 | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_56])).
% 9.21/3.32  tff(c_14757, plain, (![A_7035]: (k1_relat_1(A_7035)='#skF_4' | k2_relat_1(A_7035)!='#skF_4' | ~v1_relat_1(A_7035))), inference(demodulation, [status(thm), theory('equality')], [c_14736, c_14736, c_16])).
% 9.21/3.32  tff(c_14767, plain, (k1_relat_1('#skF_4')='#skF_4' | k2_relat_1('#skF_4')!='#skF_4'), inference(resolution, [status(thm)], [c_281, c_14757])).
% 9.21/3.32  tff(c_14851, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_14744, c_14767])).
% 9.21/3.32  tff(c_14852, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14738, c_14851])).
% 9.21/3.32  tff(c_14853, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_289])).
% 9.21/3.32  tff(c_14865, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_14853, c_2])).
% 9.21/3.32  tff(c_60, plain, (![A_28, B_29]: (m1_subset_1('#skF_1'(A_28, B_29), k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 9.21/3.32  tff(c_22433, plain, (![C_7968, A_7969, B_7970]: (v1_xboole_0(C_7968) | ~m1_subset_1(C_7968, k1_zfmisc_1(k2_zfmisc_1(A_7969, B_7970))) | ~v1_xboole_0(A_7969))), inference(cnfTransformation, [status(thm)], [f_89])).
% 9.21/3.32  tff(c_22444, plain, (![A_7971, B_7972]: (v1_xboole_0('#skF_1'(A_7971, B_7972)) | ~v1_xboole_0(A_7971))), inference(resolution, [status(thm)], [c_60, c_22433])).
% 9.21/3.32  tff(c_14863, plain, (![A_1]: (A_1='#skF_4' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_14853, c_4])).
% 9.21/3.32  tff(c_22458, plain, (![A_7973, B_7974]: ('#skF_1'(A_7973, B_7974)='#skF_4' | ~v1_xboole_0(A_7973))), inference(resolution, [status(thm)], [c_22444, c_14863])).
% 9.21/3.32  tff(c_22468, plain, (![B_7975]: ('#skF_1'('#skF_4', B_7975)='#skF_4')), inference(resolution, [status(thm)], [c_14865, c_22458])).
% 9.21/3.32  tff(c_50, plain, (![A_28, B_29]: (v1_funct_2('#skF_1'(A_28, B_29), A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_128])).
% 9.21/3.32  tff(c_22485, plain, (![B_7975]: (v1_funct_2('#skF_4', '#skF_4', B_7975))), inference(superposition, [status(thm), theory('equality')], [c_22468, c_50])).
% 9.21/3.32  tff(c_14860, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_14853, c_14853, c_120])).
% 9.21/3.32  tff(c_6, plain, (![A_2]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.21/3.32  tff(c_14864, plain, (![A_2]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_14853, c_6])).
% 9.21/3.32  tff(c_23036, plain, (![A_8013, B_8014, C_8015]: (k2_relset_1(A_8013, B_8014, C_8015)=k2_relat_1(C_8015) | ~m1_subset_1(C_8015, k1_zfmisc_1(k2_zfmisc_1(A_8013, B_8014))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 9.21/3.32  tff(c_23043, plain, (![A_8013, B_8014]: (k2_relset_1(A_8013, B_8014, '#skF_4')=k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_14864, c_23036])).
% 9.21/3.32  tff(c_23049, plain, (![A_8013, B_8014]: (k2_relset_1(A_8013, B_8014, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_14860, c_23043])).
% 9.21/3.32  tff(c_23051, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_23049, c_70])).
% 9.21/3.32  tff(c_22343, plain, (![A_7961]: (k1_relat_1(k2_funct_1(A_7961))=k2_relat_1(A_7961) | ~v2_funct_1(A_7961) | ~v1_funct_1(A_7961) | ~v1_relat_1(A_7961))), inference(cnfTransformation, [status(thm)], [f_78])).
% 9.21/3.32  tff(c_14854, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_289])).
% 9.21/3.32  tff(c_14877, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_14853, c_14854])).
% 9.21/3.32  tff(c_15295, plain, (![A_7080]: (k2_relat_1(k2_funct_1(A_7080))=k1_relat_1(A_7080) | ~v2_funct_1(A_7080) | ~v1_funct_1(A_7080) | ~v1_relat_1(A_7080))), inference(cnfTransformation, [status(thm)], [f_78])).
% 9.21/3.32  tff(c_21812, plain, (![A_7923]: (v1_funct_2(k2_funct_1(A_7923), k1_relat_1(k2_funct_1(A_7923)), k1_relat_1(A_7923)) | ~v1_funct_1(k2_funct_1(A_7923)) | ~v1_relat_1(k2_funct_1(A_7923)) | ~v2_funct_1(A_7923) | ~v1_funct_1(A_7923) | ~v1_relat_1(A_7923))), inference(superposition, [status(thm), theory('equality')], [c_15295, c_64])).
% 9.21/3.32  tff(c_21848, plain, (v1_funct_2(k2_funct_1('#skF_4'), k1_relat_1(k2_funct_1('#skF_4')), '#skF_4') | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_14877, c_21812])).
% 9.21/3.32  tff(c_21868, plain, (v1_funct_2(k2_funct_1('#skF_4'), k1_relat_1(k2_funct_1('#skF_4')), '#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_281, c_78, c_72, c_221, c_21848])).
% 9.21/3.32  tff(c_21869, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_21868])).
% 9.21/3.32  tff(c_21872, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_24, c_21869])).
% 9.21/3.32  tff(c_21876, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_281, c_78, c_21872])).
% 9.21/3.32  tff(c_21878, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_21868])).
% 9.21/3.32  tff(c_14857, plain, (![A_7]: (k2_relat_1(A_7)!='#skF_4' | A_7='#skF_4' | ~v1_relat_1(A_7))), inference(demodulation, [status(thm), theory('equality')], [c_14853, c_14853, c_12])).
% 9.21/3.32  tff(c_21893, plain, (k2_relat_1(k2_funct_1('#skF_4'))!='#skF_4' | k2_funct_1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_21878, c_14857])).
% 9.21/3.32  tff(c_21900, plain, (k2_relat_1(k2_funct_1('#skF_4'))!='#skF_4'), inference(splitLeft, [status(thm)], [c_21893])).
% 9.21/3.32  tff(c_21903, plain, (k1_relat_1('#skF_4')!='#skF_4' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_26, c_21900])).
% 9.21/3.32  tff(c_21906, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_281, c_78, c_72, c_14877, c_21903])).
% 9.21/3.32  tff(c_21907, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_21893])).
% 9.21/3.32  tff(c_15925, plain, (![A_7118, B_7119, C_7120]: (k2_relset_1(A_7118, B_7119, C_7120)=k2_relat_1(C_7120) | ~m1_subset_1(C_7120, k1_zfmisc_1(k2_zfmisc_1(A_7118, B_7119))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 9.21/3.32  tff(c_15932, plain, (![A_7118, B_7119]: (k2_relset_1(A_7118, B_7119, '#skF_4')=k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_14864, c_15925])).
% 9.21/3.32  tff(c_15938, plain, (![A_7118, B_7119]: (k2_relset_1(A_7118, B_7119, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_14860, c_15932])).
% 9.21/3.32  tff(c_15940, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_15938, c_70])).
% 9.21/3.32  tff(c_14932, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_220])).
% 9.21/3.32  tff(c_15948, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_15940, c_14932])).
% 9.21/3.32  tff(c_21912, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_21907, c_15948])).
% 9.21/3.32  tff(c_21919, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14864, c_21912])).
% 9.21/3.32  tff(c_21921, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_220])).
% 9.21/3.32  tff(c_30, plain, (![C_14, A_12, B_13]: (v1_relat_1(C_14) | ~m1_subset_1(C_14, k1_zfmisc_1(k2_zfmisc_1(A_12, B_13))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 9.21/3.32  tff(c_21925, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_21921, c_30])).
% 9.21/3.32  tff(c_21997, plain, (![A_7928]: (k1_relat_1(A_7928)!='#skF_4' | A_7928='#skF_4' | ~v1_relat_1(A_7928))), inference(demodulation, [status(thm), theory('equality')], [c_14853, c_14853, c_14])).
% 9.21/3.32  tff(c_22010, plain, (k1_relat_1(k2_funct_1('#skF_4'))!='#skF_4' | k2_funct_1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_21925, c_21997])).
% 9.21/3.32  tff(c_22038, plain, (k1_relat_1(k2_funct_1('#skF_4'))!='#skF_4'), inference(splitLeft, [status(thm)], [c_22010])).
% 9.21/3.32  tff(c_22352, plain, (k2_relat_1('#skF_4')!='#skF_4' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_22343, c_22038])).
% 9.21/3.32  tff(c_22359, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_281, c_78, c_72, c_14860, c_22352])).
% 9.21/3.32  tff(c_22360, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_22010])).
% 9.21/3.32  tff(c_21977, plain, (![A_7927]: (k2_relat_1(A_7927)!='#skF_4' | A_7927='#skF_4' | ~v1_relat_1(A_7927))), inference(demodulation, [status(thm), theory('equality')], [c_14853, c_14853, c_12])).
% 9.21/3.32  tff(c_21990, plain, (k2_relat_1(k2_funct_1('#skF_4'))!='#skF_4' | k2_funct_1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_21925, c_21977])).
% 9.21/3.32  tff(c_22017, plain, (k2_relat_1(k2_funct_1('#skF_4'))!='#skF_4'), inference(splitLeft, [status(thm)], [c_21990])).
% 9.21/3.32  tff(c_22362, plain, (k2_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_22360, c_22017])).
% 9.21/3.32  tff(c_22369, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14860, c_22362])).
% 9.21/3.32  tff(c_22370, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_21990])).
% 9.21/3.32  tff(c_21920, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_220])).
% 9.21/3.32  tff(c_22374, plain, (~v1_funct_2('#skF_4', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_22370, c_21920])).
% 9.21/3.32  tff(c_23059, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_23051, c_22374])).
% 9.21/3.32  tff(c_23063, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22485, c_23059])).
% 9.21/3.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.21/3.32  
% 9.21/3.32  Inference rules
% 9.21/3.32  ----------------------
% 9.21/3.32  #Ref     : 0
% 9.21/3.32  #Sup     : 5057
% 9.21/3.32  #Fact    : 4
% 9.21/3.32  #Define  : 0
% 9.21/3.32  #Split   : 24
% 9.21/3.32  #Chain   : 0
% 9.21/3.32  #Close   : 0
% 9.21/3.32  
% 9.21/3.32  Ordering : KBO
% 9.21/3.32  
% 9.21/3.32  Simplification rules
% 9.21/3.32  ----------------------
% 9.21/3.32  #Subsume      : 1405
% 9.21/3.32  #Demod        : 5190
% 9.21/3.32  #Tautology    : 2544
% 9.21/3.32  #SimpNegUnit  : 27
% 9.21/3.32  #BackRed      : 114
% 9.21/3.32  
% 9.21/3.32  #Partial instantiations: 1407
% 9.21/3.32  #Strategies tried      : 1
% 9.21/3.32  
% 9.21/3.32  Timing (in seconds)
% 9.21/3.32  ----------------------
% 9.21/3.32  Preprocessing        : 0.36
% 9.21/3.32  Parsing              : 0.20
% 9.21/3.32  CNF conversion       : 0.02
% 9.21/3.32  Main loop            : 2.09
% 9.21/3.32  Inferencing          : 0.69
% 9.21/3.32  Reduction            : 0.72
% 9.21/3.32  Demodulation         : 0.53
% 9.21/3.32  BG Simplification    : 0.07
% 9.21/3.32  Subsumption          : 0.49
% 9.21/3.32  Abstraction          : 0.09
% 9.21/3.32  MUC search           : 0.00
% 9.21/3.32  Cooper               : 0.00
% 9.21/3.32  Total                : 2.50
% 9.21/3.32  Index Insertion      : 0.00
% 9.21/3.32  Index Deletion       : 0.00
% 9.21/3.32  Index Matching       : 0.00
% 9.21/3.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
