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
% DateTime   : Thu Dec  3 10:12:32 EST 2020

% Result     : Theorem 4.84s
% Output     : CNFRefutation 4.84s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 365 expanded)
%              Number of leaves         :   39 ( 137 expanded)
%              Depth                    :   13
%              Number of atoms          :  228 (1042 expanded)
%              Number of equality atoms :   57 ( 181 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_relset_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_relset_1,type,(
    k3_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_152,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( v2_funct_1(C)
            & k2_relset_1(A,B,C) = B )
         => ( v1_funct_1(k2_funct_1(C))
            & v1_funct_2(k2_funct_1(C),B,A)
            & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_50,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_42,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k3_relset_1(A,B,C) = k4_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_relset_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k3_relset_1(A,B,C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_relset_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_70,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_60,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) )
     => ( v1_relat_1(k4_relat_1(A))
        & v1_funct_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_funct_1)).

tff(f_107,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_partfun1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_partfun1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_125,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_34,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc2_subset_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_135,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(c_62,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_94,plain,(
    ! [C_40,A_41,B_42] :
      ( v1_relat_1(C_40)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_102,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_94])).

tff(c_66,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_10,plain,(
    ! [A_5] :
      ( v1_funct_1(k2_funct_1(A_5))
      | ~ v1_funct_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_56,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_114,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_117,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_114])).

tff(c_121,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_66,c_117])).

tff(c_122,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_1344,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_122])).

tff(c_60,plain,(
    v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_107,plain,(
    ! [A_46] :
      ( k4_relat_1(A_46) = k2_funct_1(A_46)
      | ~ v2_funct_1(A_46)
      | ~ v1_funct_1(A_46)
      | ~ v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_110,plain,
    ( k4_relat_1('#skF_4') = k2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_107])).

tff(c_113,plain,(
    k4_relat_1('#skF_4') = k2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_66,c_110])).

tff(c_1475,plain,(
    ! [A_148,B_149,C_150] :
      ( k3_relset_1(A_148,B_149,C_150) = k4_relat_1(C_150)
      | ~ m1_subset_1(C_150,k1_zfmisc_1(k2_zfmisc_1(A_148,B_149))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1488,plain,(
    k3_relset_1('#skF_2','#skF_3','#skF_4') = k4_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_1475])).

tff(c_1494,plain,(
    k3_relset_1('#skF_2','#skF_3','#skF_4') = k2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_1488])).

tff(c_1666,plain,(
    ! [A_165,B_166,C_167] :
      ( m1_subset_1(k3_relset_1(A_165,B_166,C_167),k1_zfmisc_1(k2_zfmisc_1(B_166,A_165)))
      | ~ m1_subset_1(C_167,k1_zfmisc_1(k2_zfmisc_1(A_165,B_166))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1701,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1494,c_1666])).

tff(c_1714,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1701])).

tff(c_1716,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1344,c_1714])).

tff(c_1717,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_122])).

tff(c_58,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_1831,plain,(
    ! [A_179,B_180,C_181] :
      ( k2_relset_1(A_179,B_180,C_181) = k2_relat_1(C_181)
      | ~ m1_subset_1(C_181,k1_zfmisc_1(k2_zfmisc_1(A_179,B_180))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1844,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_1831])).

tff(c_1849,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1844])).

tff(c_20,plain,(
    ! [A_7] :
      ( k1_relat_1(k2_funct_1(A_7)) = k2_relat_1(A_7)
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_16,plain,(
    ! [A_6] :
      ( v1_relat_1(k4_relat_1(A_6))
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_127,plain,
    ( v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_16])).

tff(c_134,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_66,c_60,c_127])).

tff(c_123,plain,(
    v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_150,plain,(
    ! [C_48,A_49,B_50] :
      ( v1_partfun1(C_48,A_49)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50)))
      | ~ v1_xboole_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_158,plain,
    ( v1_partfun1('#skF_4','#skF_2')
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_150])).

tff(c_160,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_158])).

tff(c_528,plain,(
    ! [A_85,B_86,C_87] :
      ( k2_relset_1(A_85,B_86,C_87) = k2_relat_1(C_87)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_534,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_528])).

tff(c_541,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_534])).

tff(c_162,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_122])).

tff(c_198,plain,(
    ! [A_57,B_58,C_59] :
      ( k3_relset_1(A_57,B_58,C_59) = k4_relat_1(C_59)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_201,plain,(
    k3_relset_1('#skF_2','#skF_3','#skF_4') = k4_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_198])).

tff(c_207,plain,(
    k3_relset_1('#skF_2','#skF_3','#skF_4') = k2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_201])).

tff(c_429,plain,(
    ! [A_76,B_77,C_78] :
      ( m1_subset_1(k3_relset_1(A_76,B_77,C_78),k1_zfmisc_1(k2_zfmisc_1(B_77,A_76)))
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_460,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_207,c_429])).

tff(c_472,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_460])).

tff(c_474,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_162,c_472])).

tff(c_475,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_122])).

tff(c_476,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_122])).

tff(c_499,plain,(
    ! [A_80,B_81,C_82] :
      ( k1_relset_1(A_80,B_81,C_82) = k1_relat_1(C_82)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_510,plain,(
    k1_relset_1('#skF_3','#skF_2',k2_funct_1('#skF_4')) = k1_relat_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_476,c_499])).

tff(c_1258,plain,(
    ! [B_132,C_133,A_134] :
      ( k1_xboole_0 = B_132
      | v1_funct_2(C_133,A_134,B_132)
      | k1_relset_1(A_134,B_132,C_133) != A_134
      | ~ m1_subset_1(C_133,k1_zfmisc_1(k2_zfmisc_1(A_134,B_132))) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_1279,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | k1_relset_1('#skF_3','#skF_2',k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_476,c_1258])).

tff(c_1295,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_510,c_1279])).

tff(c_1296,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_475,c_1295])).

tff(c_1302,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1296])).

tff(c_1305,plain,
    ( k2_relat_1('#skF_4') != '#skF_3'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_1302])).

tff(c_1308,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_66,c_60,c_541,c_1305])).

tff(c_1309,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1296])).

tff(c_4,plain,(
    ! [A_2] : v1_xboole_0('#skF_1'(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_68,plain,(
    ! [A_35] :
      ( k1_xboole_0 = A_35
      | ~ v1_xboole_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_72,plain,(
    ! [A_2] : '#skF_1'(A_2) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_68])).

tff(c_77,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_4])).

tff(c_1337,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1309,c_77])).

tff(c_1341,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_160,c_1337])).

tff(c_1343,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_158])).

tff(c_64,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_1910,plain,(
    ! [A_186,B_187,C_188] :
      ( k1_relset_1(A_186,B_187,C_188) = k1_relat_1(C_188)
      | ~ m1_subset_1(C_188,k1_zfmisc_1(k2_zfmisc_1(A_186,B_187))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1931,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_1910])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1722,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_1343,c_2])).

tff(c_46,plain,(
    ! [B_31,C_32] :
      ( k1_relset_1(k1_xboole_0,B_31,C_32) = k1_xboole_0
      | ~ v1_funct_2(C_32,k1_xboole_0,B_31)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_2066,plain,(
    ! [B_196,C_197] :
      ( k1_relset_1('#skF_2',B_196,C_197) = '#skF_2'
      | ~ v1_funct_2(C_197,'#skF_2',B_196)
      | ~ m1_subset_1(C_197,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_196))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1722,c_1722,c_1722,c_1722,c_46])).

tff(c_2073,plain,
    ( k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_2066])).

tff(c_2078,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1931,c_2073])).

tff(c_50,plain,(
    ! [A_33] :
      ( m1_subset_1(A_33,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_33),k2_relat_1(A_33))))
      | ~ v1_funct_1(A_33)
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_1853,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3')))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1849,c_50])).

tff(c_1860,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_66,c_1853])).

tff(c_36,plain,(
    ! [C_29,A_26,B_27] :
      ( v1_partfun1(C_29,A_26)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27)))
      | ~ v1_xboole_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_1891,plain,
    ( v1_partfun1('#skF_4',k1_relat_1('#skF_4'))
    | ~ v1_xboole_0(k1_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_1860,c_36])).

tff(c_1902,plain,(
    ~ v1_xboole_0(k1_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_1891])).

tff(c_2081,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2078,c_1902])).

tff(c_2088,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1343,c_2081])).

tff(c_2090,plain,(
    v1_xboole_0(k1_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1891])).

tff(c_1727,plain,(
    ! [A_1] :
      ( A_1 = '#skF_2'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1722,c_2])).

tff(c_2094,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_2090,c_1727])).

tff(c_138,plain,(
    ! [A_47] :
      ( k2_relat_1(k2_funct_1(A_47)) = k1_relat_1(A_47)
      | ~ v2_funct_1(A_47)
      | ~ v1_funct_1(A_47)
      | ~ v1_relat_1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_52,plain,(
    ! [A_33] :
      ( v1_funct_2(A_33,k1_relat_1(A_33),k2_relat_1(A_33))
      | ~ v1_funct_1(A_33)
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_3231,plain,(
    ! [A_265] :
      ( v1_funct_2(k2_funct_1(A_265),k1_relat_1(k2_funct_1(A_265)),k1_relat_1(A_265))
      | ~ v1_funct_1(k2_funct_1(A_265))
      | ~ v1_relat_1(k2_funct_1(A_265))
      | ~ v2_funct_1(A_265)
      | ~ v1_funct_1(A_265)
      | ~ v1_relat_1(A_265) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_52])).

tff(c_3234,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),k1_relat_1(k2_funct_1('#skF_4')),'#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2094,c_3231])).

tff(c_3242,plain,(
    v1_funct_2(k2_funct_1('#skF_4'),k1_relat_1(k2_funct_1('#skF_4')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_66,c_60,c_134,c_123,c_3234])).

tff(c_3245,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),k2_relat_1('#skF_4'),'#skF_2')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_3242])).

tff(c_3247,plain,(
    v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_66,c_60,c_1849,c_3245])).

tff(c_3249,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1717,c_3247])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:50:20 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.84/1.93  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.84/1.94  
% 4.84/1.94  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.84/1.94  %$ v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_relset_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 4.84/1.94  
% 4.84/1.94  %Foreground sorts:
% 4.84/1.94  
% 4.84/1.94  
% 4.84/1.94  %Background operators:
% 4.84/1.94  
% 4.84/1.94  
% 4.84/1.94  %Foreground operators:
% 4.84/1.94  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.84/1.94  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.84/1.94  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.84/1.94  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.84/1.94  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.84/1.94  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.84/1.94  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.84/1.94  tff(k3_relset_1, type, k3_relset_1: ($i * $i * $i) > $i).
% 4.84/1.94  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.84/1.94  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.84/1.94  tff('#skF_2', type, '#skF_2': $i).
% 4.84/1.94  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 4.84/1.94  tff('#skF_3', type, '#skF_3': $i).
% 4.84/1.94  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.84/1.94  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.84/1.94  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.84/1.94  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.84/1.94  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.84/1.94  tff('#skF_4', type, '#skF_4': $i).
% 4.84/1.94  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.84/1.94  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.84/1.94  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.84/1.94  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 4.84/1.94  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.84/1.94  
% 4.84/1.96  tff(f_152, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 4.84/1.96  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.84/1.96  tff(f_50, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 4.84/1.96  tff(f_42, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_1)).
% 4.84/1.96  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k3_relset_1(A, B, C) = k4_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_relset_1)).
% 4.84/1.96  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k3_relset_1(A, B, C), k1_zfmisc_1(k2_zfmisc_1(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_relset_1)).
% 4.84/1.96  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.84/1.96  tff(f_70, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 4.84/1.96  tff(f_60, axiom, (![A]: (((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) => (v1_relat_1(k4_relat_1(A)) & v1_funct_1(k4_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_funct_1)).
% 4.84/1.96  tff(f_107, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_partfun1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_partfun1)).
% 4.84/1.96  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.84/1.96  tff(f_125, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.84/1.96  tff(f_34, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & v1_xboole_0(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc2_subset_1)).
% 4.84/1.96  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 4.84/1.96  tff(f_135, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 4.84/1.96  tff(c_62, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_152])).
% 4.84/1.96  tff(c_94, plain, (![C_40, A_41, B_42]: (v1_relat_1(C_40) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.84/1.96  tff(c_102, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_94])).
% 4.84/1.96  tff(c_66, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_152])).
% 4.84/1.96  tff(c_10, plain, (![A_5]: (v1_funct_1(k2_funct_1(A_5)) | ~v1_funct_1(A_5) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.84/1.96  tff(c_56, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_152])).
% 4.84/1.96  tff(c_114, plain, (~v1_funct_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_56])).
% 4.84/1.96  tff(c_117, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_10, c_114])).
% 4.84/1.96  tff(c_121, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_102, c_66, c_117])).
% 4.84/1.96  tff(c_122, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_56])).
% 4.84/1.96  tff(c_1344, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_122])).
% 4.84/1.96  tff(c_60, plain, (v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_152])).
% 4.84/1.96  tff(c_107, plain, (![A_46]: (k4_relat_1(A_46)=k2_funct_1(A_46) | ~v2_funct_1(A_46) | ~v1_funct_1(A_46) | ~v1_relat_1(A_46))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.84/1.96  tff(c_110, plain, (k4_relat_1('#skF_4')=k2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_107])).
% 4.84/1.96  tff(c_113, plain, (k4_relat_1('#skF_4')=k2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_66, c_110])).
% 4.84/1.96  tff(c_1475, plain, (![A_148, B_149, C_150]: (k3_relset_1(A_148, B_149, C_150)=k4_relat_1(C_150) | ~m1_subset_1(C_150, k1_zfmisc_1(k2_zfmisc_1(A_148, B_149))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.84/1.96  tff(c_1488, plain, (k3_relset_1('#skF_2', '#skF_3', '#skF_4')=k4_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_1475])).
% 4.84/1.96  tff(c_1494, plain, (k3_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_113, c_1488])).
% 4.84/1.96  tff(c_1666, plain, (![A_165, B_166, C_167]: (m1_subset_1(k3_relset_1(A_165, B_166, C_167), k1_zfmisc_1(k2_zfmisc_1(B_166, A_165))) | ~m1_subset_1(C_167, k1_zfmisc_1(k2_zfmisc_1(A_165, B_166))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.84/1.96  tff(c_1701, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_1494, c_1666])).
% 4.84/1.96  tff(c_1714, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_1701])).
% 4.84/1.96  tff(c_1716, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1344, c_1714])).
% 4.84/1.96  tff(c_1717, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_122])).
% 4.84/1.96  tff(c_58, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_152])).
% 4.84/1.96  tff(c_1831, plain, (![A_179, B_180, C_181]: (k2_relset_1(A_179, B_180, C_181)=k2_relat_1(C_181) | ~m1_subset_1(C_181, k1_zfmisc_1(k2_zfmisc_1(A_179, B_180))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.84/1.96  tff(c_1844, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_1831])).
% 4.84/1.96  tff(c_1849, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1844])).
% 4.84/1.96  tff(c_20, plain, (![A_7]: (k1_relat_1(k2_funct_1(A_7))=k2_relat_1(A_7) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.84/1.96  tff(c_16, plain, (![A_6]: (v1_relat_1(k4_relat_1(A_6)) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.84/1.96  tff(c_127, plain, (v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_113, c_16])).
% 4.84/1.96  tff(c_134, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_66, c_60, c_127])).
% 4.84/1.96  tff(c_123, plain, (v1_funct_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_56])).
% 4.84/1.96  tff(c_150, plain, (![C_48, A_49, B_50]: (v1_partfun1(C_48, A_49) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))) | ~v1_xboole_0(A_49))), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.84/1.96  tff(c_158, plain, (v1_partfun1('#skF_4', '#skF_2') | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_62, c_150])).
% 4.84/1.96  tff(c_160, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_158])).
% 4.84/1.96  tff(c_528, plain, (![A_85, B_86, C_87]: (k2_relset_1(A_85, B_86, C_87)=k2_relat_1(C_87) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.84/1.96  tff(c_534, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_528])).
% 4.84/1.96  tff(c_541, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_534])).
% 4.84/1.96  tff(c_162, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_122])).
% 4.84/1.96  tff(c_198, plain, (![A_57, B_58, C_59]: (k3_relset_1(A_57, B_58, C_59)=k4_relat_1(C_59) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.84/1.96  tff(c_201, plain, (k3_relset_1('#skF_2', '#skF_3', '#skF_4')=k4_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_198])).
% 4.84/1.96  tff(c_207, plain, (k3_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_113, c_201])).
% 4.84/1.96  tff(c_429, plain, (![A_76, B_77, C_78]: (m1_subset_1(k3_relset_1(A_76, B_77, C_78), k1_zfmisc_1(k2_zfmisc_1(B_77, A_76))) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.84/1.96  tff(c_460, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_207, c_429])).
% 4.84/1.96  tff(c_472, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_460])).
% 4.84/1.96  tff(c_474, plain, $false, inference(negUnitSimplification, [status(thm)], [c_162, c_472])).
% 4.84/1.96  tff(c_475, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_122])).
% 4.84/1.96  tff(c_476, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_122])).
% 4.84/1.96  tff(c_499, plain, (![A_80, B_81, C_82]: (k1_relset_1(A_80, B_81, C_82)=k1_relat_1(C_82) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.84/1.96  tff(c_510, plain, (k1_relset_1('#skF_3', '#skF_2', k2_funct_1('#skF_4'))=k1_relat_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_476, c_499])).
% 4.84/1.96  tff(c_1258, plain, (![B_132, C_133, A_134]: (k1_xboole_0=B_132 | v1_funct_2(C_133, A_134, B_132) | k1_relset_1(A_134, B_132, C_133)!=A_134 | ~m1_subset_1(C_133, k1_zfmisc_1(k2_zfmisc_1(A_134, B_132))))), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.84/1.96  tff(c_1279, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | k1_relset_1('#skF_3', '#skF_2', k2_funct_1('#skF_4'))!='#skF_3'), inference(resolution, [status(thm)], [c_476, c_1258])).
% 4.84/1.96  tff(c_1295, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | k1_relat_1(k2_funct_1('#skF_4'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_510, c_1279])).
% 4.84/1.96  tff(c_1296, plain, (k1_xboole_0='#skF_2' | k1_relat_1(k2_funct_1('#skF_4'))!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_475, c_1295])).
% 4.84/1.96  tff(c_1302, plain, (k1_relat_1(k2_funct_1('#skF_4'))!='#skF_3'), inference(splitLeft, [status(thm)], [c_1296])).
% 4.84/1.96  tff(c_1305, plain, (k2_relat_1('#skF_4')!='#skF_3' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_20, c_1302])).
% 4.84/1.96  tff(c_1308, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_102, c_66, c_60, c_541, c_1305])).
% 4.84/1.96  tff(c_1309, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_1296])).
% 4.84/1.96  tff(c_4, plain, (![A_2]: (v1_xboole_0('#skF_1'(A_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.84/1.96  tff(c_68, plain, (![A_35]: (k1_xboole_0=A_35 | ~v1_xboole_0(A_35))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.84/1.96  tff(c_72, plain, (![A_2]: ('#skF_1'(A_2)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_68])).
% 4.84/1.96  tff(c_77, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_72, c_4])).
% 4.84/1.96  tff(c_1337, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1309, c_77])).
% 4.84/1.96  tff(c_1341, plain, $false, inference(negUnitSimplification, [status(thm)], [c_160, c_1337])).
% 4.84/1.96  tff(c_1343, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_158])).
% 4.84/1.96  tff(c_64, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_152])).
% 4.84/1.96  tff(c_1910, plain, (![A_186, B_187, C_188]: (k1_relset_1(A_186, B_187, C_188)=k1_relat_1(C_188) | ~m1_subset_1(C_188, k1_zfmisc_1(k2_zfmisc_1(A_186, B_187))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.84/1.96  tff(c_1931, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_1910])).
% 4.84/1.96  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.84/1.96  tff(c_1722, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_1343, c_2])).
% 4.84/1.96  tff(c_46, plain, (![B_31, C_32]: (k1_relset_1(k1_xboole_0, B_31, C_32)=k1_xboole_0 | ~v1_funct_2(C_32, k1_xboole_0, B_31) | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_31))))), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.84/1.96  tff(c_2066, plain, (![B_196, C_197]: (k1_relset_1('#skF_2', B_196, C_197)='#skF_2' | ~v1_funct_2(C_197, '#skF_2', B_196) | ~m1_subset_1(C_197, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_196))))), inference(demodulation, [status(thm), theory('equality')], [c_1722, c_1722, c_1722, c_1722, c_46])).
% 4.84/1.96  tff(c_2073, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_62, c_2066])).
% 4.84/1.96  tff(c_2078, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_1931, c_2073])).
% 4.84/1.96  tff(c_50, plain, (![A_33]: (m1_subset_1(A_33, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_33), k2_relat_1(A_33)))) | ~v1_funct_1(A_33) | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.84/1.96  tff(c_1853, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3'))) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1849, c_50])).
% 4.84/1.96  tff(c_1860, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_66, c_1853])).
% 4.84/1.96  tff(c_36, plain, (![C_29, A_26, B_27]: (v1_partfun1(C_29, A_26) | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))) | ~v1_xboole_0(A_26))), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.84/1.96  tff(c_1891, plain, (v1_partfun1('#skF_4', k1_relat_1('#skF_4')) | ~v1_xboole_0(k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_1860, c_36])).
% 4.84/1.96  tff(c_1902, plain, (~v1_xboole_0(k1_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_1891])).
% 4.84/1.96  tff(c_2081, plain, (~v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2078, c_1902])).
% 4.84/1.96  tff(c_2088, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1343, c_2081])).
% 4.84/1.96  tff(c_2090, plain, (v1_xboole_0(k1_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_1891])).
% 4.84/1.96  tff(c_1727, plain, (![A_1]: (A_1='#skF_2' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_1722, c_2])).
% 4.84/1.96  tff(c_2094, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(resolution, [status(thm)], [c_2090, c_1727])).
% 4.84/1.96  tff(c_138, plain, (![A_47]: (k2_relat_1(k2_funct_1(A_47))=k1_relat_1(A_47) | ~v2_funct_1(A_47) | ~v1_funct_1(A_47) | ~v1_relat_1(A_47))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.84/1.96  tff(c_52, plain, (![A_33]: (v1_funct_2(A_33, k1_relat_1(A_33), k2_relat_1(A_33)) | ~v1_funct_1(A_33) | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.84/1.96  tff(c_3231, plain, (![A_265]: (v1_funct_2(k2_funct_1(A_265), k1_relat_1(k2_funct_1(A_265)), k1_relat_1(A_265)) | ~v1_funct_1(k2_funct_1(A_265)) | ~v1_relat_1(k2_funct_1(A_265)) | ~v2_funct_1(A_265) | ~v1_funct_1(A_265) | ~v1_relat_1(A_265))), inference(superposition, [status(thm), theory('equality')], [c_138, c_52])).
% 4.84/1.96  tff(c_3234, plain, (v1_funct_2(k2_funct_1('#skF_4'), k1_relat_1(k2_funct_1('#skF_4')), '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2094, c_3231])).
% 4.84/1.96  tff(c_3242, plain, (v1_funct_2(k2_funct_1('#skF_4'), k1_relat_1(k2_funct_1('#skF_4')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_66, c_60, c_134, c_123, c_3234])).
% 4.84/1.96  tff(c_3245, plain, (v1_funct_2(k2_funct_1('#skF_4'), k2_relat_1('#skF_4'), '#skF_2') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_20, c_3242])).
% 4.84/1.96  tff(c_3247, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_66, c_60, c_1849, c_3245])).
% 4.84/1.96  tff(c_3249, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1717, c_3247])).
% 4.84/1.96  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.84/1.96  
% 4.84/1.96  Inference rules
% 4.84/1.96  ----------------------
% 4.84/1.96  #Ref     : 0
% 4.84/1.96  #Sup     : 697
% 4.84/1.96  #Fact    : 0
% 4.84/1.96  #Define  : 0
% 4.84/1.96  #Split   : 22
% 4.84/1.96  #Chain   : 0
% 4.84/1.96  #Close   : 0
% 4.84/1.96  
% 4.84/1.96  Ordering : KBO
% 4.84/1.96  
% 4.84/1.96  Simplification rules
% 4.84/1.96  ----------------------
% 4.84/1.96  #Subsume      : 45
% 4.84/1.96  #Demod        : 633
% 4.84/1.96  #Tautology    : 360
% 4.84/1.96  #SimpNegUnit  : 21
% 4.84/1.96  #BackRed      : 75
% 4.84/1.96  
% 4.84/1.96  #Partial instantiations: 0
% 4.84/1.96  #Strategies tried      : 1
% 4.84/1.96  
% 4.84/1.96  Timing (in seconds)
% 4.84/1.96  ----------------------
% 5.28/1.97  Preprocessing        : 0.36
% 5.28/1.97  Parsing              : 0.19
% 5.28/1.97  CNF conversion       : 0.02
% 5.28/1.97  Main loop            : 0.83
% 5.28/1.97  Inferencing          : 0.30
% 5.28/1.97  Reduction            : 0.29
% 5.28/1.97  Demodulation         : 0.21
% 5.28/1.97  BG Simplification    : 0.04
% 5.28/1.97  Subsumption          : 0.13
% 5.28/1.97  Abstraction          : 0.04
% 5.28/1.97  MUC search           : 0.00
% 5.28/1.97  Cooper               : 0.00
% 5.28/1.97  Total                : 1.23
% 5.28/1.97  Index Insertion      : 0.00
% 5.28/1.97  Index Deletion       : 0.00
% 5.28/1.97  Index Matching       : 0.00
% 5.28/1.97  BG Taut test         : 0.00
%------------------------------------------------------------------------------
