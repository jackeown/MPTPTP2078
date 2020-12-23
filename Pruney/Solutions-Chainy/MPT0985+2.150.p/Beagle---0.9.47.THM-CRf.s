%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:50 EST 2020

% Result     : Theorem 6.46s
% Output     : CNFRefutation 6.98s
% Verified   : 
% Statistics : Number of formulae       :  217 (1514 expanded)
%              Number of leaves         :   45 ( 487 expanded)
%              Depth                    :   16
%              Number of atoms          :  377 (3897 expanded)
%              Number of equality atoms :  111 ( 762 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

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

tff(f_174,negated_conjecture,(
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

tff(f_110,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_85,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_57,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_118,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_103,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_114,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_136,axiom,(
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

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_93,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k10_relat_1(B,A) = k9_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_funct_1)).

tff(f_157,axiom,(
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

tff(f_34,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_40,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_68,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_147,axiom,(
    ! [A,B] :
    ? [C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
      & v1_relat_1(C)
      & v4_relat_1(C,A)
      & v5_relat_1(C,B)
      & v1_funct_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_partfun1)).

tff(f_42,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(c_80,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_391,plain,(
    ! [C_94,B_95,A_96] :
      ( v1_xboole_0(C_94)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(B_95,A_96)))
      | ~ v1_xboole_0(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_409,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_391])).

tff(c_414,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_409])).

tff(c_84,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_148,plain,(
    ! [A_58] :
      ( v1_funct_1(k2_funct_1(A_58))
      | ~ v1_funct_1(A_58)
      | ~ v1_relat_1(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_74,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_139,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_151,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_148,c_139])).

tff(c_154,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_151])).

tff(c_18,plain,(
    ! [A_12,B_13] : v1_relat_1(k2_zfmisc_1(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_182,plain,(
    ! [B_64,A_65] :
      ( v1_relat_1(B_64)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(A_65))
      | ~ v1_relat_1(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_194,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_80,c_182])).

tff(c_209,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_194])).

tff(c_211,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_154,c_209])).

tff(c_212,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_235,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_212])).

tff(c_223,plain,(
    ! [B_70,A_71] :
      ( v1_relat_1(B_70)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(A_71))
      | ~ v1_relat_1(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_226,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_80,c_223])).

tff(c_232,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_226])).

tff(c_78,plain,(
    v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_76,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_619,plain,(
    ! [A_111,B_112,C_113] :
      ( k2_relset_1(A_111,B_112,C_113) = k2_relat_1(C_113)
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k2_zfmisc_1(A_111,B_112))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_628,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_619])).

tff(c_642,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_628])).

tff(c_38,plain,(
    ! [A_22] :
      ( k1_relat_1(k2_funct_1(A_22)) = k2_relat_1(A_22)
      | ~ v2_funct_1(A_22)
      | ~ v1_funct_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_32,plain,(
    ! [A_19] :
      ( v1_relat_1(k2_funct_1(A_19))
      | ~ v1_funct_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_82,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_676,plain,(
    ! [A_116,B_117,C_118] :
      ( k1_relset_1(A_116,B_117,C_118) = k1_relat_1(C_118)
      | ~ m1_subset_1(C_118,k1_zfmisc_1(k2_zfmisc_1(A_116,B_117))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_698,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_676])).

tff(c_1352,plain,(
    ! [B_182,A_183,C_184] :
      ( k1_xboole_0 = B_182
      | k1_relset_1(A_183,B_182,C_184) = A_183
      | ~ v1_funct_2(C_184,A_183,B_182)
      | ~ m1_subset_1(C_184,k1_zfmisc_1(k2_zfmisc_1(A_183,B_182))) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_1364,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_1352])).

tff(c_1383,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_698,c_1364])).

tff(c_1387,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_1383])).

tff(c_469,plain,(
    ! [A_103] :
      ( k2_relat_1(k2_funct_1(A_103)) = k1_relat_1(A_103)
      | ~ v2_funct_1(A_103)
      | ~ v1_funct_1(A_103)
      | ~ v1_relat_1(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_22,plain,(
    ! [A_15] :
      ( k10_relat_1(A_15,k2_relat_1(A_15)) = k1_relat_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_3296,plain,(
    ! [A_263] :
      ( k10_relat_1(k2_funct_1(A_263),k1_relat_1(A_263)) = k1_relat_1(k2_funct_1(A_263))
      | ~ v1_relat_1(k2_funct_1(A_263))
      | ~ v2_funct_1(A_263)
      | ~ v1_funct_1(A_263)
      | ~ v1_relat_1(A_263) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_469,c_22])).

tff(c_3311,plain,
    ( k10_relat_1(k2_funct_1('#skF_4'),'#skF_2') = k1_relat_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1387,c_3296])).

tff(c_3328,plain,
    ( k10_relat_1(k2_funct_1('#skF_4'),'#skF_2') = k1_relat_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_232,c_84,c_78,c_3311])).

tff(c_3333,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_3328])).

tff(c_3336,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_3333])).

tff(c_3340,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_232,c_84,c_3336])).

tff(c_3342,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_3328])).

tff(c_213,plain,(
    v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_654,plain,
    ( k10_relat_1('#skF_4','#skF_3') = k1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_642,c_22])).

tff(c_662,plain,(
    k10_relat_1('#skF_4','#skF_3') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_232,c_654])).

tff(c_1393,plain,(
    k10_relat_1('#skF_4','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1387,c_662])).

tff(c_423,plain,(
    ! [A_99] :
      ( k1_relat_1(k2_funct_1(A_99)) = k2_relat_1(A_99)
      | ~ v2_funct_1(A_99)
      | ~ v1_funct_1(A_99)
      | ~ v1_relat_1(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_20,plain,(
    ! [A_14] :
      ( k9_relat_1(A_14,k1_relat_1(A_14)) = k2_relat_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_3599,plain,(
    ! [A_287] :
      ( k9_relat_1(k2_funct_1(A_287),k2_relat_1(A_287)) = k2_relat_1(k2_funct_1(A_287))
      | ~ v1_relat_1(k2_funct_1(A_287))
      | ~ v2_funct_1(A_287)
      | ~ v1_funct_1(A_287)
      | ~ v1_relat_1(A_287) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_423,c_20])).

tff(c_3624,plain,
    ( k9_relat_1(k2_funct_1('#skF_4'),'#skF_3') = k2_relat_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_642,c_3599])).

tff(c_3640,plain,(
    k9_relat_1(k2_funct_1('#skF_4'),'#skF_3') = k2_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_232,c_84,c_78,c_3342,c_3624])).

tff(c_34,plain,(
    ! [B_21,A_20] :
      ( k9_relat_1(k2_funct_1(B_21),A_20) = k10_relat_1(B_21,A_20)
      | ~ v2_funct_1(B_21)
      | ~ v1_funct_1(B_21)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_3646,plain,
    ( k2_relat_1(k2_funct_1('#skF_4')) = k10_relat_1('#skF_4','#skF_3')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3640,c_34])).

tff(c_3653,plain,(
    k2_relat_1(k2_funct_1('#skF_4')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_232,c_84,c_78,c_1393,c_3646])).

tff(c_68,plain,(
    ! [A_39] :
      ( m1_subset_1(A_39,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_39),k2_relat_1(A_39))))
      | ~ v1_funct_1(A_39)
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_3676,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')),'#skF_2')))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3653,c_68])).

tff(c_3702,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3342,c_213,c_3676])).

tff(c_3771,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_4'),'#skF_2')))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_3702])).

tff(c_3789,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_232,c_84,c_78,c_642,c_3771])).

tff(c_3791,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_235,c_3789])).

tff(c_3792,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1383])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_3831,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3792,c_2])).

tff(c_3833,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_414,c_3831])).

tff(c_3834,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_409])).

tff(c_135,plain,(
    ! [B_53,A_54] :
      ( ~ v1_xboole_0(B_53)
      | B_53 = A_54
      | ~ v1_xboole_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_138,plain,(
    ! [A_54] :
      ( k1_xboole_0 = A_54
      | ~ v1_xboole_0(A_54) ) ),
    inference(resolution,[status(thm)],[c_2,c_135])).

tff(c_3841,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_3834,c_138])).

tff(c_10,plain,(
    ! [B_4] : k2_zfmisc_1(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_3864,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_4',B_4) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3841,c_3841,c_10])).

tff(c_3835,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_409])).

tff(c_3848,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_3835,c_138])).

tff(c_3876,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3841,c_3848])).

tff(c_3879,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3876,c_235])).

tff(c_4273,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3864,c_3879])).

tff(c_26,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_3867,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3841,c_3841,c_26])).

tff(c_3916,plain,(
    ! [A_288] :
      ( k2_relat_1(k2_funct_1(A_288)) = k1_relat_1(A_288)
      | ~ v2_funct_1(A_288)
      | ~ v1_funct_1(A_288)
      | ~ v1_relat_1(A_288) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_6752,plain,(
    ! [A_470] :
      ( k10_relat_1(k2_funct_1(A_470),k1_relat_1(A_470)) = k1_relat_1(k2_funct_1(A_470))
      | ~ v1_relat_1(k2_funct_1(A_470))
      | ~ v2_funct_1(A_470)
      | ~ v1_funct_1(A_470)
      | ~ v1_relat_1(A_470) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3916,c_22])).

tff(c_6773,plain,
    ( k10_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k1_relat_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3867,c_6752])).

tff(c_6783,plain,
    ( k10_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k1_relat_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_232,c_84,c_78,c_6773])).

tff(c_6784,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_6783])).

tff(c_6787,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_6784])).

tff(c_6791,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_232,c_84,c_6787])).

tff(c_6793,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_6783])).

tff(c_8,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_3865,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3841,c_3841,c_8])).

tff(c_127,plain,(
    ! [A_47,B_48] : v1_relat_1(k2_zfmisc_1(A_47,B_48)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_129,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_127])).

tff(c_24,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_254,plain,(
    ! [A_73] :
      ( k10_relat_1(A_73,k2_relat_1(A_73)) = k1_relat_1(A_73)
      | ~ v1_relat_1(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_263,plain,
    ( k10_relat_1(k1_xboole_0,k1_xboole_0) = k1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_254])).

tff(c_267,plain,(
    k10_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_26,c_263])).

tff(c_3858,plain,(
    k10_relat_1('#skF_4','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3841,c_3841,c_3841,c_267])).

tff(c_3866,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3841,c_3841,c_24])).

tff(c_4004,plain,(
    ! [A_293] :
      ( k1_relat_1(k2_funct_1(A_293)) = k2_relat_1(A_293)
      | ~ v2_funct_1(A_293)
      | ~ v1_funct_1(A_293)
      | ~ v1_relat_1(A_293) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_6869,plain,(
    ! [A_476] :
      ( k9_relat_1(k2_funct_1(A_476),k2_relat_1(A_476)) = k2_relat_1(k2_funct_1(A_476))
      | ~ v1_relat_1(k2_funct_1(A_476))
      | ~ v2_funct_1(A_476)
      | ~ v1_funct_1(A_476)
      | ~ v1_relat_1(A_476) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4004,c_20])).

tff(c_6897,plain,
    ( k9_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k2_relat_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3866,c_6869])).

tff(c_6907,plain,(
    k9_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k2_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_232,c_84,c_78,c_6793,c_6897])).

tff(c_6911,plain,
    ( k2_relat_1(k2_funct_1('#skF_4')) = k10_relat_1('#skF_4','#skF_4')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_6907,c_34])).

tff(c_6918,plain,(
    k2_relat_1(k2_funct_1('#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_232,c_84,c_78,c_3858,c_6911])).

tff(c_6941,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')),'#skF_4')))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6918,c_68])).

tff(c_6967,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6793,c_213,c_3865,c_6941])).

tff(c_6969,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4273,c_6967])).

tff(c_6971,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_212])).

tff(c_7208,plain,(
    ! [C_510,B_511,A_512] :
      ( v1_xboole_0(C_510)
      | ~ m1_subset_1(C_510,k1_zfmisc_1(k2_zfmisc_1(B_511,A_512)))
      | ~ v1_xboole_0(A_512) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_7229,plain,
    ( v1_xboole_0(k2_funct_1('#skF_4'))
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_6971,c_7208])).

tff(c_7272,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_7229])).

tff(c_7440,plain,(
    ! [A_528,B_529,C_530] :
      ( k2_relset_1(A_528,B_529,C_530) = k2_relat_1(C_530)
      | ~ m1_subset_1(C_530,k1_zfmisc_1(k2_zfmisc_1(A_528,B_529))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_7449,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_7440])).

tff(c_7463,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_7449])).

tff(c_6970,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_212])).

tff(c_7619,plain,(
    ! [A_544,B_545,C_546] :
      ( k1_relset_1(A_544,B_545,C_546) = k1_relat_1(C_546)
      | ~ m1_subset_1(C_546,k1_zfmisc_1(k2_zfmisc_1(A_544,B_545))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_7640,plain,(
    k1_relset_1('#skF_3','#skF_2',k2_funct_1('#skF_4')) = k1_relat_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_6971,c_7619])).

tff(c_8133,plain,(
    ! [B_592,C_593,A_594] :
      ( k1_xboole_0 = B_592
      | v1_funct_2(C_593,A_594,B_592)
      | k1_relset_1(A_594,B_592,C_593) != A_594
      | ~ m1_subset_1(C_593,k1_zfmisc_1(k2_zfmisc_1(A_594,B_592))) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_8142,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | k1_relset_1('#skF_3','#skF_2',k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_6971,c_8133])).

tff(c_8160,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7640,c_8142])).

tff(c_8161,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_6970,c_8160])).

tff(c_8168,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_8161])).

tff(c_8171,plain,
    ( k2_relat_1('#skF_4') != '#skF_3'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_8168])).

tff(c_8174,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_232,c_84,c_78,c_7463,c_8171])).

tff(c_8175,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_8161])).

tff(c_8213,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8175,c_2])).

tff(c_8215,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7272,c_8213])).

tff(c_8217,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_7229])).

tff(c_8223,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_8217,c_138])).

tff(c_8239,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_2',B_4) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8223,c_8223,c_10])).

tff(c_8382,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8239,c_80])).

tff(c_7227,plain,(
    ! [C_510] :
      ( v1_xboole_0(C_510)
      | ~ m1_subset_1(C_510,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_7208])).

tff(c_7234,plain,(
    ! [C_510] :
      ( v1_xboole_0(C_510)
      | ~ m1_subset_1(C_510,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_7227])).

tff(c_8523,plain,(
    ! [C_609] :
      ( v1_xboole_0(C_609)
      | ~ m1_subset_1(C_609,k1_zfmisc_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8223,c_7234])).

tff(c_8531,plain,(
    v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_8382,c_8523])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( ~ v1_xboole_0(B_2)
      | B_2 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_8224,plain,(
    ! [A_1] :
      ( A_1 = '#skF_2'
      | ~ v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_8217,c_4])).

tff(c_8539,plain,(
    '#skF_2' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_8531,c_8224])).

tff(c_7052,plain,(
    ! [A_485] :
      ( v1_funct_2(A_485,k1_relat_1(A_485),k2_relat_1(A_485))
      | ~ v1_funct_1(A_485)
      | ~ v1_relat_1(A_485) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_7055,plain,
    ( v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_7052])).

tff(c_7060,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_26,c_7055])).

tff(c_7063,plain,(
    ~ v1_funct_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_7060])).

tff(c_6989,plain,(
    ! [A_479,B_480] : m1_subset_1('#skF_1'(A_479,B_480),k1_zfmisc_1(k2_zfmisc_1(A_479,B_480))) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_6998,plain,(
    ! [A_3] : m1_subset_1('#skF_1'(A_3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_6989])).

tff(c_7084,plain,(
    ! [C_491,B_492,A_493] :
      ( v1_xboole_0(C_491)
      | ~ m1_subset_1(C_491,k1_zfmisc_1(k2_zfmisc_1(B_492,A_493)))
      | ~ v1_xboole_0(A_493) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_7103,plain,(
    ! [C_491] :
      ( v1_xboole_0(C_491)
      | ~ m1_subset_1(C_491,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_7084])).

tff(c_7114,plain,(
    ! [C_495] :
      ( v1_xboole_0(C_495)
      | ~ m1_subset_1(C_495,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_7103])).

tff(c_7129,plain,(
    ! [A_496] : v1_xboole_0('#skF_1'(A_496,k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_6998,c_7114])).

tff(c_7149,plain,(
    ! [A_498] : '#skF_1'(A_498,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_7129,c_138])).

tff(c_58,plain,(
    ! [A_36,B_37] : v1_funct_1('#skF_1'(A_36,B_37)) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_7170,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_7149,c_58])).

tff(c_7179,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7063,c_7170])).

tff(c_7180,plain,(
    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_7060])).

tff(c_8228,plain,(
    v1_funct_2('#skF_2','#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8223,c_8223,c_8223,c_7180])).

tff(c_8549,plain,(
    v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8539,c_8539,c_8539,c_8228])).

tff(c_8242,plain,(
    k1_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8223,c_8223,c_26])).

tff(c_8216,plain,(
    v1_xboole_0(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_7229])).

tff(c_8267,plain,(
    ! [A_596] :
      ( A_596 = '#skF_2'
      | ~ v1_xboole_0(A_596) ) ),
    inference(resolution,[status(thm)],[c_8217,c_4])).

tff(c_8274,plain,(
    k2_funct_1('#skF_4') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_8216,c_8267])).

tff(c_8317,plain,
    ( k2_relat_1('#skF_4') = k1_relat_1('#skF_2')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_8274,c_38])).

tff(c_8327,plain,(
    k2_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_232,c_84,c_78,c_8242,c_8317])).

tff(c_8557,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8539,c_8327])).

tff(c_12,plain,(
    ! [A_5] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_8238,plain,(
    ! [A_5] : m1_subset_1('#skF_2',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8223,c_12])).

tff(c_8734,plain,(
    ! [A_616] : m1_subset_1('#skF_4',k1_zfmisc_1(A_616)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8539,c_8238])).

tff(c_44,plain,(
    ! [A_30,B_31,C_32] :
      ( k2_relset_1(A_30,B_31,C_32) = k2_relat_1(C_32)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_8738,plain,(
    ! [A_30,B_31] : k2_relset_1(A_30,B_31,'#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_8734,c_44])).

tff(c_8756,plain,(
    ! [A_30,B_31] : k2_relset_1(A_30,B_31,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8557,c_8738])).

tff(c_8566,plain,(
    k2_relset_1('#skF_4','#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8539,c_76])).

tff(c_8824,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8756,c_8566])).

tff(c_8309,plain,(
    ~ v1_funct_2('#skF_2','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8274,c_6970])).

tff(c_8548,plain,(
    ~ v1_funct_2('#skF_4','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8539,c_8539,c_8309])).

tff(c_8832,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8824,c_8548])).

tff(c_8837,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8549,c_8832])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:18:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.46/2.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.85/2.37  
% 6.85/2.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.85/2.37  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 6.85/2.37  
% 6.85/2.37  %Foreground sorts:
% 6.85/2.37  
% 6.85/2.37  
% 6.85/2.37  %Background operators:
% 6.85/2.37  
% 6.85/2.37  
% 6.85/2.37  %Foreground operators:
% 6.85/2.37  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.85/2.37  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.85/2.37  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 6.85/2.37  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.85/2.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.85/2.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.85/2.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.85/2.37  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.85/2.37  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.85/2.37  tff('#skF_2', type, '#skF_2': $i).
% 6.85/2.37  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 6.85/2.37  tff('#skF_3', type, '#skF_3': $i).
% 6.85/2.37  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.85/2.37  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.85/2.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.85/2.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.85/2.37  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 6.85/2.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.85/2.37  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.85/2.37  tff('#skF_4', type, '#skF_4': $i).
% 6.85/2.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.85/2.37  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.85/2.37  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.85/2.37  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.85/2.37  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.85/2.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.85/2.37  
% 6.98/2.40  tff(f_174, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 6.98/2.40  tff(f_110, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 6.98/2.40  tff(f_85, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 6.98/2.40  tff(f_57, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 6.98/2.40  tff(f_55, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 6.98/2.40  tff(f_118, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 6.98/2.40  tff(f_103, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 6.98/2.40  tff(f_114, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.98/2.40  tff(f_136, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 6.98/2.40  tff(f_65, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 6.98/2.40  tff(f_61, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 6.98/2.40  tff(f_93, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k10_relat_1(B, A) = k9_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t155_funct_1)).
% 6.98/2.40  tff(f_157, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 6.98/2.40  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 6.98/2.40  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 6.98/2.40  tff(f_40, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 6.98/2.40  tff(f_68, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 6.98/2.40  tff(f_147, axiom, (![A, B]: (?[C]: ((((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & v1_relat_1(C)) & v4_relat_1(C, A)) & v5_relat_1(C, B)) & v1_funct_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_partfun1)).
% 6.98/2.40  tff(f_42, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 6.98/2.40  tff(c_80, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_174])).
% 6.98/2.40  tff(c_391, plain, (![C_94, B_95, A_96]: (v1_xboole_0(C_94) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(B_95, A_96))) | ~v1_xboole_0(A_96))), inference(cnfTransformation, [status(thm)], [f_110])).
% 6.98/2.40  tff(c_409, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_80, c_391])).
% 6.98/2.40  tff(c_414, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_409])).
% 6.98/2.40  tff(c_84, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_174])).
% 6.98/2.40  tff(c_148, plain, (![A_58]: (v1_funct_1(k2_funct_1(A_58)) | ~v1_funct_1(A_58) | ~v1_relat_1(A_58))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.98/2.40  tff(c_74, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_174])).
% 6.98/2.40  tff(c_139, plain, (~v1_funct_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_74])).
% 6.98/2.40  tff(c_151, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_148, c_139])).
% 6.98/2.40  tff(c_154, plain, (~v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_151])).
% 6.98/2.40  tff(c_18, plain, (![A_12, B_13]: (v1_relat_1(k2_zfmisc_1(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.98/2.40  tff(c_182, plain, (![B_64, A_65]: (v1_relat_1(B_64) | ~m1_subset_1(B_64, k1_zfmisc_1(A_65)) | ~v1_relat_1(A_65))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.98/2.40  tff(c_194, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_80, c_182])).
% 6.98/2.40  tff(c_209, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_194])).
% 6.98/2.40  tff(c_211, plain, $false, inference(negUnitSimplification, [status(thm)], [c_154, c_209])).
% 6.98/2.40  tff(c_212, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_74])).
% 6.98/2.40  tff(c_235, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_212])).
% 6.98/2.40  tff(c_223, plain, (![B_70, A_71]: (v1_relat_1(B_70) | ~m1_subset_1(B_70, k1_zfmisc_1(A_71)) | ~v1_relat_1(A_71))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.98/2.40  tff(c_226, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_80, c_223])).
% 6.98/2.40  tff(c_232, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_226])).
% 6.98/2.40  tff(c_78, plain, (v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_174])).
% 6.98/2.40  tff(c_76, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_174])).
% 6.98/2.40  tff(c_619, plain, (![A_111, B_112, C_113]: (k2_relset_1(A_111, B_112, C_113)=k2_relat_1(C_113) | ~m1_subset_1(C_113, k1_zfmisc_1(k2_zfmisc_1(A_111, B_112))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 6.98/2.40  tff(c_628, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_80, c_619])).
% 6.98/2.40  tff(c_642, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_628])).
% 6.98/2.40  tff(c_38, plain, (![A_22]: (k1_relat_1(k2_funct_1(A_22))=k2_relat_1(A_22) | ~v2_funct_1(A_22) | ~v1_funct_1(A_22) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.98/2.40  tff(c_32, plain, (![A_19]: (v1_relat_1(k2_funct_1(A_19)) | ~v1_funct_1(A_19) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.98/2.40  tff(c_82, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_174])).
% 6.98/2.40  tff(c_676, plain, (![A_116, B_117, C_118]: (k1_relset_1(A_116, B_117, C_118)=k1_relat_1(C_118) | ~m1_subset_1(C_118, k1_zfmisc_1(k2_zfmisc_1(A_116, B_117))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 6.98/2.40  tff(c_698, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_80, c_676])).
% 6.98/2.40  tff(c_1352, plain, (![B_182, A_183, C_184]: (k1_xboole_0=B_182 | k1_relset_1(A_183, B_182, C_184)=A_183 | ~v1_funct_2(C_184, A_183, B_182) | ~m1_subset_1(C_184, k1_zfmisc_1(k2_zfmisc_1(A_183, B_182))))), inference(cnfTransformation, [status(thm)], [f_136])).
% 6.98/2.40  tff(c_1364, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_80, c_1352])).
% 6.98/2.40  tff(c_1383, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_698, c_1364])).
% 6.98/2.40  tff(c_1387, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitLeft, [status(thm)], [c_1383])).
% 6.98/2.40  tff(c_469, plain, (![A_103]: (k2_relat_1(k2_funct_1(A_103))=k1_relat_1(A_103) | ~v2_funct_1(A_103) | ~v1_funct_1(A_103) | ~v1_relat_1(A_103))), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.98/2.40  tff(c_22, plain, (![A_15]: (k10_relat_1(A_15, k2_relat_1(A_15))=k1_relat_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.98/2.40  tff(c_3296, plain, (![A_263]: (k10_relat_1(k2_funct_1(A_263), k1_relat_1(A_263))=k1_relat_1(k2_funct_1(A_263)) | ~v1_relat_1(k2_funct_1(A_263)) | ~v2_funct_1(A_263) | ~v1_funct_1(A_263) | ~v1_relat_1(A_263))), inference(superposition, [status(thm), theory('equality')], [c_469, c_22])).
% 6.98/2.40  tff(c_3311, plain, (k10_relat_1(k2_funct_1('#skF_4'), '#skF_2')=k1_relat_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1387, c_3296])).
% 6.98/2.40  tff(c_3328, plain, (k10_relat_1(k2_funct_1('#skF_4'), '#skF_2')=k1_relat_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_232, c_84, c_78, c_3311])).
% 6.98/2.40  tff(c_3333, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_3328])).
% 6.98/2.40  tff(c_3336, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_3333])).
% 6.98/2.40  tff(c_3340, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_232, c_84, c_3336])).
% 6.98/2.40  tff(c_3342, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_3328])).
% 6.98/2.40  tff(c_213, plain, (v1_funct_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_74])).
% 6.98/2.40  tff(c_654, plain, (k10_relat_1('#skF_4', '#skF_3')=k1_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_642, c_22])).
% 6.98/2.40  tff(c_662, plain, (k10_relat_1('#skF_4', '#skF_3')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_232, c_654])).
% 6.98/2.40  tff(c_1393, plain, (k10_relat_1('#skF_4', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1387, c_662])).
% 6.98/2.40  tff(c_423, plain, (![A_99]: (k1_relat_1(k2_funct_1(A_99))=k2_relat_1(A_99) | ~v2_funct_1(A_99) | ~v1_funct_1(A_99) | ~v1_relat_1(A_99))), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.98/2.40  tff(c_20, plain, (![A_14]: (k9_relat_1(A_14, k1_relat_1(A_14))=k2_relat_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.98/2.40  tff(c_3599, plain, (![A_287]: (k9_relat_1(k2_funct_1(A_287), k2_relat_1(A_287))=k2_relat_1(k2_funct_1(A_287)) | ~v1_relat_1(k2_funct_1(A_287)) | ~v2_funct_1(A_287) | ~v1_funct_1(A_287) | ~v1_relat_1(A_287))), inference(superposition, [status(thm), theory('equality')], [c_423, c_20])).
% 6.98/2.40  tff(c_3624, plain, (k9_relat_1(k2_funct_1('#skF_4'), '#skF_3')=k2_relat_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_642, c_3599])).
% 6.98/2.40  tff(c_3640, plain, (k9_relat_1(k2_funct_1('#skF_4'), '#skF_3')=k2_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_232, c_84, c_78, c_3342, c_3624])).
% 6.98/2.40  tff(c_34, plain, (![B_21, A_20]: (k9_relat_1(k2_funct_1(B_21), A_20)=k10_relat_1(B_21, A_20) | ~v2_funct_1(B_21) | ~v1_funct_1(B_21) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_93])).
% 6.98/2.40  tff(c_3646, plain, (k2_relat_1(k2_funct_1('#skF_4'))=k10_relat_1('#skF_4', '#skF_3') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3640, c_34])).
% 6.98/2.40  tff(c_3653, plain, (k2_relat_1(k2_funct_1('#skF_4'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_232, c_84, c_78, c_1393, c_3646])).
% 6.98/2.40  tff(c_68, plain, (![A_39]: (m1_subset_1(A_39, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_39), k2_relat_1(A_39)))) | ~v1_funct_1(A_39) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_157])).
% 6.98/2.40  tff(c_3676, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')), '#skF_2'))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_3653, c_68])).
% 6.98/2.40  tff(c_3702, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_3342, c_213, c_3676])).
% 6.98/2.40  tff(c_3771, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_4'), '#skF_2'))) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_38, c_3702])).
% 6.98/2.40  tff(c_3789, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_232, c_84, c_78, c_642, c_3771])).
% 6.98/2.40  tff(c_3791, plain, $false, inference(negUnitSimplification, [status(thm)], [c_235, c_3789])).
% 6.98/2.40  tff(c_3792, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_1383])).
% 6.98/2.40  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 6.98/2.40  tff(c_3831, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3792, c_2])).
% 6.98/2.40  tff(c_3833, plain, $false, inference(negUnitSimplification, [status(thm)], [c_414, c_3831])).
% 6.98/2.40  tff(c_3834, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_409])).
% 6.98/2.40  tff(c_135, plain, (![B_53, A_54]: (~v1_xboole_0(B_53) | B_53=A_54 | ~v1_xboole_0(A_54))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.98/2.40  tff(c_138, plain, (![A_54]: (k1_xboole_0=A_54 | ~v1_xboole_0(A_54))), inference(resolution, [status(thm)], [c_2, c_135])).
% 6.98/2.40  tff(c_3841, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_3834, c_138])).
% 6.98/2.40  tff(c_10, plain, (![B_4]: (k2_zfmisc_1(k1_xboole_0, B_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.98/2.40  tff(c_3864, plain, (![B_4]: (k2_zfmisc_1('#skF_4', B_4)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3841, c_3841, c_10])).
% 6.98/2.40  tff(c_3835, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_409])).
% 6.98/2.40  tff(c_3848, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_3835, c_138])).
% 6.98/2.40  tff(c_3876, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3841, c_3848])).
% 6.98/2.40  tff(c_3879, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_3876, c_235])).
% 6.98/2.40  tff(c_4273, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3864, c_3879])).
% 6.98/2.40  tff(c_26, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.98/2.40  tff(c_3867, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3841, c_3841, c_26])).
% 6.98/2.40  tff(c_3916, plain, (![A_288]: (k2_relat_1(k2_funct_1(A_288))=k1_relat_1(A_288) | ~v2_funct_1(A_288) | ~v1_funct_1(A_288) | ~v1_relat_1(A_288))), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.98/2.40  tff(c_6752, plain, (![A_470]: (k10_relat_1(k2_funct_1(A_470), k1_relat_1(A_470))=k1_relat_1(k2_funct_1(A_470)) | ~v1_relat_1(k2_funct_1(A_470)) | ~v2_funct_1(A_470) | ~v1_funct_1(A_470) | ~v1_relat_1(A_470))), inference(superposition, [status(thm), theory('equality')], [c_3916, c_22])).
% 6.98/2.40  tff(c_6773, plain, (k10_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k1_relat_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3867, c_6752])).
% 6.98/2.40  tff(c_6783, plain, (k10_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k1_relat_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_232, c_84, c_78, c_6773])).
% 6.98/2.40  tff(c_6784, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_6783])).
% 6.98/2.40  tff(c_6787, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_6784])).
% 6.98/2.40  tff(c_6791, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_232, c_84, c_6787])).
% 6.98/2.40  tff(c_6793, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_6783])).
% 6.98/2.40  tff(c_8, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.98/2.40  tff(c_3865, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3841, c_3841, c_8])).
% 6.98/2.40  tff(c_127, plain, (![A_47, B_48]: (v1_relat_1(k2_zfmisc_1(A_47, B_48)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.98/2.40  tff(c_129, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10, c_127])).
% 6.98/2.40  tff(c_24, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.98/2.40  tff(c_254, plain, (![A_73]: (k10_relat_1(A_73, k2_relat_1(A_73))=k1_relat_1(A_73) | ~v1_relat_1(A_73))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.98/2.40  tff(c_263, plain, (k10_relat_1(k1_xboole_0, k1_xboole_0)=k1_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_24, c_254])).
% 6.98/2.40  tff(c_267, plain, (k10_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_129, c_26, c_263])).
% 6.98/2.40  tff(c_3858, plain, (k10_relat_1('#skF_4', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3841, c_3841, c_3841, c_267])).
% 6.98/2.40  tff(c_3866, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3841, c_3841, c_24])).
% 6.98/2.40  tff(c_4004, plain, (![A_293]: (k1_relat_1(k2_funct_1(A_293))=k2_relat_1(A_293) | ~v2_funct_1(A_293) | ~v1_funct_1(A_293) | ~v1_relat_1(A_293))), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.98/2.40  tff(c_6869, plain, (![A_476]: (k9_relat_1(k2_funct_1(A_476), k2_relat_1(A_476))=k2_relat_1(k2_funct_1(A_476)) | ~v1_relat_1(k2_funct_1(A_476)) | ~v2_funct_1(A_476) | ~v1_funct_1(A_476) | ~v1_relat_1(A_476))), inference(superposition, [status(thm), theory('equality')], [c_4004, c_20])).
% 6.98/2.40  tff(c_6897, plain, (k9_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k2_relat_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3866, c_6869])).
% 6.98/2.40  tff(c_6907, plain, (k9_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k2_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_232, c_84, c_78, c_6793, c_6897])).
% 6.98/2.40  tff(c_6911, plain, (k2_relat_1(k2_funct_1('#skF_4'))=k10_relat_1('#skF_4', '#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_6907, c_34])).
% 6.98/2.40  tff(c_6918, plain, (k2_relat_1(k2_funct_1('#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_232, c_84, c_78, c_3858, c_6911])).
% 6.98/2.40  tff(c_6941, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')), '#skF_4'))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_6918, c_68])).
% 6.98/2.40  tff(c_6967, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_6793, c_213, c_3865, c_6941])).
% 6.98/2.40  tff(c_6969, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4273, c_6967])).
% 6.98/2.40  tff(c_6971, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_212])).
% 6.98/2.40  tff(c_7208, plain, (![C_510, B_511, A_512]: (v1_xboole_0(C_510) | ~m1_subset_1(C_510, k1_zfmisc_1(k2_zfmisc_1(B_511, A_512))) | ~v1_xboole_0(A_512))), inference(cnfTransformation, [status(thm)], [f_110])).
% 6.98/2.40  tff(c_7229, plain, (v1_xboole_0(k2_funct_1('#skF_4')) | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_6971, c_7208])).
% 6.98/2.40  tff(c_7272, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_7229])).
% 6.98/2.40  tff(c_7440, plain, (![A_528, B_529, C_530]: (k2_relset_1(A_528, B_529, C_530)=k2_relat_1(C_530) | ~m1_subset_1(C_530, k1_zfmisc_1(k2_zfmisc_1(A_528, B_529))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 6.98/2.40  tff(c_7449, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_80, c_7440])).
% 6.98/2.40  tff(c_7463, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_7449])).
% 6.98/2.40  tff(c_6970, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_212])).
% 6.98/2.40  tff(c_7619, plain, (![A_544, B_545, C_546]: (k1_relset_1(A_544, B_545, C_546)=k1_relat_1(C_546) | ~m1_subset_1(C_546, k1_zfmisc_1(k2_zfmisc_1(A_544, B_545))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 6.98/2.40  tff(c_7640, plain, (k1_relset_1('#skF_3', '#skF_2', k2_funct_1('#skF_4'))=k1_relat_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_6971, c_7619])).
% 6.98/2.40  tff(c_8133, plain, (![B_592, C_593, A_594]: (k1_xboole_0=B_592 | v1_funct_2(C_593, A_594, B_592) | k1_relset_1(A_594, B_592, C_593)!=A_594 | ~m1_subset_1(C_593, k1_zfmisc_1(k2_zfmisc_1(A_594, B_592))))), inference(cnfTransformation, [status(thm)], [f_136])).
% 6.98/2.40  tff(c_8142, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | k1_relset_1('#skF_3', '#skF_2', k2_funct_1('#skF_4'))!='#skF_3'), inference(resolution, [status(thm)], [c_6971, c_8133])).
% 6.98/2.40  tff(c_8160, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | k1_relat_1(k2_funct_1('#skF_4'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_7640, c_8142])).
% 6.98/2.40  tff(c_8161, plain, (k1_xboole_0='#skF_2' | k1_relat_1(k2_funct_1('#skF_4'))!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_6970, c_8160])).
% 6.98/2.40  tff(c_8168, plain, (k1_relat_1(k2_funct_1('#skF_4'))!='#skF_3'), inference(splitLeft, [status(thm)], [c_8161])).
% 6.98/2.40  tff(c_8171, plain, (k2_relat_1('#skF_4')!='#skF_3' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_38, c_8168])).
% 6.98/2.40  tff(c_8174, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_232, c_84, c_78, c_7463, c_8171])).
% 6.98/2.40  tff(c_8175, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_8161])).
% 6.98/2.40  tff(c_8213, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8175, c_2])).
% 6.98/2.40  tff(c_8215, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7272, c_8213])).
% 6.98/2.40  tff(c_8217, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_7229])).
% 6.98/2.40  tff(c_8223, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_8217, c_138])).
% 6.98/2.40  tff(c_8239, plain, (![B_4]: (k2_zfmisc_1('#skF_2', B_4)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8223, c_8223, c_10])).
% 6.98/2.40  tff(c_8382, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_8239, c_80])).
% 6.98/2.40  tff(c_7227, plain, (![C_510]: (v1_xboole_0(C_510) | ~m1_subset_1(C_510, k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_7208])).
% 6.98/2.40  tff(c_7234, plain, (![C_510]: (v1_xboole_0(C_510) | ~m1_subset_1(C_510, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_7227])).
% 6.98/2.40  tff(c_8523, plain, (![C_609]: (v1_xboole_0(C_609) | ~m1_subset_1(C_609, k1_zfmisc_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_8223, c_7234])).
% 6.98/2.40  tff(c_8531, plain, (v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_8382, c_8523])).
% 6.98/2.40  tff(c_4, plain, (![B_2, A_1]: (~v1_xboole_0(B_2) | B_2=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.98/2.40  tff(c_8224, plain, (![A_1]: (A_1='#skF_2' | ~v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_8217, c_4])).
% 6.98/2.40  tff(c_8539, plain, ('#skF_2'='#skF_4'), inference(resolution, [status(thm)], [c_8531, c_8224])).
% 6.98/2.40  tff(c_7052, plain, (![A_485]: (v1_funct_2(A_485, k1_relat_1(A_485), k2_relat_1(A_485)) | ~v1_funct_1(A_485) | ~v1_relat_1(A_485))), inference(cnfTransformation, [status(thm)], [f_157])).
% 6.98/2.40  tff(c_7055, plain, (v1_funct_2(k1_xboole_0, k1_relat_1(k1_xboole_0), k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_24, c_7052])).
% 6.98/2.40  tff(c_7060, plain, (v1_funct_2(k1_xboole_0, k1_xboole_0, k1_xboole_0) | ~v1_funct_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_129, c_26, c_7055])).
% 6.98/2.40  tff(c_7063, plain, (~v1_funct_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_7060])).
% 6.98/2.40  tff(c_6989, plain, (![A_479, B_480]: (m1_subset_1('#skF_1'(A_479, B_480), k1_zfmisc_1(k2_zfmisc_1(A_479, B_480))))), inference(cnfTransformation, [status(thm)], [f_147])).
% 6.98/2.40  tff(c_6998, plain, (![A_3]: (m1_subset_1('#skF_1'(A_3, k1_xboole_0), k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_6989])).
% 6.98/2.40  tff(c_7084, plain, (![C_491, B_492, A_493]: (v1_xboole_0(C_491) | ~m1_subset_1(C_491, k1_zfmisc_1(k2_zfmisc_1(B_492, A_493))) | ~v1_xboole_0(A_493))), inference(cnfTransformation, [status(thm)], [f_110])).
% 6.98/2.40  tff(c_7103, plain, (![C_491]: (v1_xboole_0(C_491) | ~m1_subset_1(C_491, k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_7084])).
% 6.98/2.40  tff(c_7114, plain, (![C_495]: (v1_xboole_0(C_495) | ~m1_subset_1(C_495, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_7103])).
% 6.98/2.40  tff(c_7129, plain, (![A_496]: (v1_xboole_0('#skF_1'(A_496, k1_xboole_0)))), inference(resolution, [status(thm)], [c_6998, c_7114])).
% 6.98/2.40  tff(c_7149, plain, (![A_498]: ('#skF_1'(A_498, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_7129, c_138])).
% 6.98/2.40  tff(c_58, plain, (![A_36, B_37]: (v1_funct_1('#skF_1'(A_36, B_37)))), inference(cnfTransformation, [status(thm)], [f_147])).
% 6.98/2.40  tff(c_7170, plain, (v1_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_7149, c_58])).
% 6.98/2.40  tff(c_7179, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7063, c_7170])).
% 6.98/2.40  tff(c_7180, plain, (v1_funct_2(k1_xboole_0, k1_xboole_0, k1_xboole_0)), inference(splitRight, [status(thm)], [c_7060])).
% 6.98/2.40  tff(c_8228, plain, (v1_funct_2('#skF_2', '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8223, c_8223, c_8223, c_7180])).
% 6.98/2.40  tff(c_8549, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8539, c_8539, c_8539, c_8228])).
% 6.98/2.40  tff(c_8242, plain, (k1_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_8223, c_8223, c_26])).
% 6.98/2.40  tff(c_8216, plain, (v1_xboole_0(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_7229])).
% 6.98/2.40  tff(c_8267, plain, (![A_596]: (A_596='#skF_2' | ~v1_xboole_0(A_596))), inference(resolution, [status(thm)], [c_8217, c_4])).
% 6.98/2.40  tff(c_8274, plain, (k2_funct_1('#skF_4')='#skF_2'), inference(resolution, [status(thm)], [c_8216, c_8267])).
% 6.98/2.40  tff(c_8317, plain, (k2_relat_1('#skF_4')=k1_relat_1('#skF_2') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_8274, c_38])).
% 6.98/2.40  tff(c_8327, plain, (k2_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_232, c_84, c_78, c_8242, c_8317])).
% 6.98/2.40  tff(c_8557, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_8539, c_8327])).
% 6.98/2.40  tff(c_12, plain, (![A_5]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.98/2.40  tff(c_8238, plain, (![A_5]: (m1_subset_1('#skF_2', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_8223, c_12])).
% 6.98/2.40  tff(c_8734, plain, (![A_616]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_616)))), inference(demodulation, [status(thm), theory('equality')], [c_8539, c_8238])).
% 6.98/2.40  tff(c_44, plain, (![A_30, B_31, C_32]: (k2_relset_1(A_30, B_31, C_32)=k2_relat_1(C_32) | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 6.98/2.40  tff(c_8738, plain, (![A_30, B_31]: (k2_relset_1(A_30, B_31, '#skF_4')=k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_8734, c_44])).
% 6.98/2.40  tff(c_8756, plain, (![A_30, B_31]: (k2_relset_1(A_30, B_31, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8557, c_8738])).
% 6.98/2.40  tff(c_8566, plain, (k2_relset_1('#skF_4', '#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_8539, c_76])).
% 6.98/2.40  tff(c_8824, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_8756, c_8566])).
% 6.98/2.40  tff(c_8309, plain, (~v1_funct_2('#skF_2', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8274, c_6970])).
% 6.98/2.40  tff(c_8548, plain, (~v1_funct_2('#skF_4', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8539, c_8539, c_8309])).
% 6.98/2.40  tff(c_8832, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8824, c_8548])).
% 6.98/2.40  tff(c_8837, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8549, c_8832])).
% 6.98/2.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.98/2.40  
% 6.98/2.40  Inference rules
% 6.98/2.40  ----------------------
% 6.98/2.40  #Ref     : 0
% 6.98/2.40  #Sup     : 2091
% 6.98/2.40  #Fact    : 0
% 6.98/2.40  #Define  : 0
% 6.98/2.40  #Split   : 19
% 6.98/2.40  #Chain   : 0
% 6.98/2.40  #Close   : 0
% 6.98/2.40  
% 6.98/2.40  Ordering : KBO
% 6.98/2.40  
% 6.98/2.40  Simplification rules
% 6.98/2.40  ----------------------
% 6.98/2.40  #Subsume      : 506
% 6.98/2.40  #Demod        : 2434
% 6.98/2.40  #Tautology    : 1148
% 6.98/2.40  #SimpNegUnit  : 32
% 6.98/2.40  #BackRed      : 198
% 6.98/2.40  
% 6.98/2.40  #Partial instantiations: 0
% 6.98/2.40  #Strategies tried      : 1
% 6.98/2.40  
% 6.98/2.40  Timing (in seconds)
% 6.98/2.40  ----------------------
% 6.98/2.40  Preprocessing        : 0.34
% 6.98/2.40  Parsing              : 0.18
% 6.98/2.40  CNF conversion       : 0.02
% 6.98/2.40  Main loop            : 1.25
% 6.98/2.40  Inferencing          : 0.41
% 6.98/2.40  Reduction            : 0.44
% 6.98/2.40  Demodulation         : 0.33
% 6.98/2.41  BG Simplification    : 0.05
% 6.98/2.41  Subsumption          : 0.26
% 6.98/2.41  Abstraction          : 0.06
% 6.98/2.41  MUC search           : 0.00
% 6.98/2.41  Cooper               : 0.00
% 6.98/2.41  Total                : 1.67
% 6.98/2.41  Index Insertion      : 0.00
% 6.98/2.41  Index Deletion       : 0.00
% 6.98/2.41  Index Matching       : 0.00
% 6.98/2.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
