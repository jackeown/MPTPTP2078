%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:42 EST 2020

% Result     : Theorem 8.46s
% Output     : CNFRefutation 8.61s
% Verified   : 
% Statistics : Number of formulae       :  256 (4410 expanded)
%              Number of leaves         :   42 (1382 expanded)
%              Depth                    :   18
%              Number of atoms          :  452 (11526 expanded)
%              Number of equality atoms :  169 (4120 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

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

tff(f_156,negated_conjecture,(
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

tff(f_90,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_79,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_65,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_116,axiom,(
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

tff(f_139,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_129,axiom,(
    ! [A,B] :
    ? [C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
      & v1_relat_1(C)
      & v4_relat_1(C,A)
      & v5_relat_1(C,B)
      & v1_funct_1(C)
      & v1_funct_2(C,A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_funct_2)).

tff(f_42,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_40,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_76,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_12586,plain,(
    ! [C_3166,A_3167,B_3168] :
      ( v1_xboole_0(C_3166)
      | ~ m1_subset_1(C_3166,k1_zfmisc_1(k2_zfmisc_1(A_3167,B_3168)))
      | ~ v1_xboole_0(A_3167) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_12602,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_12586])).

tff(c_12605,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_12602])).

tff(c_12532,plain,(
    ! [C_3154,A_3155,B_3156] :
      ( v1_relat_1(C_3154)
      | ~ m1_subset_1(C_3154,k1_zfmisc_1(k2_zfmisc_1(A_3155,B_3156))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_12544,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_76,c_12532])).

tff(c_80,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_74,plain,(
    v2_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_72,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_13956,plain,(
    ! [A_3265,B_3266,C_3267] :
      ( k2_relset_1(A_3265,B_3266,C_3267) = k2_relat_1(C_3267)
      | ~ m1_subset_1(C_3267,k1_zfmisc_1(k2_zfmisc_1(A_3265,B_3266))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_13968,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_76,c_13956])).

tff(c_13977,plain,(
    k2_relat_1('#skF_6') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_13968])).

tff(c_30,plain,(
    ! [A_14] :
      ( k1_relat_1(k2_funct_1(A_14)) = k2_relat_1(A_14)
      | ~ v2_funct_1(A_14)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_122,plain,(
    ! [A_54] :
      ( v1_funct_1(k2_funct_1(A_54))
      | ~ v1_funct_1(A_54)
      | ~ v1_relat_1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_70,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4')))
    | ~ v1_funct_2(k2_funct_1('#skF_6'),'#skF_5','#skF_4')
    | ~ v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_114,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_125,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_122,c_114])).

tff(c_128,plain,(
    ~ v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_125])).

tff(c_177,plain,(
    ! [C_62,A_63,B_64] :
      ( v1_relat_1(C_62)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_183,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_76,c_177])).

tff(c_193,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_128,c_183])).

tff(c_194,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_6'),'#skF_5','#skF_4')
    | ~ m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_222,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_194])).

tff(c_252,plain,(
    ! [C_75,A_76,B_77] :
      ( v1_relat_1(C_75)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_260,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_76,c_252])).

tff(c_494,plain,(
    ! [A_116,B_117,C_118] :
      ( k2_relset_1(A_116,B_117,C_118) = k2_relat_1(C_118)
      | ~ m1_subset_1(C_118,k1_zfmisc_1(k2_zfmisc_1(A_116,B_117))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_500,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_76,c_494])).

tff(c_507,plain,(
    k2_relat_1('#skF_6') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_500])).

tff(c_14,plain,(
    ! [A_11] :
      ( k2_relat_1(A_11) != k1_xboole_0
      | k1_xboole_0 = A_11
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_270,plain,
    ( k2_relat_1('#skF_6') != k1_xboole_0
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_260,c_14])).

tff(c_272,plain,(
    k2_relat_1('#skF_6') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_270])).

tff(c_509,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_507,c_272])).

tff(c_78,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_575,plain,(
    ! [A_122,B_123,C_124] :
      ( k1_relset_1(A_122,B_123,C_124) = k1_relat_1(C_124)
      | ~ m1_subset_1(C_124,k1_zfmisc_1(k2_zfmisc_1(A_122,B_123))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_595,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_76,c_575])).

tff(c_1363,plain,(
    ! [B_169,A_170,C_171] :
      ( k1_xboole_0 = B_169
      | k1_relset_1(A_170,B_169,C_171) = A_170
      | ~ v1_funct_2(C_171,A_170,B_169)
      | ~ m1_subset_1(C_171,k1_zfmisc_1(k2_zfmisc_1(A_170,B_169))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_1375,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_76,c_1363])).

tff(c_1390,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_595,c_1375])).

tff(c_1391,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_509,c_1390])).

tff(c_28,plain,(
    ! [A_14] :
      ( k2_relat_1(k2_funct_1(A_14)) = k1_relat_1(A_14)
      | ~ v2_funct_1(A_14)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_22,plain,(
    ! [A_12] :
      ( v1_relat_1(k2_funct_1(A_12))
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_195,plain,(
    v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_435,plain,(
    ! [A_106] :
      ( k1_relat_1(k2_funct_1(A_106)) = k2_relat_1(A_106)
      | ~ v2_funct_1(A_106)
      | ~ v1_funct_1(A_106)
      | ~ v1_relat_1(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_66,plain,(
    ! [A_34] :
      ( v1_funct_2(A_34,k1_relat_1(A_34),k2_relat_1(A_34))
      | ~ v1_funct_1(A_34)
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_3867,plain,(
    ! [A_1235] :
      ( v1_funct_2(k2_funct_1(A_1235),k2_relat_1(A_1235),k2_relat_1(k2_funct_1(A_1235)))
      | ~ v1_funct_1(k2_funct_1(A_1235))
      | ~ v1_relat_1(k2_funct_1(A_1235))
      | ~ v2_funct_1(A_1235)
      | ~ v1_funct_1(A_1235)
      | ~ v1_relat_1(A_1235) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_435,c_66])).

tff(c_3882,plain,
    ( v1_funct_2(k2_funct_1('#skF_6'),'#skF_5',k2_relat_1(k2_funct_1('#skF_6')))
    | ~ v1_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6'))
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_507,c_3867])).

tff(c_3898,plain,
    ( v1_funct_2(k2_funct_1('#skF_6'),'#skF_5',k2_relat_1(k2_funct_1('#skF_6')))
    | ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_260,c_80,c_74,c_195,c_3882])).

tff(c_3899,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_3898])).

tff(c_3902,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_22,c_3899])).

tff(c_3906,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_260,c_80,c_3902])).

tff(c_3908,plain,(
    v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_3898])).

tff(c_519,plain,(
    ! [A_119] :
      ( m1_subset_1(A_119,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_119),k2_relat_1(A_119))))
      | ~ v1_funct_1(A_119)
      | ~ v1_relat_1(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_5560,plain,(
    ! [A_1272] :
      ( m1_subset_1(k2_funct_1(A_1272),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_1272),k2_relat_1(k2_funct_1(A_1272)))))
      | ~ v1_funct_1(k2_funct_1(A_1272))
      | ~ v1_relat_1(k2_funct_1(A_1272))
      | ~ v2_funct_1(A_1272)
      | ~ v1_funct_1(A_1272)
      | ~ v1_relat_1(A_1272) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_519])).

tff(c_5601,plain,
    ( m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_5',k2_relat_1(k2_funct_1('#skF_6')))))
    | ~ v1_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6'))
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_507,c_5560])).

tff(c_5628,plain,(
    m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_5',k2_relat_1(k2_funct_1('#skF_6'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_260,c_80,c_74,c_3908,c_195,c_5601])).

tff(c_5651,plain,
    ( m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_relat_1('#skF_6'))))
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_5628])).

tff(c_5666,plain,(
    m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_260,c_80,c_74,c_1391,c_5651])).

tff(c_5668,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_222,c_5666])).

tff(c_5669,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_270])).

tff(c_16,plain,(
    ! [A_11] :
      ( k1_relat_1(A_11) != k1_xboole_0
      | k1_xboole_0 = A_11
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_269,plain,
    ( k1_relat_1('#skF_6') != k1_xboole_0
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_260,c_16])).

tff(c_271,plain,(
    k1_relat_1('#skF_6') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_269])).

tff(c_5671,plain,(
    k1_relat_1('#skF_6') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5669,c_271])).

tff(c_52,plain,(
    ! [A_31,B_32] : v1_funct_2('#skF_3'(A_31,B_32),A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_10,plain,(
    ! [A_7] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_5679,plain,(
    ! [A_7] : m1_subset_1('#skF_6',k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5669,c_10])).

tff(c_5997,plain,(
    ! [A_1318,B_1319,C_1320] :
      ( k1_relset_1(A_1318,B_1319,C_1320) = k1_relat_1(C_1320)
      | ~ m1_subset_1(C_1320,k1_zfmisc_1(k2_zfmisc_1(A_1318,B_1319))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_6006,plain,(
    ! [A_1318,B_1319] : k1_relset_1(A_1318,B_1319,'#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_5679,c_5997])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_5683,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5669,c_6])).

tff(c_62,plain,(
    ! [A_31,B_32] : m1_subset_1('#skF_3'(A_31,B_32),k1_zfmisc_1(k2_zfmisc_1(A_31,B_32))) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_5754,plain,(
    ! [C_1281,A_1282,B_1283] :
      ( v1_xboole_0(C_1281)
      | ~ m1_subset_1(C_1281,k1_zfmisc_1(k2_zfmisc_1(A_1282,B_1283)))
      | ~ v1_xboole_0(A_1282) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_5765,plain,(
    ! [A_1284,B_1285] :
      ( v1_xboole_0('#skF_3'(A_1284,B_1285))
      | ~ v1_xboole_0(A_1284) ) ),
    inference(resolution,[status(thm)],[c_62,c_5754])).

tff(c_103,plain,(
    ! [A_48] :
      ( r2_hidden('#skF_2'(A_48),A_48)
      | k1_xboole_0 = A_48 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_107,plain,(
    ! [A_48] :
      ( ~ v1_xboole_0(A_48)
      | k1_xboole_0 = A_48 ) ),
    inference(resolution,[status(thm)],[c_103,c_2])).

tff(c_5677,plain,(
    ! [A_48] :
      ( ~ v1_xboole_0(A_48)
      | A_48 = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5669,c_107])).

tff(c_5770,plain,(
    ! [A_1286,B_1287] :
      ( '#skF_3'(A_1286,B_1287) = '#skF_6'
      | ~ v1_xboole_0(A_1286) ) ),
    inference(resolution,[status(thm)],[c_5765,c_5677])).

tff(c_5776,plain,(
    ! [B_1287] : '#skF_3'('#skF_6',B_1287) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_5683,c_5770])).

tff(c_48,plain,(
    ! [B_29,C_30] :
      ( k1_relset_1(k1_xboole_0,B_29,C_30) = k1_xboole_0
      | ~ v1_funct_2(C_30,k1_xboole_0,B_29)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_6456,plain,(
    ! [B_1349,C_1350] :
      ( k1_relset_1('#skF_6',B_1349,C_1350) = '#skF_6'
      | ~ v1_funct_2(C_1350,'#skF_6',B_1349)
      | ~ m1_subset_1(C_1350,k1_zfmisc_1(k2_zfmisc_1('#skF_6',B_1349))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5669,c_5669,c_5669,c_5669,c_48])).

tff(c_6460,plain,(
    ! [B_32] :
      ( k1_relset_1('#skF_6',B_32,'#skF_3'('#skF_6',B_32)) = '#skF_6'
      | ~ v1_funct_2('#skF_3'('#skF_6',B_32),'#skF_6',B_32) ) ),
    inference(resolution,[status(thm)],[c_62,c_6456])).

tff(c_6467,plain,(
    k1_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_6006,c_5776,c_6460])).

tff(c_6469,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5671,c_6467])).

tff(c_6470,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_269])).

tff(c_6479,plain,(
    ! [A_7] : m1_subset_1('#skF_6',k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6470,c_10])).

tff(c_6471,plain,(
    k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_269])).

tff(c_6490,plain,(
    k1_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6470,c_6471])).

tff(c_6773,plain,(
    ! [A_1391,B_1392,C_1393] :
      ( k1_relset_1(A_1391,B_1392,C_1393) = k1_relat_1(C_1393)
      | ~ m1_subset_1(C_1393,k1_zfmisc_1(k2_zfmisc_1(A_1391,B_1392))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_6780,plain,(
    ! [A_1391,B_1392] : k1_relset_1(A_1391,B_1392,'#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_6479,c_6773])).

tff(c_6783,plain,(
    ! [A_1391,B_1392] : k1_relset_1(A_1391,B_1392,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6490,c_6780])).

tff(c_50,plain,(
    ! [B_29,A_28,C_30] :
      ( k1_xboole_0 = B_29
      | k1_relset_1(A_28,B_29,C_30) = A_28
      | ~ v1_funct_2(C_30,A_28,B_29)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_7684,plain,(
    ! [B_1443,A_1444,C_1445] :
      ( B_1443 = '#skF_6'
      | k1_relset_1(A_1444,B_1443,C_1445) = A_1444
      | ~ v1_funct_2(C_1445,A_1444,B_1443)
      | ~ m1_subset_1(C_1445,k1_zfmisc_1(k2_zfmisc_1(A_1444,B_1443))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6470,c_50])).

tff(c_7694,plain,(
    ! [B_1443,A_1444] :
      ( B_1443 = '#skF_6'
      | k1_relset_1(A_1444,B_1443,'#skF_6') = A_1444
      | ~ v1_funct_2('#skF_6',A_1444,B_1443) ) ),
    inference(resolution,[status(thm)],[c_6479,c_7684])).

tff(c_7770,plain,(
    ! [B_1448,A_1449] :
      ( B_1448 = '#skF_6'
      | A_1449 = '#skF_6'
      | ~ v1_funct_2('#skF_6',A_1449,B_1448) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6783,c_7694])).

tff(c_7799,plain,
    ( '#skF_5' = '#skF_6'
    | '#skF_6' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_78,c_7770])).

tff(c_7800,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_7799])).

tff(c_7840,plain,(
    ! [A_7] : m1_subset_1('#skF_4',k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7800,c_6479])).

tff(c_7842,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7800,c_7800,c_6490])).

tff(c_7845,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7800,c_260])).

tff(c_7850,plain,(
    v1_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7800,c_80])).

tff(c_7849,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7800,c_74])).

tff(c_7847,plain,(
    v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7800,c_195])).

tff(c_6808,plain,(
    ! [A_1398,B_1399,C_1400] :
      ( k2_relset_1(A_1398,B_1399,C_1400) = k2_relat_1(C_1400)
      | ~ m1_subset_1(C_1400,k1_zfmisc_1(k2_zfmisc_1(A_1398,B_1399))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_6818,plain,(
    ! [A_1401,B_1402] : k2_relset_1(A_1401,B_1402,'#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_6479,c_6808])).

tff(c_6822,plain,(
    k2_relat_1('#skF_6') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_6818,c_72])).

tff(c_7820,plain,(
    k2_relat_1('#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7800,c_6822])).

tff(c_6720,plain,(
    ! [A_1381] :
      ( k1_relat_1(k2_funct_1(A_1381)) = k2_relat_1(A_1381)
      | ~ v2_funct_1(A_1381)
      | ~ v1_funct_1(A_1381)
      | ~ v1_relat_1(A_1381) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_8967,plain,(
    ! [A_2303] :
      ( v1_funct_2(k2_funct_1(A_2303),k2_relat_1(A_2303),k2_relat_1(k2_funct_1(A_2303)))
      | ~ v1_funct_1(k2_funct_1(A_2303))
      | ~ v1_relat_1(k2_funct_1(A_2303))
      | ~ v2_funct_1(A_2303)
      | ~ v1_funct_1(A_2303)
      | ~ v1_relat_1(A_2303) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6720,c_66])).

tff(c_8973,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_5',k2_relat_1(k2_funct_1('#skF_4')))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_7820,c_8967])).

tff(c_8986,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_5',k2_relat_1(k2_funct_1('#skF_4')))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7845,c_7850,c_7849,c_7847,c_8973])).

tff(c_9146,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_8986])).

tff(c_9149,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_9146])).

tff(c_9153,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7845,c_7850,c_9149])).

tff(c_9155,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_8986])).

tff(c_6475,plain,(
    ! [A_11] :
      ( k2_relat_1(A_11) != '#skF_6'
      | A_11 = '#skF_6'
      | ~ v1_relat_1(A_11) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6470,c_6470,c_14])).

tff(c_7830,plain,(
    ! [A_11] :
      ( k2_relat_1(A_11) != '#skF_4'
      | A_11 = '#skF_4'
      | ~ v1_relat_1(A_11) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7800,c_7800,c_6475])).

tff(c_9163,plain,
    ( k2_relat_1(k2_funct_1('#skF_4')) != '#skF_4'
    | k2_funct_1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_9155,c_7830])).

tff(c_9202,plain,(
    k2_relat_1(k2_funct_1('#skF_4')) != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_9163])).

tff(c_9205,plain,
    ( k1_relat_1('#skF_4') != '#skF_4'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_9202])).

tff(c_9208,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7845,c_7850,c_7849,c_7842,c_9205])).

tff(c_9209,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_9163])).

tff(c_6474,plain,(
    ! [A_11] :
      ( k1_relat_1(A_11) != '#skF_6'
      | A_11 = '#skF_6'
      | ~ v1_relat_1(A_11) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6470,c_6470,c_16])).

tff(c_7829,plain,(
    ! [A_11] :
      ( k1_relat_1(A_11) != '#skF_4'
      | A_11 = '#skF_4'
      | ~ v1_relat_1(A_11) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7800,c_7800,c_6474])).

tff(c_9162,plain,
    ( k1_relat_1(k2_funct_1('#skF_4')) != '#skF_4'
    | k2_funct_1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_9155,c_7829])).

tff(c_9169,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_9162])).

tff(c_9212,plain,(
    k1_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9209,c_9169])).

tff(c_9221,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7842,c_9212])).

tff(c_9222,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_9162])).

tff(c_7846,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7800,c_222])).

tff(c_9227,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9222,c_7846])).

tff(c_9233,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7840,c_9227])).

tff(c_9234,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_7799])).

tff(c_9240,plain,(
    k2_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9234,c_6822])).

tff(c_223,plain,(
    ! [A_71] :
      ( k1_relat_1(A_71) != k1_xboole_0
      | k1_xboole_0 = A_71
      | ~ v1_relat_1(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_236,plain,(
    ! [A_12] :
      ( k1_relat_1(k2_funct_1(A_12)) != k1_xboole_0
      | k2_funct_1(A_12) = k1_xboole_0
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(resolution,[status(thm)],[c_22,c_223])).

tff(c_9692,plain,(
    ! [A_3083] :
      ( k1_relat_1(k2_funct_1(A_3083)) != '#skF_6'
      | k2_funct_1(A_3083) = '#skF_6'
      | ~ v1_funct_1(A_3083)
      | ~ v1_relat_1(A_3083) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6470,c_6470,c_236])).

tff(c_12499,plain,(
    ! [A_3151] :
      ( k2_relat_1(A_3151) != '#skF_6'
      | k2_funct_1(A_3151) = '#skF_6'
      | ~ v1_funct_1(A_3151)
      | ~ v1_relat_1(A_3151)
      | ~ v2_funct_1(A_3151)
      | ~ v1_funct_1(A_3151)
      | ~ v1_relat_1(A_3151) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_9692])).

tff(c_12502,plain,
    ( k2_relat_1('#skF_6') != '#skF_6'
    | k2_funct_1('#skF_6') = '#skF_6'
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_74,c_12499])).

tff(c_12505,plain,(
    k2_funct_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_260,c_80,c_9240,c_12502])).

tff(c_9241,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9234,c_222])).

tff(c_12506,plain,(
    ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12505,c_9241])).

tff(c_12510,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6479,c_12506])).

tff(c_12511,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_6'),'#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_194])).

tff(c_12512,plain,(
    m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_194])).

tff(c_13291,plain,(
    ! [A_3224,B_3225,C_3226] :
      ( k1_relset_1(A_3224,B_3225,C_3226) = k1_relat_1(C_3226)
      | ~ m1_subset_1(C_3226,k1_zfmisc_1(k2_zfmisc_1(A_3224,B_3225))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_13306,plain,(
    k1_relset_1('#skF_5','#skF_4',k2_funct_1('#skF_6')) = k1_relat_1(k2_funct_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_12512,c_13291])).

tff(c_14935,plain,(
    ! [B_3306,C_3307,A_3308] :
      ( k1_xboole_0 = B_3306
      | v1_funct_2(C_3307,A_3308,B_3306)
      | k1_relset_1(A_3308,B_3306,C_3307) != A_3308
      | ~ m1_subset_1(C_3307,k1_zfmisc_1(k2_zfmisc_1(A_3308,B_3306))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_14947,plain,
    ( k1_xboole_0 = '#skF_4'
    | v1_funct_2(k2_funct_1('#skF_6'),'#skF_5','#skF_4')
    | k1_relset_1('#skF_5','#skF_4',k2_funct_1('#skF_6')) != '#skF_5' ),
    inference(resolution,[status(thm)],[c_12512,c_14935])).

tff(c_14963,plain,
    ( k1_xboole_0 = '#skF_4'
    | v1_funct_2(k2_funct_1('#skF_6'),'#skF_5','#skF_4')
    | k1_relat_1(k2_funct_1('#skF_6')) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13306,c_14947])).

tff(c_14964,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1(k2_funct_1('#skF_6')) != '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_12511,c_14963])).

tff(c_14970,plain,(
    k1_relat_1(k2_funct_1('#skF_6')) != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_14964])).

tff(c_14973,plain,
    ( k2_relat_1('#skF_6') != '#skF_5'
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_14970])).

tff(c_14976,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12544,c_80,c_74,c_13977,c_14973])).

tff(c_14977,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_14964])).

tff(c_15028,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14977,c_6])).

tff(c_15030,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12605,c_15028])).

tff(c_15032,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_12602])).

tff(c_15040,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_15032,c_107])).

tff(c_15031,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_12602])).

tff(c_15036,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_15031,c_107])).

tff(c_15066,plain,(
    '#skF_6' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15040,c_15036])).

tff(c_12553,plain,
    ( k1_relat_1('#skF_6') != k1_xboole_0
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_12544,c_16])).

tff(c_12563,plain,(
    k1_relat_1('#skF_6') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_12553])).

tff(c_15048,plain,(
    k1_relat_1('#skF_6') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15036,c_12563])).

tff(c_15102,plain,(
    k1_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15066,c_15066,c_15048])).

tff(c_15153,plain,(
    ! [A_3315,B_3316] :
      ( v1_xboole_0('#skF_3'(A_3315,B_3316))
      | ~ v1_xboole_0(A_3315) ) ),
    inference(resolution,[status(thm)],[c_62,c_12586])).

tff(c_15052,plain,(
    ! [A_48] :
      ( ~ v1_xboole_0(A_48)
      | A_48 = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15036,c_107])).

tff(c_15104,plain,(
    ! [A_48] :
      ( ~ v1_xboole_0(A_48)
      | A_48 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15066,c_15052])).

tff(c_15184,plain,(
    ! [A_3320,B_3321] :
      ( '#skF_3'(A_3320,B_3321) = '#skF_4'
      | ~ v1_xboole_0(A_3320) ) ),
    inference(resolution,[status(thm)],[c_15153,c_15104])).

tff(c_15191,plain,(
    ! [B_3322] : '#skF_3'('#skF_4',B_3322) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_15032,c_15184])).

tff(c_15202,plain,(
    ! [B_3322] : v1_funct_2('#skF_4','#skF_4',B_3322) ),
    inference(superposition,[status(thm),theory(equality)],[c_15191,c_52])).

tff(c_15054,plain,(
    ! [A_7] : m1_subset_1('#skF_6',k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15036,c_10])).

tff(c_15123,plain,(
    ! [A_7] : m1_subset_1('#skF_4',k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15066,c_15054])).

tff(c_15242,plain,(
    ! [A_3328,B_3329,C_3330] :
      ( k1_relset_1(A_3328,B_3329,C_3330) = k1_relat_1(C_3330)
      | ~ m1_subset_1(C_3330,k1_zfmisc_1(k2_zfmisc_1(A_3328,B_3329))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_15250,plain,(
    ! [A_3328,B_3329] : k1_relset_1(A_3328,B_3329,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_15123,c_15242])).

tff(c_15707,plain,(
    ! [B_3365,C_3366] :
      ( k1_relset_1('#skF_4',B_3365,C_3366) = '#skF_4'
      | ~ v1_funct_2(C_3366,'#skF_4',B_3365)
      | ~ m1_subset_1(C_3366,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_3365))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15040,c_15040,c_15040,c_15040,c_48])).

tff(c_15711,plain,(
    ! [B_3365] :
      ( k1_relset_1('#skF_4',B_3365,'#skF_4') = '#skF_4'
      | ~ v1_funct_2('#skF_4','#skF_4',B_3365) ) ),
    inference(resolution,[status(thm)],[c_15123,c_15707])).

tff(c_15718,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15202,c_15250,c_15711])).

tff(c_15720,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_15102,c_15718])).

tff(c_15721,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_12553])).

tff(c_15732,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15721,c_6])).

tff(c_16149,plain,(
    ! [C_3412,A_3413,B_3414] :
      ( v1_xboole_0(C_3412)
      | ~ m1_subset_1(C_3412,k1_zfmisc_1(k2_zfmisc_1(A_3413,B_3414)))
      | ~ v1_xboole_0(A_3413) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_16160,plain,(
    ! [A_3415,B_3416] :
      ( v1_xboole_0('#skF_3'(A_3415,B_3416))
      | ~ v1_xboole_0(A_3415) ) ),
    inference(resolution,[status(thm)],[c_62,c_16149])).

tff(c_15726,plain,(
    ! [A_48] :
      ( ~ v1_xboole_0(A_48)
      | A_48 = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15721,c_107])).

tff(c_16165,plain,(
    ! [A_3417,B_3418] :
      ( '#skF_3'(A_3417,B_3418) = '#skF_6'
      | ~ v1_xboole_0(A_3417) ) ),
    inference(resolution,[status(thm)],[c_16160,c_15726])).

tff(c_16172,plain,(
    ! [B_3419] : '#skF_3'('#skF_6',B_3419) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_15732,c_16165])).

tff(c_16186,plain,(
    ! [B_3419] : v1_funct_2('#skF_6','#skF_6',B_3419) ),
    inference(superposition,[status(thm),theory(equality)],[c_16172,c_52])).

tff(c_15722,plain,(
    k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_12553])).

tff(c_15739,plain,(
    k1_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15721,c_15722])).

tff(c_16031,plain,(
    ! [A_3406] :
      ( k2_relat_1(k2_funct_1(A_3406)) = k1_relat_1(A_3406)
      | ~ v2_funct_1(A_3406)
      | ~ v1_funct_1(A_3406)
      | ~ v1_relat_1(A_3406) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_12543,plain,(
    v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_12512,c_12532])).

tff(c_12562,plain,
    ( k2_relat_1(k2_funct_1('#skF_6')) != k1_xboole_0
    | k2_funct_1('#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12543,c_14])).

tff(c_15796,plain,
    ( k2_relat_1(k2_funct_1('#skF_6')) != '#skF_6'
    | k2_funct_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15721,c_15721,c_12562])).

tff(c_15797,plain,(
    k2_relat_1(k2_funct_1('#skF_6')) != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_15796])).

tff(c_16040,plain,
    ( k1_relat_1('#skF_6') != '#skF_6'
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_16031,c_15797])).

tff(c_16047,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12544,c_80,c_74,c_15739,c_16040])).

tff(c_16048,plain,(
    k2_funct_1('#skF_6') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_15796])).

tff(c_12561,plain,
    ( k1_relat_1(k2_funct_1('#skF_6')) != k1_xboole_0
    | k2_funct_1('#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12543,c_16])).

tff(c_15794,plain,
    ( k1_relat_1(k2_funct_1('#skF_6')) != '#skF_6'
    | k2_funct_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15721,c_15721,c_12561])).

tff(c_15795,plain,(
    k1_relat_1(k2_funct_1('#skF_6')) != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_15794])).

tff(c_16077,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15739,c_16048,c_15795])).

tff(c_16078,plain,(
    k2_funct_1('#skF_6') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_15794])).

tff(c_16280,plain,(
    ! [A_3430] :
      ( k1_relat_1(k2_funct_1(A_3430)) = k2_relat_1(A_3430)
      | ~ v2_funct_1(A_3430)
      | ~ v1_funct_1(A_3430)
      | ~ v1_relat_1(A_3430) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_16292,plain,
    ( k2_relat_1('#skF_6') = k1_relat_1('#skF_6')
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_16078,c_16280])).

tff(c_16296,plain,(
    k2_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12544,c_80,c_74,c_15739,c_16292])).

tff(c_15728,plain,(
    ! [A_7] : m1_subset_1('#skF_6',k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15721,c_10])).

tff(c_16382,plain,(
    ! [A_3443,B_3444,C_3445] :
      ( k2_relset_1(A_3443,B_3444,C_3445) = k2_relat_1(C_3445)
      | ~ m1_subset_1(C_3445,k1_zfmisc_1(k2_zfmisc_1(A_3443,B_3444))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_16389,plain,(
    ! [A_3443,B_3444] : k2_relset_1(A_3443,B_3444,'#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_15728,c_16382])).

tff(c_16392,plain,(
    ! [A_3443,B_3444] : k2_relset_1(A_3443,B_3444,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16296,c_16389])).

tff(c_16393,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16392,c_72])).

tff(c_16082,plain,(
    ~ v1_funct_2('#skF_6','#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16078,c_12511])).

tff(c_16401,plain,(
    ~ v1_funct_2('#skF_6','#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16393,c_16082])).

tff(c_16405,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16186,c_16401])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:26:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.46/2.89  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.61/2.92  
% 8.61/2.92  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.61/2.93  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4
% 8.61/2.93  
% 8.61/2.93  %Foreground sorts:
% 8.61/2.93  
% 8.61/2.93  
% 8.61/2.93  %Background operators:
% 8.61/2.93  
% 8.61/2.93  
% 8.61/2.93  %Foreground operators:
% 8.61/2.93  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 8.61/2.93  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.61/2.93  tff('#skF_2', type, '#skF_2': $i > $i).
% 8.61/2.93  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 8.61/2.93  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 8.61/2.93  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.61/2.93  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.61/2.93  tff('#skF_1', type, '#skF_1': $i > $i).
% 8.61/2.93  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.61/2.93  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 8.61/2.93  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.61/2.93  tff('#skF_5', type, '#skF_5': $i).
% 8.61/2.93  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.61/2.93  tff('#skF_6', type, '#skF_6': $i).
% 8.61/2.93  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 8.61/2.93  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 8.61/2.93  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.61/2.93  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.61/2.93  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.61/2.93  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.61/2.93  tff('#skF_4', type, '#skF_4': $i).
% 8.61/2.93  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 8.61/2.93  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.61/2.93  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 8.61/2.93  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.61/2.93  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.61/2.93  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.61/2.93  
% 8.61/2.96  tff(f_156, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 8.61/2.96  tff(f_90, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc3_relset_1)).
% 8.61/2.96  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 8.61/2.96  tff(f_98, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 8.61/2.96  tff(f_79, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 8.61/2.96  tff(f_65, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 8.61/2.96  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 8.61/2.96  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 8.61/2.96  tff(f_116, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 8.61/2.96  tff(f_139, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 8.61/2.96  tff(f_129, axiom, (![A, B]: (?[C]: (((((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & v1_relat_1(C)) & v4_relat_1(C, A)) & v5_relat_1(C, B)) & v1_funct_1(C)) & v1_funct_2(C, A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_funct_2)).
% 8.61/2.96  tff(f_42, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 8.61/2.96  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 8.61/2.96  tff(f_40, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 8.61/2.96  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 8.61/2.96  tff(c_76, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_156])).
% 8.61/2.96  tff(c_12586, plain, (![C_3166, A_3167, B_3168]: (v1_xboole_0(C_3166) | ~m1_subset_1(C_3166, k1_zfmisc_1(k2_zfmisc_1(A_3167, B_3168))) | ~v1_xboole_0(A_3167))), inference(cnfTransformation, [status(thm)], [f_90])).
% 8.61/2.96  tff(c_12602, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_76, c_12586])).
% 8.61/2.96  tff(c_12605, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_12602])).
% 8.61/2.96  tff(c_12532, plain, (![C_3154, A_3155, B_3156]: (v1_relat_1(C_3154) | ~m1_subset_1(C_3154, k1_zfmisc_1(k2_zfmisc_1(A_3155, B_3156))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 8.61/2.96  tff(c_12544, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_76, c_12532])).
% 8.61/2.96  tff(c_80, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_156])).
% 8.61/2.96  tff(c_74, plain, (v2_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_156])).
% 8.61/2.96  tff(c_72, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_5'), inference(cnfTransformation, [status(thm)], [f_156])).
% 8.61/2.96  tff(c_13956, plain, (![A_3265, B_3266, C_3267]: (k2_relset_1(A_3265, B_3266, C_3267)=k2_relat_1(C_3267) | ~m1_subset_1(C_3267, k1_zfmisc_1(k2_zfmisc_1(A_3265, B_3266))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 8.61/2.96  tff(c_13968, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_76, c_13956])).
% 8.61/2.96  tff(c_13977, plain, (k2_relat_1('#skF_6')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_13968])).
% 8.61/2.96  tff(c_30, plain, (![A_14]: (k1_relat_1(k2_funct_1(A_14))=k2_relat_1(A_14) | ~v2_funct_1(A_14) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_79])).
% 8.61/2.96  tff(c_122, plain, (![A_54]: (v1_funct_1(k2_funct_1(A_54)) | ~v1_funct_1(A_54) | ~v1_relat_1(A_54))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.61/2.96  tff(c_70, plain, (~m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4'))) | ~v1_funct_2(k2_funct_1('#skF_6'), '#skF_5', '#skF_4') | ~v1_funct_1(k2_funct_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_156])).
% 8.61/2.96  tff(c_114, plain, (~v1_funct_1(k2_funct_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_70])).
% 8.61/2.96  tff(c_125, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_122, c_114])).
% 8.61/2.96  tff(c_128, plain, (~v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_125])).
% 8.61/2.96  tff(c_177, plain, (![C_62, A_63, B_64]: (v1_relat_1(C_62) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 8.61/2.96  tff(c_183, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_76, c_177])).
% 8.61/2.96  tff(c_193, plain, $false, inference(negUnitSimplification, [status(thm)], [c_128, c_183])).
% 8.61/2.96  tff(c_194, plain, (~v1_funct_2(k2_funct_1('#skF_6'), '#skF_5', '#skF_4') | ~m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4')))), inference(splitRight, [status(thm)], [c_70])).
% 8.61/2.96  tff(c_222, plain, (~m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4')))), inference(splitLeft, [status(thm)], [c_194])).
% 8.61/2.96  tff(c_252, plain, (![C_75, A_76, B_77]: (v1_relat_1(C_75) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 8.61/2.96  tff(c_260, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_76, c_252])).
% 8.61/2.96  tff(c_494, plain, (![A_116, B_117, C_118]: (k2_relset_1(A_116, B_117, C_118)=k2_relat_1(C_118) | ~m1_subset_1(C_118, k1_zfmisc_1(k2_zfmisc_1(A_116, B_117))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 8.61/2.96  tff(c_500, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_76, c_494])).
% 8.61/2.96  tff(c_507, plain, (k2_relat_1('#skF_6')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_500])).
% 8.61/2.96  tff(c_14, plain, (![A_11]: (k2_relat_1(A_11)!=k1_xboole_0 | k1_xboole_0=A_11 | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_56])).
% 8.61/2.96  tff(c_270, plain, (k2_relat_1('#skF_6')!=k1_xboole_0 | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_260, c_14])).
% 8.61/2.96  tff(c_272, plain, (k2_relat_1('#skF_6')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_270])).
% 8.61/2.96  tff(c_509, plain, (k1_xboole_0!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_507, c_272])).
% 8.61/2.96  tff(c_78, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_156])).
% 8.61/2.96  tff(c_575, plain, (![A_122, B_123, C_124]: (k1_relset_1(A_122, B_123, C_124)=k1_relat_1(C_124) | ~m1_subset_1(C_124, k1_zfmisc_1(k2_zfmisc_1(A_122, B_123))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 8.61/2.96  tff(c_595, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_76, c_575])).
% 8.61/2.96  tff(c_1363, plain, (![B_169, A_170, C_171]: (k1_xboole_0=B_169 | k1_relset_1(A_170, B_169, C_171)=A_170 | ~v1_funct_2(C_171, A_170, B_169) | ~m1_subset_1(C_171, k1_zfmisc_1(k2_zfmisc_1(A_170, B_169))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 8.61/2.96  tff(c_1375, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_76, c_1363])).
% 8.61/2.96  tff(c_1390, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_595, c_1375])).
% 8.61/2.96  tff(c_1391, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_509, c_1390])).
% 8.61/2.96  tff(c_28, plain, (![A_14]: (k2_relat_1(k2_funct_1(A_14))=k1_relat_1(A_14) | ~v2_funct_1(A_14) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_79])).
% 8.61/2.96  tff(c_22, plain, (![A_12]: (v1_relat_1(k2_funct_1(A_12)) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.61/2.96  tff(c_195, plain, (v1_funct_1(k2_funct_1('#skF_6'))), inference(splitRight, [status(thm)], [c_70])).
% 8.61/2.96  tff(c_435, plain, (![A_106]: (k1_relat_1(k2_funct_1(A_106))=k2_relat_1(A_106) | ~v2_funct_1(A_106) | ~v1_funct_1(A_106) | ~v1_relat_1(A_106))), inference(cnfTransformation, [status(thm)], [f_79])).
% 8.61/2.96  tff(c_66, plain, (![A_34]: (v1_funct_2(A_34, k1_relat_1(A_34), k2_relat_1(A_34)) | ~v1_funct_1(A_34) | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_139])).
% 8.61/2.96  tff(c_3867, plain, (![A_1235]: (v1_funct_2(k2_funct_1(A_1235), k2_relat_1(A_1235), k2_relat_1(k2_funct_1(A_1235))) | ~v1_funct_1(k2_funct_1(A_1235)) | ~v1_relat_1(k2_funct_1(A_1235)) | ~v2_funct_1(A_1235) | ~v1_funct_1(A_1235) | ~v1_relat_1(A_1235))), inference(superposition, [status(thm), theory('equality')], [c_435, c_66])).
% 8.61/2.96  tff(c_3882, plain, (v1_funct_2(k2_funct_1('#skF_6'), '#skF_5', k2_relat_1(k2_funct_1('#skF_6'))) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')) | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_507, c_3867])).
% 8.61/2.96  tff(c_3898, plain, (v1_funct_2(k2_funct_1('#skF_6'), '#skF_5', k2_relat_1(k2_funct_1('#skF_6'))) | ~v1_relat_1(k2_funct_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_260, c_80, c_74, c_195, c_3882])).
% 8.61/2.96  tff(c_3899, plain, (~v1_relat_1(k2_funct_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_3898])).
% 8.61/2.96  tff(c_3902, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_22, c_3899])).
% 8.61/2.96  tff(c_3906, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_260, c_80, c_3902])).
% 8.61/2.96  tff(c_3908, plain, (v1_relat_1(k2_funct_1('#skF_6'))), inference(splitRight, [status(thm)], [c_3898])).
% 8.61/2.96  tff(c_519, plain, (![A_119]: (m1_subset_1(A_119, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_119), k2_relat_1(A_119)))) | ~v1_funct_1(A_119) | ~v1_relat_1(A_119))), inference(cnfTransformation, [status(thm)], [f_139])).
% 8.61/2.96  tff(c_5560, plain, (![A_1272]: (m1_subset_1(k2_funct_1(A_1272), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_1272), k2_relat_1(k2_funct_1(A_1272))))) | ~v1_funct_1(k2_funct_1(A_1272)) | ~v1_relat_1(k2_funct_1(A_1272)) | ~v2_funct_1(A_1272) | ~v1_funct_1(A_1272) | ~v1_relat_1(A_1272))), inference(superposition, [status(thm), theory('equality')], [c_30, c_519])).
% 8.61/2.96  tff(c_5601, plain, (m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', k2_relat_1(k2_funct_1('#skF_6'))))) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')) | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_507, c_5560])).
% 8.61/2.96  tff(c_5628, plain, (m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', k2_relat_1(k2_funct_1('#skF_6')))))), inference(demodulation, [status(thm), theory('equality')], [c_260, c_80, c_74, c_3908, c_195, c_5601])).
% 8.61/2.96  tff(c_5651, plain, (m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_relat_1('#skF_6')))) | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_28, c_5628])).
% 8.61/2.96  tff(c_5666, plain, (m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_260, c_80, c_74, c_1391, c_5651])).
% 8.61/2.96  tff(c_5668, plain, $false, inference(negUnitSimplification, [status(thm)], [c_222, c_5666])).
% 8.61/2.96  tff(c_5669, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_270])).
% 8.61/2.96  tff(c_16, plain, (![A_11]: (k1_relat_1(A_11)!=k1_xboole_0 | k1_xboole_0=A_11 | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_56])).
% 8.61/2.96  tff(c_269, plain, (k1_relat_1('#skF_6')!=k1_xboole_0 | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_260, c_16])).
% 8.61/2.96  tff(c_271, plain, (k1_relat_1('#skF_6')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_269])).
% 8.61/2.96  tff(c_5671, plain, (k1_relat_1('#skF_6')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_5669, c_271])).
% 8.61/2.96  tff(c_52, plain, (![A_31, B_32]: (v1_funct_2('#skF_3'(A_31, B_32), A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_129])).
% 8.61/2.96  tff(c_10, plain, (![A_7]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 8.61/2.96  tff(c_5679, plain, (![A_7]: (m1_subset_1('#skF_6', k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_5669, c_10])).
% 8.61/2.96  tff(c_5997, plain, (![A_1318, B_1319, C_1320]: (k1_relset_1(A_1318, B_1319, C_1320)=k1_relat_1(C_1320) | ~m1_subset_1(C_1320, k1_zfmisc_1(k2_zfmisc_1(A_1318, B_1319))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 8.61/2.96  tff(c_6006, plain, (![A_1318, B_1319]: (k1_relset_1(A_1318, B_1319, '#skF_6')=k1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_5679, c_5997])).
% 8.61/2.96  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.61/2.96  tff(c_5683, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_5669, c_6])).
% 8.61/2.96  tff(c_62, plain, (![A_31, B_32]: (m1_subset_1('#skF_3'(A_31, B_32), k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))))), inference(cnfTransformation, [status(thm)], [f_129])).
% 8.61/2.96  tff(c_5754, plain, (![C_1281, A_1282, B_1283]: (v1_xboole_0(C_1281) | ~m1_subset_1(C_1281, k1_zfmisc_1(k2_zfmisc_1(A_1282, B_1283))) | ~v1_xboole_0(A_1282))), inference(cnfTransformation, [status(thm)], [f_90])).
% 8.61/2.96  tff(c_5765, plain, (![A_1284, B_1285]: (v1_xboole_0('#skF_3'(A_1284, B_1285)) | ~v1_xboole_0(A_1284))), inference(resolution, [status(thm)], [c_62, c_5754])).
% 8.61/2.96  tff(c_103, plain, (![A_48]: (r2_hidden('#skF_2'(A_48), A_48) | k1_xboole_0=A_48)), inference(cnfTransformation, [status(thm)], [f_40])).
% 8.61/2.96  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.61/2.96  tff(c_107, plain, (![A_48]: (~v1_xboole_0(A_48) | k1_xboole_0=A_48)), inference(resolution, [status(thm)], [c_103, c_2])).
% 8.61/2.96  tff(c_5677, plain, (![A_48]: (~v1_xboole_0(A_48) | A_48='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_5669, c_107])).
% 8.61/2.96  tff(c_5770, plain, (![A_1286, B_1287]: ('#skF_3'(A_1286, B_1287)='#skF_6' | ~v1_xboole_0(A_1286))), inference(resolution, [status(thm)], [c_5765, c_5677])).
% 8.61/2.96  tff(c_5776, plain, (![B_1287]: ('#skF_3'('#skF_6', B_1287)='#skF_6')), inference(resolution, [status(thm)], [c_5683, c_5770])).
% 8.61/2.96  tff(c_48, plain, (![B_29, C_30]: (k1_relset_1(k1_xboole_0, B_29, C_30)=k1_xboole_0 | ~v1_funct_2(C_30, k1_xboole_0, B_29) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_29))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 8.61/2.96  tff(c_6456, plain, (![B_1349, C_1350]: (k1_relset_1('#skF_6', B_1349, C_1350)='#skF_6' | ~v1_funct_2(C_1350, '#skF_6', B_1349) | ~m1_subset_1(C_1350, k1_zfmisc_1(k2_zfmisc_1('#skF_6', B_1349))))), inference(demodulation, [status(thm), theory('equality')], [c_5669, c_5669, c_5669, c_5669, c_48])).
% 8.61/2.96  tff(c_6460, plain, (![B_32]: (k1_relset_1('#skF_6', B_32, '#skF_3'('#skF_6', B_32))='#skF_6' | ~v1_funct_2('#skF_3'('#skF_6', B_32), '#skF_6', B_32))), inference(resolution, [status(thm)], [c_62, c_6456])).
% 8.61/2.96  tff(c_6467, plain, (k1_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_6006, c_5776, c_6460])).
% 8.61/2.96  tff(c_6469, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5671, c_6467])).
% 8.61/2.96  tff(c_6470, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_269])).
% 8.61/2.96  tff(c_6479, plain, (![A_7]: (m1_subset_1('#skF_6', k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_6470, c_10])).
% 8.61/2.96  tff(c_6471, plain, (k1_relat_1('#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_269])).
% 8.61/2.96  tff(c_6490, plain, (k1_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_6470, c_6471])).
% 8.61/2.96  tff(c_6773, plain, (![A_1391, B_1392, C_1393]: (k1_relset_1(A_1391, B_1392, C_1393)=k1_relat_1(C_1393) | ~m1_subset_1(C_1393, k1_zfmisc_1(k2_zfmisc_1(A_1391, B_1392))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 8.61/2.96  tff(c_6780, plain, (![A_1391, B_1392]: (k1_relset_1(A_1391, B_1392, '#skF_6')=k1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_6479, c_6773])).
% 8.61/2.96  tff(c_6783, plain, (![A_1391, B_1392]: (k1_relset_1(A_1391, B_1392, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_6490, c_6780])).
% 8.61/2.96  tff(c_50, plain, (![B_29, A_28, C_30]: (k1_xboole_0=B_29 | k1_relset_1(A_28, B_29, C_30)=A_28 | ~v1_funct_2(C_30, A_28, B_29) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 8.61/2.96  tff(c_7684, plain, (![B_1443, A_1444, C_1445]: (B_1443='#skF_6' | k1_relset_1(A_1444, B_1443, C_1445)=A_1444 | ~v1_funct_2(C_1445, A_1444, B_1443) | ~m1_subset_1(C_1445, k1_zfmisc_1(k2_zfmisc_1(A_1444, B_1443))))), inference(demodulation, [status(thm), theory('equality')], [c_6470, c_50])).
% 8.61/2.96  tff(c_7694, plain, (![B_1443, A_1444]: (B_1443='#skF_6' | k1_relset_1(A_1444, B_1443, '#skF_6')=A_1444 | ~v1_funct_2('#skF_6', A_1444, B_1443))), inference(resolution, [status(thm)], [c_6479, c_7684])).
% 8.61/2.96  tff(c_7770, plain, (![B_1448, A_1449]: (B_1448='#skF_6' | A_1449='#skF_6' | ~v1_funct_2('#skF_6', A_1449, B_1448))), inference(demodulation, [status(thm), theory('equality')], [c_6783, c_7694])).
% 8.61/2.96  tff(c_7799, plain, ('#skF_5'='#skF_6' | '#skF_6'='#skF_4'), inference(resolution, [status(thm)], [c_78, c_7770])).
% 8.61/2.96  tff(c_7800, plain, ('#skF_6'='#skF_4'), inference(splitLeft, [status(thm)], [c_7799])).
% 8.61/2.96  tff(c_7840, plain, (![A_7]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_7800, c_6479])).
% 8.61/2.96  tff(c_7842, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_7800, c_7800, c_6490])).
% 8.61/2.96  tff(c_7845, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7800, c_260])).
% 8.61/2.96  tff(c_7850, plain, (v1_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7800, c_80])).
% 8.61/2.96  tff(c_7849, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7800, c_74])).
% 8.61/2.96  tff(c_7847, plain, (v1_funct_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_7800, c_195])).
% 8.61/2.96  tff(c_6808, plain, (![A_1398, B_1399, C_1400]: (k2_relset_1(A_1398, B_1399, C_1400)=k2_relat_1(C_1400) | ~m1_subset_1(C_1400, k1_zfmisc_1(k2_zfmisc_1(A_1398, B_1399))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 8.61/2.96  tff(c_6818, plain, (![A_1401, B_1402]: (k2_relset_1(A_1401, B_1402, '#skF_6')=k2_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_6479, c_6808])).
% 8.61/2.96  tff(c_6822, plain, (k2_relat_1('#skF_6')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_6818, c_72])).
% 8.61/2.96  tff(c_7820, plain, (k2_relat_1('#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_7800, c_6822])).
% 8.61/2.96  tff(c_6720, plain, (![A_1381]: (k1_relat_1(k2_funct_1(A_1381))=k2_relat_1(A_1381) | ~v2_funct_1(A_1381) | ~v1_funct_1(A_1381) | ~v1_relat_1(A_1381))), inference(cnfTransformation, [status(thm)], [f_79])).
% 8.61/2.96  tff(c_8967, plain, (![A_2303]: (v1_funct_2(k2_funct_1(A_2303), k2_relat_1(A_2303), k2_relat_1(k2_funct_1(A_2303))) | ~v1_funct_1(k2_funct_1(A_2303)) | ~v1_relat_1(k2_funct_1(A_2303)) | ~v2_funct_1(A_2303) | ~v1_funct_1(A_2303) | ~v1_relat_1(A_2303))), inference(superposition, [status(thm), theory('equality')], [c_6720, c_66])).
% 8.61/2.96  tff(c_8973, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_5', k2_relat_1(k2_funct_1('#skF_4'))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_7820, c_8967])).
% 8.61/2.96  tff(c_8986, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_5', k2_relat_1(k2_funct_1('#skF_4'))) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_7845, c_7850, c_7849, c_7847, c_8973])).
% 8.61/2.96  tff(c_9146, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_8986])).
% 8.61/2.96  tff(c_9149, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_22, c_9146])).
% 8.61/2.96  tff(c_9153, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7845, c_7850, c_9149])).
% 8.61/2.96  tff(c_9155, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_8986])).
% 8.61/2.96  tff(c_6475, plain, (![A_11]: (k2_relat_1(A_11)!='#skF_6' | A_11='#skF_6' | ~v1_relat_1(A_11))), inference(demodulation, [status(thm), theory('equality')], [c_6470, c_6470, c_14])).
% 8.61/2.96  tff(c_7830, plain, (![A_11]: (k2_relat_1(A_11)!='#skF_4' | A_11='#skF_4' | ~v1_relat_1(A_11))), inference(demodulation, [status(thm), theory('equality')], [c_7800, c_7800, c_6475])).
% 8.61/2.96  tff(c_9163, plain, (k2_relat_1(k2_funct_1('#skF_4'))!='#skF_4' | k2_funct_1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_9155, c_7830])).
% 8.61/2.96  tff(c_9202, plain, (k2_relat_1(k2_funct_1('#skF_4'))!='#skF_4'), inference(splitLeft, [status(thm)], [c_9163])).
% 8.61/2.96  tff(c_9205, plain, (k1_relat_1('#skF_4')!='#skF_4' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_28, c_9202])).
% 8.61/2.96  tff(c_9208, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7845, c_7850, c_7849, c_7842, c_9205])).
% 8.61/2.96  tff(c_9209, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_9163])).
% 8.61/2.96  tff(c_6474, plain, (![A_11]: (k1_relat_1(A_11)!='#skF_6' | A_11='#skF_6' | ~v1_relat_1(A_11))), inference(demodulation, [status(thm), theory('equality')], [c_6470, c_6470, c_16])).
% 8.61/2.96  tff(c_7829, plain, (![A_11]: (k1_relat_1(A_11)!='#skF_4' | A_11='#skF_4' | ~v1_relat_1(A_11))), inference(demodulation, [status(thm), theory('equality')], [c_7800, c_7800, c_6474])).
% 8.61/2.96  tff(c_9162, plain, (k1_relat_1(k2_funct_1('#skF_4'))!='#skF_4' | k2_funct_1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_9155, c_7829])).
% 8.61/2.96  tff(c_9169, plain, (k1_relat_1(k2_funct_1('#skF_4'))!='#skF_4'), inference(splitLeft, [status(thm)], [c_9162])).
% 8.61/2.96  tff(c_9212, plain, (k1_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_9209, c_9169])).
% 8.61/2.96  tff(c_9221, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7842, c_9212])).
% 8.61/2.96  tff(c_9222, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_9162])).
% 8.61/2.96  tff(c_7846, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_7800, c_222])).
% 8.61/2.96  tff(c_9227, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_9222, c_7846])).
% 8.61/2.96  tff(c_9233, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7840, c_9227])).
% 8.61/2.96  tff(c_9234, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_7799])).
% 8.61/2.96  tff(c_9240, plain, (k2_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_9234, c_6822])).
% 8.61/2.96  tff(c_223, plain, (![A_71]: (k1_relat_1(A_71)!=k1_xboole_0 | k1_xboole_0=A_71 | ~v1_relat_1(A_71))), inference(cnfTransformation, [status(thm)], [f_56])).
% 8.61/2.96  tff(c_236, plain, (![A_12]: (k1_relat_1(k2_funct_1(A_12))!=k1_xboole_0 | k2_funct_1(A_12)=k1_xboole_0 | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(resolution, [status(thm)], [c_22, c_223])).
% 8.61/2.96  tff(c_9692, plain, (![A_3083]: (k1_relat_1(k2_funct_1(A_3083))!='#skF_6' | k2_funct_1(A_3083)='#skF_6' | ~v1_funct_1(A_3083) | ~v1_relat_1(A_3083))), inference(demodulation, [status(thm), theory('equality')], [c_6470, c_6470, c_236])).
% 8.61/2.96  tff(c_12499, plain, (![A_3151]: (k2_relat_1(A_3151)!='#skF_6' | k2_funct_1(A_3151)='#skF_6' | ~v1_funct_1(A_3151) | ~v1_relat_1(A_3151) | ~v2_funct_1(A_3151) | ~v1_funct_1(A_3151) | ~v1_relat_1(A_3151))), inference(superposition, [status(thm), theory('equality')], [c_30, c_9692])).
% 8.61/2.96  tff(c_12502, plain, (k2_relat_1('#skF_6')!='#skF_6' | k2_funct_1('#skF_6')='#skF_6' | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_74, c_12499])).
% 8.61/2.96  tff(c_12505, plain, (k2_funct_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_260, c_80, c_9240, c_12502])).
% 8.61/2.96  tff(c_9241, plain, (~m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_9234, c_222])).
% 8.61/2.96  tff(c_12506, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_12505, c_9241])).
% 8.61/2.96  tff(c_12510, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6479, c_12506])).
% 8.61/2.96  tff(c_12511, plain, (~v1_funct_2(k2_funct_1('#skF_6'), '#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_194])).
% 8.61/2.96  tff(c_12512, plain, (m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4')))), inference(splitRight, [status(thm)], [c_194])).
% 8.61/2.96  tff(c_13291, plain, (![A_3224, B_3225, C_3226]: (k1_relset_1(A_3224, B_3225, C_3226)=k1_relat_1(C_3226) | ~m1_subset_1(C_3226, k1_zfmisc_1(k2_zfmisc_1(A_3224, B_3225))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 8.61/2.96  tff(c_13306, plain, (k1_relset_1('#skF_5', '#skF_4', k2_funct_1('#skF_6'))=k1_relat_1(k2_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_12512, c_13291])).
% 8.61/2.96  tff(c_14935, plain, (![B_3306, C_3307, A_3308]: (k1_xboole_0=B_3306 | v1_funct_2(C_3307, A_3308, B_3306) | k1_relset_1(A_3308, B_3306, C_3307)!=A_3308 | ~m1_subset_1(C_3307, k1_zfmisc_1(k2_zfmisc_1(A_3308, B_3306))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 8.61/2.96  tff(c_14947, plain, (k1_xboole_0='#skF_4' | v1_funct_2(k2_funct_1('#skF_6'), '#skF_5', '#skF_4') | k1_relset_1('#skF_5', '#skF_4', k2_funct_1('#skF_6'))!='#skF_5'), inference(resolution, [status(thm)], [c_12512, c_14935])).
% 8.61/2.96  tff(c_14963, plain, (k1_xboole_0='#skF_4' | v1_funct_2(k2_funct_1('#skF_6'), '#skF_5', '#skF_4') | k1_relat_1(k2_funct_1('#skF_6'))!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_13306, c_14947])).
% 8.61/2.96  tff(c_14964, plain, (k1_xboole_0='#skF_4' | k1_relat_1(k2_funct_1('#skF_6'))!='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_12511, c_14963])).
% 8.61/2.96  tff(c_14970, plain, (k1_relat_1(k2_funct_1('#skF_6'))!='#skF_5'), inference(splitLeft, [status(thm)], [c_14964])).
% 8.61/2.96  tff(c_14973, plain, (k2_relat_1('#skF_6')!='#skF_5' | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_30, c_14970])).
% 8.61/2.96  tff(c_14976, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12544, c_80, c_74, c_13977, c_14973])).
% 8.61/2.96  tff(c_14977, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_14964])).
% 8.61/2.96  tff(c_15028, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_14977, c_6])).
% 8.61/2.96  tff(c_15030, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12605, c_15028])).
% 8.61/2.96  tff(c_15032, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_12602])).
% 8.61/2.96  tff(c_15040, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_15032, c_107])).
% 8.61/2.96  tff(c_15031, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_12602])).
% 8.61/2.96  tff(c_15036, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_15031, c_107])).
% 8.61/2.96  tff(c_15066, plain, ('#skF_6'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_15040, c_15036])).
% 8.61/2.96  tff(c_12553, plain, (k1_relat_1('#skF_6')!=k1_xboole_0 | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_12544, c_16])).
% 8.61/2.96  tff(c_12563, plain, (k1_relat_1('#skF_6')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_12553])).
% 8.61/2.96  tff(c_15048, plain, (k1_relat_1('#skF_6')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_15036, c_12563])).
% 8.61/2.96  tff(c_15102, plain, (k1_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_15066, c_15066, c_15048])).
% 8.61/2.96  tff(c_15153, plain, (![A_3315, B_3316]: (v1_xboole_0('#skF_3'(A_3315, B_3316)) | ~v1_xboole_0(A_3315))), inference(resolution, [status(thm)], [c_62, c_12586])).
% 8.61/2.96  tff(c_15052, plain, (![A_48]: (~v1_xboole_0(A_48) | A_48='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_15036, c_107])).
% 8.61/2.96  tff(c_15104, plain, (![A_48]: (~v1_xboole_0(A_48) | A_48='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_15066, c_15052])).
% 8.61/2.96  tff(c_15184, plain, (![A_3320, B_3321]: ('#skF_3'(A_3320, B_3321)='#skF_4' | ~v1_xboole_0(A_3320))), inference(resolution, [status(thm)], [c_15153, c_15104])).
% 8.61/2.96  tff(c_15191, plain, (![B_3322]: ('#skF_3'('#skF_4', B_3322)='#skF_4')), inference(resolution, [status(thm)], [c_15032, c_15184])).
% 8.61/2.96  tff(c_15202, plain, (![B_3322]: (v1_funct_2('#skF_4', '#skF_4', B_3322))), inference(superposition, [status(thm), theory('equality')], [c_15191, c_52])).
% 8.61/2.96  tff(c_15054, plain, (![A_7]: (m1_subset_1('#skF_6', k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_15036, c_10])).
% 8.61/2.96  tff(c_15123, plain, (![A_7]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_15066, c_15054])).
% 8.61/2.96  tff(c_15242, plain, (![A_3328, B_3329, C_3330]: (k1_relset_1(A_3328, B_3329, C_3330)=k1_relat_1(C_3330) | ~m1_subset_1(C_3330, k1_zfmisc_1(k2_zfmisc_1(A_3328, B_3329))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 8.61/2.96  tff(c_15250, plain, (![A_3328, B_3329]: (k1_relset_1(A_3328, B_3329, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_15123, c_15242])).
% 8.61/2.96  tff(c_15707, plain, (![B_3365, C_3366]: (k1_relset_1('#skF_4', B_3365, C_3366)='#skF_4' | ~v1_funct_2(C_3366, '#skF_4', B_3365) | ~m1_subset_1(C_3366, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_3365))))), inference(demodulation, [status(thm), theory('equality')], [c_15040, c_15040, c_15040, c_15040, c_48])).
% 8.61/2.96  tff(c_15711, plain, (![B_3365]: (k1_relset_1('#skF_4', B_3365, '#skF_4')='#skF_4' | ~v1_funct_2('#skF_4', '#skF_4', B_3365))), inference(resolution, [status(thm)], [c_15123, c_15707])).
% 8.61/2.96  tff(c_15718, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_15202, c_15250, c_15711])).
% 8.61/2.96  tff(c_15720, plain, $false, inference(negUnitSimplification, [status(thm)], [c_15102, c_15718])).
% 8.61/2.96  tff(c_15721, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_12553])).
% 8.61/2.96  tff(c_15732, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_15721, c_6])).
% 8.61/2.96  tff(c_16149, plain, (![C_3412, A_3413, B_3414]: (v1_xboole_0(C_3412) | ~m1_subset_1(C_3412, k1_zfmisc_1(k2_zfmisc_1(A_3413, B_3414))) | ~v1_xboole_0(A_3413))), inference(cnfTransformation, [status(thm)], [f_90])).
% 8.61/2.96  tff(c_16160, plain, (![A_3415, B_3416]: (v1_xboole_0('#skF_3'(A_3415, B_3416)) | ~v1_xboole_0(A_3415))), inference(resolution, [status(thm)], [c_62, c_16149])).
% 8.61/2.96  tff(c_15726, plain, (![A_48]: (~v1_xboole_0(A_48) | A_48='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_15721, c_107])).
% 8.61/2.96  tff(c_16165, plain, (![A_3417, B_3418]: ('#skF_3'(A_3417, B_3418)='#skF_6' | ~v1_xboole_0(A_3417))), inference(resolution, [status(thm)], [c_16160, c_15726])).
% 8.61/2.96  tff(c_16172, plain, (![B_3419]: ('#skF_3'('#skF_6', B_3419)='#skF_6')), inference(resolution, [status(thm)], [c_15732, c_16165])).
% 8.61/2.96  tff(c_16186, plain, (![B_3419]: (v1_funct_2('#skF_6', '#skF_6', B_3419))), inference(superposition, [status(thm), theory('equality')], [c_16172, c_52])).
% 8.61/2.96  tff(c_15722, plain, (k1_relat_1('#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_12553])).
% 8.61/2.96  tff(c_15739, plain, (k1_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_15721, c_15722])).
% 8.61/2.96  tff(c_16031, plain, (![A_3406]: (k2_relat_1(k2_funct_1(A_3406))=k1_relat_1(A_3406) | ~v2_funct_1(A_3406) | ~v1_funct_1(A_3406) | ~v1_relat_1(A_3406))), inference(cnfTransformation, [status(thm)], [f_79])).
% 8.61/2.96  tff(c_12543, plain, (v1_relat_1(k2_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_12512, c_12532])).
% 8.61/2.96  tff(c_12562, plain, (k2_relat_1(k2_funct_1('#skF_6'))!=k1_xboole_0 | k2_funct_1('#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_12543, c_14])).
% 8.61/2.96  tff(c_15796, plain, (k2_relat_1(k2_funct_1('#skF_6'))!='#skF_6' | k2_funct_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_15721, c_15721, c_12562])).
% 8.61/2.96  tff(c_15797, plain, (k2_relat_1(k2_funct_1('#skF_6'))!='#skF_6'), inference(splitLeft, [status(thm)], [c_15796])).
% 8.61/2.96  tff(c_16040, plain, (k1_relat_1('#skF_6')!='#skF_6' | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_16031, c_15797])).
% 8.61/2.96  tff(c_16047, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12544, c_80, c_74, c_15739, c_16040])).
% 8.61/2.96  tff(c_16048, plain, (k2_funct_1('#skF_6')='#skF_6'), inference(splitRight, [status(thm)], [c_15796])).
% 8.61/2.96  tff(c_12561, plain, (k1_relat_1(k2_funct_1('#skF_6'))!=k1_xboole_0 | k2_funct_1('#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_12543, c_16])).
% 8.61/2.96  tff(c_15794, plain, (k1_relat_1(k2_funct_1('#skF_6'))!='#skF_6' | k2_funct_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_15721, c_15721, c_12561])).
% 8.61/2.96  tff(c_15795, plain, (k1_relat_1(k2_funct_1('#skF_6'))!='#skF_6'), inference(splitLeft, [status(thm)], [c_15794])).
% 8.61/2.96  tff(c_16077, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15739, c_16048, c_15795])).
% 8.61/2.96  tff(c_16078, plain, (k2_funct_1('#skF_6')='#skF_6'), inference(splitRight, [status(thm)], [c_15794])).
% 8.61/2.96  tff(c_16280, plain, (![A_3430]: (k1_relat_1(k2_funct_1(A_3430))=k2_relat_1(A_3430) | ~v2_funct_1(A_3430) | ~v1_funct_1(A_3430) | ~v1_relat_1(A_3430))), inference(cnfTransformation, [status(thm)], [f_79])).
% 8.61/2.96  tff(c_16292, plain, (k2_relat_1('#skF_6')=k1_relat_1('#skF_6') | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_16078, c_16280])).
% 8.61/2.96  tff(c_16296, plain, (k2_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_12544, c_80, c_74, c_15739, c_16292])).
% 8.61/2.96  tff(c_15728, plain, (![A_7]: (m1_subset_1('#skF_6', k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_15721, c_10])).
% 8.61/2.96  tff(c_16382, plain, (![A_3443, B_3444, C_3445]: (k2_relset_1(A_3443, B_3444, C_3445)=k2_relat_1(C_3445) | ~m1_subset_1(C_3445, k1_zfmisc_1(k2_zfmisc_1(A_3443, B_3444))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 8.61/2.96  tff(c_16389, plain, (![A_3443, B_3444]: (k2_relset_1(A_3443, B_3444, '#skF_6')=k2_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_15728, c_16382])).
% 8.61/2.96  tff(c_16392, plain, (![A_3443, B_3444]: (k2_relset_1(A_3443, B_3444, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_16296, c_16389])).
% 8.61/2.96  tff(c_16393, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_16392, c_72])).
% 8.61/2.96  tff(c_16082, plain, (~v1_funct_2('#skF_6', '#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_16078, c_12511])).
% 8.61/2.96  tff(c_16401, plain, (~v1_funct_2('#skF_6', '#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_16393, c_16082])).
% 8.61/2.96  tff(c_16405, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16186, c_16401])).
% 8.61/2.96  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.61/2.96  
% 8.61/2.96  Inference rules
% 8.61/2.96  ----------------------
% 8.61/2.96  #Ref     : 0
% 8.61/2.96  #Sup     : 3738
% 8.61/2.96  #Fact    : 0
% 8.61/2.96  #Define  : 0
% 8.61/2.96  #Split   : 36
% 8.61/2.96  #Chain   : 0
% 8.61/2.96  #Close   : 0
% 8.61/2.96  
% 8.61/2.96  Ordering : KBO
% 8.61/2.96  
% 8.61/2.96  Simplification rules
% 8.61/2.96  ----------------------
% 8.61/2.96  #Subsume      : 1052
% 8.61/2.96  #Demod        : 3719
% 8.61/2.96  #Tautology    : 1837
% 8.61/2.96  #SimpNegUnit  : 21
% 8.61/2.96  #BackRed      : 252
% 8.61/2.96  
% 8.61/2.96  #Partial instantiations: 216
% 8.61/2.96  #Strategies tried      : 1
% 8.61/2.96  
% 8.61/2.96  Timing (in seconds)
% 8.61/2.96  ----------------------
% 8.61/2.96  Preprocessing        : 0.35
% 8.61/2.96  Parsing              : 0.19
% 8.61/2.96  CNF conversion       : 0.02
% 8.61/2.96  Main loop            : 1.78
% 8.61/2.96  Inferencing          : 0.64
% 8.61/2.96  Reduction            : 0.64
% 8.61/2.96  Demodulation         : 0.47
% 8.61/2.96  BG Simplification    : 0.06
% 8.61/2.96  Subsumption          : 0.32
% 8.61/2.96  Abstraction          : 0.09
% 8.61/2.96  MUC search           : 0.00
% 8.61/2.96  Cooper               : 0.00
% 8.61/2.96  Total                : 2.21
% 8.61/2.96  Index Insertion      : 0.00
% 8.61/2.96  Index Deletion       : 0.00
% 8.61/2.96  Index Matching       : 0.00
% 8.61/2.96  BG Taut test         : 0.00
%------------------------------------------------------------------------------
