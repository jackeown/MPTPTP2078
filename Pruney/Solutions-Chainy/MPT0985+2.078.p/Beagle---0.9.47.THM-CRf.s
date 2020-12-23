%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:38 EST 2020

% Result     : Theorem 9.16s
% Output     : CNFRefutation 9.16s
% Verified   : 
% Statistics : Number of formulae       :  190 ( 934 expanded)
%              Number of leaves         :   44 ( 313 expanded)
%              Depth                    :   17
%              Number of atoms          :  307 (2375 expanded)
%              Number of equality atoms :   96 ( 451 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_154,negated_conjecture,(
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

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_95,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_66,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_103,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_76,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_137,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_121,axiom,(
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

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_42,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_125,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_127,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_78,axiom,(
    ! [A] : k2_funct_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_76,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_268,plain,(
    ! [C_66,A_67,B_68] :
      ( v1_relat_1(C_66)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_289,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_268])).

tff(c_80,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_74,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_497,plain,(
    ! [C_112,B_113,A_114] :
      ( v1_xboole_0(C_112)
      | ~ m1_subset_1(C_112,k1_zfmisc_1(k2_zfmisc_1(B_113,A_114)))
      | ~ v1_xboole_0(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_520,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_497])).

tff(c_525,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_520])).

tff(c_24,plain,(
    ! [A_13] :
      ( v1_funct_1(k2_funct_1(A_13))
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_70,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_158,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_161,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_158])).

tff(c_164,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_161])).

tff(c_203,plain,(
    ! [C_58,A_59,B_60] :
      ( v1_relat_1(C_58)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_213,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_203])).

tff(c_227,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_164,c_213])).

tff(c_228,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_365,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_228])).

tff(c_72,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_740,plain,(
    ! [A_123,B_124,C_125] :
      ( k2_relset_1(A_123,B_124,C_125) = k2_relat_1(C_125)
      | ~ m1_subset_1(C_125,k1_zfmisc_1(k2_zfmisc_1(A_123,B_124))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_750,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_740])).

tff(c_764,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_750])).

tff(c_30,plain,(
    ! [A_14] :
      ( k1_relat_1(k2_funct_1(A_14)) = k2_relat_1(A_14)
      | ~ v2_funct_1(A_14)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_26,plain,(
    ! [A_13] :
      ( v1_relat_1(k2_funct_1(A_13))
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_229,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_534,plain,(
    ! [A_116] :
      ( k1_relat_1(k2_funct_1(A_116)) = k2_relat_1(A_116)
      | ~ v2_funct_1(A_116)
      | ~ v1_funct_1(A_116)
      | ~ v1_relat_1(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_66,plain,(
    ! [A_37] :
      ( v1_funct_2(A_37,k1_relat_1(A_37),k2_relat_1(A_37))
      | ~ v1_funct_1(A_37)
      | ~ v1_relat_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_10061,plain,(
    ! [A_410] :
      ( v1_funct_2(k2_funct_1(A_410),k2_relat_1(A_410),k2_relat_1(k2_funct_1(A_410)))
      | ~ v1_funct_1(k2_funct_1(A_410))
      | ~ v1_relat_1(k2_funct_1(A_410))
      | ~ v2_funct_1(A_410)
      | ~ v1_funct_1(A_410)
      | ~ v1_relat_1(A_410) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_534,c_66])).

tff(c_10082,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_764,c_10061])).

tff(c_10114,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_289,c_80,c_74,c_229,c_10082])).

tff(c_10123,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_10114])).

tff(c_10126,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_10123])).

tff(c_10130,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_289,c_80,c_10126])).

tff(c_10132,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_10114])).

tff(c_78,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_963,plain,(
    ! [A_140,B_141,C_142] :
      ( k1_relset_1(A_140,B_141,C_142) = k1_relat_1(C_142)
      | ~ m1_subset_1(C_142,k1_zfmisc_1(k2_zfmisc_1(A_140,B_141))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_994,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_963])).

tff(c_1368,plain,(
    ! [B_166,A_167,C_168] :
      ( k1_xboole_0 = B_166
      | k1_relset_1(A_167,B_166,C_168) = A_167
      | ~ v1_funct_2(C_168,A_167,B_166)
      | ~ m1_subset_1(C_168,k1_zfmisc_1(k2_zfmisc_1(A_167,B_166))) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_1384,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_1368])).

tff(c_1404,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_994,c_1384])).

tff(c_1408,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1404])).

tff(c_28,plain,(
    ! [A_14] :
      ( k2_relat_1(k2_funct_1(A_14)) = k1_relat_1(A_14)
      | ~ v2_funct_1(A_14)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_817,plain,(
    ! [A_133] :
      ( m1_subset_1(A_133,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_133),k2_relat_1(A_133))))
      | ~ v1_funct_1(A_133)
      | ~ v1_relat_1(A_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_12854,plain,(
    ! [A_448] :
      ( m1_subset_1(k2_funct_1(A_448),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_448)),k1_relat_1(A_448))))
      | ~ v1_funct_1(k2_funct_1(A_448))
      | ~ v1_relat_1(k2_funct_1(A_448))
      | ~ v2_funct_1(A_448)
      | ~ v1_funct_1(A_448)
      | ~ v1_relat_1(A_448) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_817])).

tff(c_12916,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_1')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1408,c_12854])).

tff(c_12971,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_289,c_80,c_74,c_10132,c_229,c_12916])).

tff(c_13105,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),'#skF_1')))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_12971])).

tff(c_13121,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_289,c_80,c_74,c_764,c_13105])).

tff(c_13123,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_365,c_13121])).

tff(c_13124,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1404])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_13165,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13124,c_2])).

tff(c_13167,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_525,c_13165])).

tff(c_13168,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_520])).

tff(c_133,plain,(
    ! [B_44,A_45] :
      ( ~ v1_xboole_0(B_44)
      | B_44 = A_45
      | ~ v1_xboole_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_136,plain,(
    ! [A_45] :
      ( k1_xboole_0 = A_45
      | ~ v1_xboole_0(A_45) ) ),
    inference(resolution,[status(thm)],[c_2,c_133])).

tff(c_13175,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_13168,c_136])).

tff(c_12,plain,(
    ! [A_5] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_144,plain,(
    ! [A_48,B_49] :
      ( r1_tarski(A_48,B_49)
      | ~ m1_subset_1(A_48,k1_zfmisc_1(B_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_152,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(resolution,[status(thm)],[c_12,c_144])).

tff(c_13201,plain,(
    ! [A_5] : r1_tarski('#skF_3',A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13175,c_152])).

tff(c_60,plain,(
    ! [A_35] : m1_subset_1(k6_partfun1(A_35),k1_zfmisc_1(k2_zfmisc_1(A_35,A_35))) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_13394,plain,(
    ! [A_461] :
      ( v1_xboole_0(k6_partfun1(A_461))
      | ~ v1_xboole_0(A_461) ) ),
    inference(resolution,[status(thm)],[c_60,c_497])).

tff(c_13203,plain,(
    ! [A_45] :
      ( A_45 = '#skF_3'
      | ~ v1_xboole_0(A_45) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13175,c_136])).

tff(c_13450,plain,(
    ! [A_466] :
      ( k6_partfun1(A_466) = '#skF_3'
      | ~ v1_xboole_0(A_466) ) ),
    inference(resolution,[status(thm)],[c_13394,c_13203])).

tff(c_13458,plain,(
    k6_partfun1('#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_13168,c_13450])).

tff(c_62,plain,(
    ! [A_36] : k6_relat_1(A_36) = k6_partfun1(A_36) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_32,plain,(
    ! [A_15] : k2_funct_1(k6_relat_1(A_15)) = k6_relat_1(A_15) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_81,plain,(
    ! [A_15] : k2_funct_1(k6_partfun1(A_15)) = k6_partfun1(A_15) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_62,c_32])).

tff(c_13487,plain,(
    k6_partfun1('#skF_3') = k2_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_13458,c_81])).

tff(c_13500,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13458,c_13487])).

tff(c_10,plain,(
    ! [B_4] : k2_zfmisc_1(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_13205,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_3',B_4) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13175,c_13175,c_10])).

tff(c_13169,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_520])).

tff(c_13182,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_13169,c_136])).

tff(c_13214,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13175,c_13182])).

tff(c_16,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_369,plain,(
    ~ r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_16,c_365])).

tff(c_13218,plain,(
    ~ r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_3','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13214,c_369])).

tff(c_13576,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13201,c_13500,c_13205,c_13218])).

tff(c_13578,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_228])).

tff(c_13730,plain,(
    ! [C_498,B_499,A_500] :
      ( v1_xboole_0(C_498)
      | ~ m1_subset_1(C_498,k1_zfmisc_1(k2_zfmisc_1(B_499,A_500)))
      | ~ v1_xboole_0(A_500) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_13754,plain,
    ( v1_xboole_0(k2_funct_1('#skF_3'))
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_13578,c_13730])).

tff(c_13772,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_13754])).

tff(c_14150,plain,(
    ! [A_530,B_531,C_532] :
      ( k2_relset_1(A_530,B_531,C_532) = k2_relat_1(C_532)
      | ~ m1_subset_1(C_532,k1_zfmisc_1(k2_zfmisc_1(A_530,B_531))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_14163,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_14150])).

tff(c_14178,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_14163])).

tff(c_13577,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_228])).

tff(c_14379,plain,(
    ! [A_541,B_542,C_543] :
      ( k1_relset_1(A_541,B_542,C_543) = k1_relat_1(C_543)
      | ~ m1_subset_1(C_543,k1_zfmisc_1(k2_zfmisc_1(A_541,B_542))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_14411,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_13578,c_14379])).

tff(c_14769,plain,(
    ! [B_577,C_578,A_579] :
      ( k1_xboole_0 = B_577
      | v1_funct_2(C_578,A_579,B_577)
      | k1_relset_1(A_579,B_577,C_578) != A_579
      | ~ m1_subset_1(C_578,k1_zfmisc_1(k2_zfmisc_1(A_579,B_577))) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_14778,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_13578,c_14769])).

tff(c_14804,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14411,c_14778])).

tff(c_14805,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_13577,c_14804])).

tff(c_14814,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_14805])).

tff(c_14817,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_14814])).

tff(c_14820,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_289,c_80,c_74,c_14178,c_14817])).

tff(c_14821,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_14805])).

tff(c_14869,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14821,c_2])).

tff(c_14871,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13772,c_14869])).

tff(c_14873,plain,(
    v1_xboole_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_13754])).

tff(c_14879,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_14873,c_136])).

tff(c_46,plain,(
    ! [A_32] :
      ( v1_funct_2(k1_xboole_0,A_32,k1_xboole_0)
      | k1_xboole_0 = A_32
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_32,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_83,plain,(
    ! [A_32] :
      ( v1_funct_2(k1_xboole_0,A_32,k1_xboole_0)
      | k1_xboole_0 = A_32 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_46])).

tff(c_15435,plain,(
    ! [A_609] :
      ( v1_funct_2('#skF_1',A_609,'#skF_1')
      | A_609 = '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14879,c_14879,c_14879,c_83])).

tff(c_14872,plain,(
    v1_xboole_0(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_13754])).

tff(c_15003,plain,(
    ! [A_588] :
      ( A_588 = '#skF_1'
      | ~ v1_xboole_0(A_588) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14879,c_136])).

tff(c_15013,plain,(
    k2_funct_1('#skF_3') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_14872,c_15003])).

tff(c_15024,plain,(
    ~ v1_funct_2('#skF_1','#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15013,c_13577])).

tff(c_15439,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_15435,c_15024])).

tff(c_13757,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_13730])).

tff(c_13762,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_13757])).

tff(c_15443,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15439,c_13762])).

tff(c_15446,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14873,c_15443])).

tff(c_15447,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_13757])).

tff(c_15672,plain,(
    ! [A_621] :
      ( v1_xboole_0(k6_partfun1(A_621))
      | ~ v1_xboole_0(A_621) ) ),
    inference(resolution,[status(thm)],[c_60,c_13730])).

tff(c_15454,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_15447,c_136])).

tff(c_15448,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_13757])).

tff(c_15462,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_15448,c_136])).

tff(c_15492,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15454,c_15462])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( ~ v1_xboole_0(B_2)
      | B_2 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_15463,plain,(
    ! [A_1] :
      ( A_1 = '#skF_2'
      | ~ v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_15448,c_4])).

tff(c_15543,plain,(
    ! [A_1] :
      ( A_1 = '#skF_3'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15492,c_15463])).

tff(c_15740,plain,(
    ! [A_625] :
      ( k6_partfun1(A_625) = '#skF_3'
      | ~ v1_xboole_0(A_625) ) ),
    inference(resolution,[status(thm)],[c_15672,c_15543])).

tff(c_15748,plain,(
    k6_partfun1('#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_15447,c_15740])).

tff(c_15775,plain,(
    k6_partfun1('#skF_3') = k2_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_15748,c_81])).

tff(c_15788,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15748,c_15775])).

tff(c_15802,plain,
    ( k2_relat_1('#skF_3') = k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_15788,c_28])).

tff(c_15815,plain,(
    k2_relat_1('#skF_3') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_289,c_80,c_74,c_15802])).

tff(c_15484,plain,(
    ! [A_5] : m1_subset_1('#skF_3',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15454,c_12])).

tff(c_15823,plain,(
    ! [A_626,B_627,C_628] :
      ( k2_relset_1(A_626,B_627,C_628) = k2_relat_1(C_628)
      | ~ m1_subset_1(C_628,k1_zfmisc_1(k2_zfmisc_1(A_626,B_627))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_15845,plain,(
    ! [A_626,B_627] : k2_relset_1(A_626,B_627,'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_15484,c_15823])).

tff(c_15956,plain,(
    ! [A_645,B_646] : k2_relset_1(A_645,B_646,'#skF_3') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15815,c_15845])).

tff(c_15501,plain,(
    k2_relset_1('#skF_1','#skF_3','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15492,c_15492,c_72])).

tff(c_15960,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_15956,c_15501])).

tff(c_15893,plain,(
    ! [A_633,B_634,C_635] :
      ( k1_relset_1(A_633,B_634,C_635) = k1_relat_1(C_635)
      | ~ m1_subset_1(C_635,k1_zfmisc_1(k2_zfmisc_1(A_633,B_634))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_15915,plain,(
    ! [A_633,B_634] : k1_relset_1(A_633,B_634,'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_15484,c_15893])).

tff(c_15968,plain,(
    ! [A_633,B_634] : k1_relset_1(A_633,B_634,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15960,c_15915])).

tff(c_50,plain,(
    ! [C_34,B_33] :
      ( v1_funct_2(C_34,k1_xboole_0,B_33)
      | k1_relset_1(k1_xboole_0,B_33,C_34) != k1_xboole_0
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_33))) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_85,plain,(
    ! [C_34,B_33] :
      ( v1_funct_2(C_34,k1_xboole_0,B_33)
      | k1_relset_1(k1_xboole_0,B_33,C_34) != k1_xboole_0
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_50])).

tff(c_16032,plain,(
    ! [C_651,B_652] :
      ( v1_funct_2(C_651,'#skF_3',B_652)
      | k1_relset_1('#skF_3',B_652,C_651) != '#skF_3'
      | ~ m1_subset_1(C_651,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15454,c_15454,c_15454,c_15454,c_85])).

tff(c_16035,plain,(
    ! [B_652] :
      ( v1_funct_2('#skF_3','#skF_3',B_652)
      | k1_relset_1('#skF_3',B_652,'#skF_3') != '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_15484,c_16032])).

tff(c_16041,plain,(
    ! [B_652] : v1_funct_2('#skF_3','#skF_3',B_652) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15968,c_16035])).

tff(c_15498,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15492,c_13577])).

tff(c_15790,plain,(
    ~ v1_funct_2('#skF_3','#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15788,c_15498])).

tff(c_16046,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16041,c_15790])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n008.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 11:39:45 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.16/3.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.16/3.26  
% 9.16/3.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.16/3.26  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 9.16/3.26  
% 9.16/3.26  %Foreground sorts:
% 9.16/3.26  
% 9.16/3.26  
% 9.16/3.26  %Background operators:
% 9.16/3.26  
% 9.16/3.26  
% 9.16/3.26  %Foreground operators:
% 9.16/3.26  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 9.16/3.26  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.16/3.26  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 9.16/3.26  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 9.16/3.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.16/3.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.16/3.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.16/3.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.16/3.26  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.16/3.26  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.16/3.26  tff('#skF_2', type, '#skF_2': $i).
% 9.16/3.26  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 9.16/3.26  tff('#skF_3', type, '#skF_3': $i).
% 9.16/3.26  tff('#skF_1', type, '#skF_1': $i).
% 9.16/3.26  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 9.16/3.26  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 9.16/3.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.16/3.26  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 9.16/3.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.16/3.26  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.16/3.26  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.16/3.26  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 9.16/3.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.16/3.26  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 9.16/3.26  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.16/3.26  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.16/3.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.16/3.26  
% 9.16/3.29  tff(f_154, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 9.16/3.29  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 9.16/3.29  tff(f_95, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 9.16/3.29  tff(f_66, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 9.16/3.29  tff(f_103, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 9.16/3.29  tff(f_76, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 9.16/3.29  tff(f_137, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 9.16/3.29  tff(f_99, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 9.16/3.29  tff(f_121, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 9.16/3.29  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 9.16/3.29  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 9.16/3.29  tff(f_42, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 9.16/3.29  tff(f_46, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 9.16/3.29  tff(f_125, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 9.16/3.29  tff(f_127, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 9.16/3.29  tff(f_78, axiom, (![A]: (k2_funct_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_funct_1)).
% 9.16/3.29  tff(f_40, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 9.16/3.29  tff(c_76, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_154])).
% 9.16/3.29  tff(c_268, plain, (![C_66, A_67, B_68]: (v1_relat_1(C_66) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 9.16/3.29  tff(c_289, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_76, c_268])).
% 9.16/3.29  tff(c_80, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_154])).
% 9.16/3.29  tff(c_74, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_154])).
% 9.16/3.29  tff(c_497, plain, (![C_112, B_113, A_114]: (v1_xboole_0(C_112) | ~m1_subset_1(C_112, k1_zfmisc_1(k2_zfmisc_1(B_113, A_114))) | ~v1_xboole_0(A_114))), inference(cnfTransformation, [status(thm)], [f_95])).
% 9.16/3.29  tff(c_520, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_76, c_497])).
% 9.16/3.29  tff(c_525, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_520])).
% 9.16/3.29  tff(c_24, plain, (![A_13]: (v1_funct_1(k2_funct_1(A_13)) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_66])).
% 9.16/3.29  tff(c_70, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_154])).
% 9.16/3.29  tff(c_158, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_70])).
% 9.16/3.29  tff(c_161, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_24, c_158])).
% 9.16/3.29  tff(c_164, plain, (~v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_161])).
% 9.16/3.29  tff(c_203, plain, (![C_58, A_59, B_60]: (v1_relat_1(C_58) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 9.16/3.29  tff(c_213, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_76, c_203])).
% 9.16/3.29  tff(c_227, plain, $false, inference(negUnitSimplification, [status(thm)], [c_164, c_213])).
% 9.16/3.29  tff(c_228, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_70])).
% 9.16/3.29  tff(c_365, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_228])).
% 9.16/3.29  tff(c_72, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_154])).
% 9.16/3.29  tff(c_740, plain, (![A_123, B_124, C_125]: (k2_relset_1(A_123, B_124, C_125)=k2_relat_1(C_125) | ~m1_subset_1(C_125, k1_zfmisc_1(k2_zfmisc_1(A_123, B_124))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 9.16/3.29  tff(c_750, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_76, c_740])).
% 9.16/3.29  tff(c_764, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_750])).
% 9.16/3.29  tff(c_30, plain, (![A_14]: (k1_relat_1(k2_funct_1(A_14))=k2_relat_1(A_14) | ~v2_funct_1(A_14) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_76])).
% 9.16/3.29  tff(c_26, plain, (![A_13]: (v1_relat_1(k2_funct_1(A_13)) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_66])).
% 9.16/3.29  tff(c_229, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_70])).
% 9.16/3.29  tff(c_534, plain, (![A_116]: (k1_relat_1(k2_funct_1(A_116))=k2_relat_1(A_116) | ~v2_funct_1(A_116) | ~v1_funct_1(A_116) | ~v1_relat_1(A_116))), inference(cnfTransformation, [status(thm)], [f_76])).
% 9.16/3.29  tff(c_66, plain, (![A_37]: (v1_funct_2(A_37, k1_relat_1(A_37), k2_relat_1(A_37)) | ~v1_funct_1(A_37) | ~v1_relat_1(A_37))), inference(cnfTransformation, [status(thm)], [f_137])).
% 9.16/3.29  tff(c_10061, plain, (![A_410]: (v1_funct_2(k2_funct_1(A_410), k2_relat_1(A_410), k2_relat_1(k2_funct_1(A_410))) | ~v1_funct_1(k2_funct_1(A_410)) | ~v1_relat_1(k2_funct_1(A_410)) | ~v2_funct_1(A_410) | ~v1_funct_1(A_410) | ~v1_relat_1(A_410))), inference(superposition, [status(thm), theory('equality')], [c_534, c_66])).
% 9.16/3.29  tff(c_10082, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_764, c_10061])).
% 9.16/3.29  tff(c_10114, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_289, c_80, c_74, c_229, c_10082])).
% 9.16/3.29  tff(c_10123, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_10114])).
% 9.16/3.29  tff(c_10126, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_26, c_10123])).
% 9.16/3.29  tff(c_10130, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_289, c_80, c_10126])).
% 9.16/3.29  tff(c_10132, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_10114])).
% 9.16/3.29  tff(c_78, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_154])).
% 9.16/3.29  tff(c_963, plain, (![A_140, B_141, C_142]: (k1_relset_1(A_140, B_141, C_142)=k1_relat_1(C_142) | ~m1_subset_1(C_142, k1_zfmisc_1(k2_zfmisc_1(A_140, B_141))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 9.16/3.29  tff(c_994, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_76, c_963])).
% 9.16/3.29  tff(c_1368, plain, (![B_166, A_167, C_168]: (k1_xboole_0=B_166 | k1_relset_1(A_167, B_166, C_168)=A_167 | ~v1_funct_2(C_168, A_167, B_166) | ~m1_subset_1(C_168, k1_zfmisc_1(k2_zfmisc_1(A_167, B_166))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 9.16/3.29  tff(c_1384, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_76, c_1368])).
% 9.16/3.29  tff(c_1404, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_994, c_1384])).
% 9.16/3.29  tff(c_1408, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_1404])).
% 9.16/3.29  tff(c_28, plain, (![A_14]: (k2_relat_1(k2_funct_1(A_14))=k1_relat_1(A_14) | ~v2_funct_1(A_14) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_76])).
% 9.16/3.29  tff(c_817, plain, (![A_133]: (m1_subset_1(A_133, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_133), k2_relat_1(A_133)))) | ~v1_funct_1(A_133) | ~v1_relat_1(A_133))), inference(cnfTransformation, [status(thm)], [f_137])).
% 9.16/3.29  tff(c_12854, plain, (![A_448]: (m1_subset_1(k2_funct_1(A_448), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_448)), k1_relat_1(A_448)))) | ~v1_funct_1(k2_funct_1(A_448)) | ~v1_relat_1(k2_funct_1(A_448)) | ~v2_funct_1(A_448) | ~v1_funct_1(A_448) | ~v1_relat_1(A_448))), inference(superposition, [status(thm), theory('equality')], [c_28, c_817])).
% 9.16/3.29  tff(c_12916, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_1'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1408, c_12854])).
% 9.16/3.29  tff(c_12971, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_289, c_80, c_74, c_10132, c_229, c_12916])).
% 9.16/3.29  tff(c_13105, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), '#skF_1'))) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_30, c_12971])).
% 9.16/3.29  tff(c_13121, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_289, c_80, c_74, c_764, c_13105])).
% 9.16/3.29  tff(c_13123, plain, $false, inference(negUnitSimplification, [status(thm)], [c_365, c_13121])).
% 9.16/3.29  tff(c_13124, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_1404])).
% 9.16/3.29  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 9.16/3.29  tff(c_13165, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_13124, c_2])).
% 9.16/3.29  tff(c_13167, plain, $false, inference(negUnitSimplification, [status(thm)], [c_525, c_13165])).
% 9.16/3.29  tff(c_13168, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_520])).
% 9.16/3.29  tff(c_133, plain, (![B_44, A_45]: (~v1_xboole_0(B_44) | B_44=A_45 | ~v1_xboole_0(A_45))), inference(cnfTransformation, [status(thm)], [f_34])).
% 9.16/3.29  tff(c_136, plain, (![A_45]: (k1_xboole_0=A_45 | ~v1_xboole_0(A_45))), inference(resolution, [status(thm)], [c_2, c_133])).
% 9.16/3.29  tff(c_13175, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_13168, c_136])).
% 9.16/3.29  tff(c_12, plain, (![A_5]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 9.16/3.29  tff(c_144, plain, (![A_48, B_49]: (r1_tarski(A_48, B_49) | ~m1_subset_1(A_48, k1_zfmisc_1(B_49)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 9.16/3.29  tff(c_152, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(resolution, [status(thm)], [c_12, c_144])).
% 9.16/3.29  tff(c_13201, plain, (![A_5]: (r1_tarski('#skF_3', A_5))), inference(demodulation, [status(thm), theory('equality')], [c_13175, c_152])).
% 9.16/3.29  tff(c_60, plain, (![A_35]: (m1_subset_1(k6_partfun1(A_35), k1_zfmisc_1(k2_zfmisc_1(A_35, A_35))))), inference(cnfTransformation, [status(thm)], [f_125])).
% 9.16/3.29  tff(c_13394, plain, (![A_461]: (v1_xboole_0(k6_partfun1(A_461)) | ~v1_xboole_0(A_461))), inference(resolution, [status(thm)], [c_60, c_497])).
% 9.16/3.29  tff(c_13203, plain, (![A_45]: (A_45='#skF_3' | ~v1_xboole_0(A_45))), inference(demodulation, [status(thm), theory('equality')], [c_13175, c_136])).
% 9.16/3.29  tff(c_13450, plain, (![A_466]: (k6_partfun1(A_466)='#skF_3' | ~v1_xboole_0(A_466))), inference(resolution, [status(thm)], [c_13394, c_13203])).
% 9.16/3.29  tff(c_13458, plain, (k6_partfun1('#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_13168, c_13450])).
% 9.16/3.29  tff(c_62, plain, (![A_36]: (k6_relat_1(A_36)=k6_partfun1(A_36))), inference(cnfTransformation, [status(thm)], [f_127])).
% 9.16/3.29  tff(c_32, plain, (![A_15]: (k2_funct_1(k6_relat_1(A_15))=k6_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_78])).
% 9.16/3.29  tff(c_81, plain, (![A_15]: (k2_funct_1(k6_partfun1(A_15))=k6_partfun1(A_15))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_62, c_32])).
% 9.16/3.29  tff(c_13487, plain, (k6_partfun1('#skF_3')=k2_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_13458, c_81])).
% 9.16/3.29  tff(c_13500, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_13458, c_13487])).
% 9.16/3.29  tff(c_10, plain, (![B_4]: (k2_zfmisc_1(k1_xboole_0, B_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 9.16/3.29  tff(c_13205, plain, (![B_4]: (k2_zfmisc_1('#skF_3', B_4)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_13175, c_13175, c_10])).
% 9.16/3.29  tff(c_13169, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_520])).
% 9.16/3.29  tff(c_13182, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_13169, c_136])).
% 9.16/3.29  tff(c_13214, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_13175, c_13182])).
% 9.16/3.29  tff(c_16, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_46])).
% 9.16/3.29  tff(c_369, plain, (~r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_16, c_365])).
% 9.16/3.29  tff(c_13218, plain, (~r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_3', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_13214, c_369])).
% 9.16/3.29  tff(c_13576, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13201, c_13500, c_13205, c_13218])).
% 9.16/3.29  tff(c_13578, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_228])).
% 9.16/3.29  tff(c_13730, plain, (![C_498, B_499, A_500]: (v1_xboole_0(C_498) | ~m1_subset_1(C_498, k1_zfmisc_1(k2_zfmisc_1(B_499, A_500))) | ~v1_xboole_0(A_500))), inference(cnfTransformation, [status(thm)], [f_95])).
% 9.16/3.29  tff(c_13754, plain, (v1_xboole_0(k2_funct_1('#skF_3')) | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_13578, c_13730])).
% 9.16/3.29  tff(c_13772, plain, (~v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_13754])).
% 9.16/3.29  tff(c_14150, plain, (![A_530, B_531, C_532]: (k2_relset_1(A_530, B_531, C_532)=k2_relat_1(C_532) | ~m1_subset_1(C_532, k1_zfmisc_1(k2_zfmisc_1(A_530, B_531))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 9.16/3.29  tff(c_14163, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_76, c_14150])).
% 9.16/3.29  tff(c_14178, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_14163])).
% 9.16/3.29  tff(c_13577, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_228])).
% 9.16/3.29  tff(c_14379, plain, (![A_541, B_542, C_543]: (k1_relset_1(A_541, B_542, C_543)=k1_relat_1(C_543) | ~m1_subset_1(C_543, k1_zfmisc_1(k2_zfmisc_1(A_541, B_542))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 9.16/3.29  tff(c_14411, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_13578, c_14379])).
% 9.16/3.29  tff(c_14769, plain, (![B_577, C_578, A_579]: (k1_xboole_0=B_577 | v1_funct_2(C_578, A_579, B_577) | k1_relset_1(A_579, B_577, C_578)!=A_579 | ~m1_subset_1(C_578, k1_zfmisc_1(k2_zfmisc_1(A_579, B_577))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 9.16/3.29  tff(c_14778, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_13578, c_14769])).
% 9.16/3.29  tff(c_14804, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_14411, c_14778])).
% 9.16/3.29  tff(c_14805, plain, (k1_xboole_0='#skF_1' | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_13577, c_14804])).
% 9.16/3.29  tff(c_14814, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_14805])).
% 9.16/3.29  tff(c_14817, plain, (k2_relat_1('#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_30, c_14814])).
% 9.16/3.29  tff(c_14820, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_289, c_80, c_74, c_14178, c_14817])).
% 9.16/3.29  tff(c_14821, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_14805])).
% 9.16/3.29  tff(c_14869, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_14821, c_2])).
% 9.16/3.29  tff(c_14871, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13772, c_14869])).
% 9.16/3.29  tff(c_14873, plain, (v1_xboole_0('#skF_1')), inference(splitRight, [status(thm)], [c_13754])).
% 9.16/3.29  tff(c_14879, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_14873, c_136])).
% 9.16/3.29  tff(c_46, plain, (![A_32]: (v1_funct_2(k1_xboole_0, A_32, k1_xboole_0) | k1_xboole_0=A_32 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_32, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 9.16/3.29  tff(c_83, plain, (![A_32]: (v1_funct_2(k1_xboole_0, A_32, k1_xboole_0) | k1_xboole_0=A_32)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_46])).
% 9.16/3.29  tff(c_15435, plain, (![A_609]: (v1_funct_2('#skF_1', A_609, '#skF_1') | A_609='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_14879, c_14879, c_14879, c_83])).
% 9.16/3.29  tff(c_14872, plain, (v1_xboole_0(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_13754])).
% 9.16/3.29  tff(c_15003, plain, (![A_588]: (A_588='#skF_1' | ~v1_xboole_0(A_588))), inference(demodulation, [status(thm), theory('equality')], [c_14879, c_136])).
% 9.16/3.29  tff(c_15013, plain, (k2_funct_1('#skF_3')='#skF_1'), inference(resolution, [status(thm)], [c_14872, c_15003])).
% 9.16/3.29  tff(c_15024, plain, (~v1_funct_2('#skF_1', '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_15013, c_13577])).
% 9.16/3.29  tff(c_15439, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_15435, c_15024])).
% 9.16/3.29  tff(c_13757, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_76, c_13730])).
% 9.16/3.29  tff(c_13762, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_13757])).
% 9.16/3.29  tff(c_15443, plain, (~v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_15439, c_13762])).
% 9.16/3.29  tff(c_15446, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14873, c_15443])).
% 9.16/3.29  tff(c_15447, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_13757])).
% 9.16/3.29  tff(c_15672, plain, (![A_621]: (v1_xboole_0(k6_partfun1(A_621)) | ~v1_xboole_0(A_621))), inference(resolution, [status(thm)], [c_60, c_13730])).
% 9.16/3.29  tff(c_15454, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_15447, c_136])).
% 9.16/3.29  tff(c_15448, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_13757])).
% 9.16/3.29  tff(c_15462, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_15448, c_136])).
% 9.16/3.29  tff(c_15492, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_15454, c_15462])).
% 9.16/3.29  tff(c_4, plain, (![B_2, A_1]: (~v1_xboole_0(B_2) | B_2=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_34])).
% 9.16/3.29  tff(c_15463, plain, (![A_1]: (A_1='#skF_2' | ~v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_15448, c_4])).
% 9.16/3.29  tff(c_15543, plain, (![A_1]: (A_1='#skF_3' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_15492, c_15463])).
% 9.16/3.29  tff(c_15740, plain, (![A_625]: (k6_partfun1(A_625)='#skF_3' | ~v1_xboole_0(A_625))), inference(resolution, [status(thm)], [c_15672, c_15543])).
% 9.16/3.29  tff(c_15748, plain, (k6_partfun1('#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_15447, c_15740])).
% 9.16/3.29  tff(c_15775, plain, (k6_partfun1('#skF_3')=k2_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_15748, c_81])).
% 9.16/3.29  tff(c_15788, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_15748, c_15775])).
% 9.16/3.29  tff(c_15802, plain, (k2_relat_1('#skF_3')=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_15788, c_28])).
% 9.16/3.29  tff(c_15815, plain, (k2_relat_1('#skF_3')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_289, c_80, c_74, c_15802])).
% 9.16/3.29  tff(c_15484, plain, (![A_5]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_15454, c_12])).
% 9.16/3.29  tff(c_15823, plain, (![A_626, B_627, C_628]: (k2_relset_1(A_626, B_627, C_628)=k2_relat_1(C_628) | ~m1_subset_1(C_628, k1_zfmisc_1(k2_zfmisc_1(A_626, B_627))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 9.16/3.29  tff(c_15845, plain, (![A_626, B_627]: (k2_relset_1(A_626, B_627, '#skF_3')=k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_15484, c_15823])).
% 9.16/3.29  tff(c_15956, plain, (![A_645, B_646]: (k2_relset_1(A_645, B_646, '#skF_3')=k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_15815, c_15845])).
% 9.16/3.29  tff(c_15501, plain, (k2_relset_1('#skF_1', '#skF_3', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_15492, c_15492, c_72])).
% 9.16/3.29  tff(c_15960, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_15956, c_15501])).
% 9.16/3.29  tff(c_15893, plain, (![A_633, B_634, C_635]: (k1_relset_1(A_633, B_634, C_635)=k1_relat_1(C_635) | ~m1_subset_1(C_635, k1_zfmisc_1(k2_zfmisc_1(A_633, B_634))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 9.16/3.29  tff(c_15915, plain, (![A_633, B_634]: (k1_relset_1(A_633, B_634, '#skF_3')=k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_15484, c_15893])).
% 9.16/3.29  tff(c_15968, plain, (![A_633, B_634]: (k1_relset_1(A_633, B_634, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_15960, c_15915])).
% 9.16/3.29  tff(c_50, plain, (![C_34, B_33]: (v1_funct_2(C_34, k1_xboole_0, B_33) | k1_relset_1(k1_xboole_0, B_33, C_34)!=k1_xboole_0 | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_33))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 9.16/3.29  tff(c_85, plain, (![C_34, B_33]: (v1_funct_2(C_34, k1_xboole_0, B_33) | k1_relset_1(k1_xboole_0, B_33, C_34)!=k1_xboole_0 | ~m1_subset_1(C_34, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_50])).
% 9.16/3.29  tff(c_16032, plain, (![C_651, B_652]: (v1_funct_2(C_651, '#skF_3', B_652) | k1_relset_1('#skF_3', B_652, C_651)!='#skF_3' | ~m1_subset_1(C_651, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_15454, c_15454, c_15454, c_15454, c_85])).
% 9.16/3.29  tff(c_16035, plain, (![B_652]: (v1_funct_2('#skF_3', '#skF_3', B_652) | k1_relset_1('#skF_3', B_652, '#skF_3')!='#skF_3')), inference(resolution, [status(thm)], [c_15484, c_16032])).
% 9.16/3.29  tff(c_16041, plain, (![B_652]: (v1_funct_2('#skF_3', '#skF_3', B_652))), inference(demodulation, [status(thm), theory('equality')], [c_15968, c_16035])).
% 9.16/3.29  tff(c_15498, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_15492, c_13577])).
% 9.16/3.29  tff(c_15790, plain, (~v1_funct_2('#skF_3', '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_15788, c_15498])).
% 9.16/3.29  tff(c_16046, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16041, c_15790])).
% 9.16/3.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.16/3.29  
% 9.16/3.29  Inference rules
% 9.16/3.29  ----------------------
% 9.16/3.29  #Ref     : 0
% 9.16/3.29  #Sup     : 3708
% 9.16/3.29  #Fact    : 0
% 9.16/3.29  #Define  : 0
% 9.16/3.29  #Split   : 17
% 9.16/3.29  #Chain   : 0
% 9.16/3.29  #Close   : 0
% 9.16/3.29  
% 9.16/3.29  Ordering : KBO
% 9.16/3.29  
% 9.16/3.29  Simplification rules
% 9.16/3.29  ----------------------
% 9.16/3.29  #Subsume      : 884
% 9.16/3.29  #Demod        : 4997
% 9.16/3.29  #Tautology    : 1859
% 9.16/3.29  #SimpNegUnit  : 56
% 9.16/3.29  #BackRed      : 259
% 9.16/3.29  
% 9.16/3.29  #Partial instantiations: 0
% 9.16/3.29  #Strategies tried      : 1
% 9.16/3.29  
% 9.16/3.29  Timing (in seconds)
% 9.16/3.29  ----------------------
% 9.50/3.29  Preprocessing        : 0.36
% 9.50/3.29  Parsing              : 0.19
% 9.50/3.29  CNF conversion       : 0.02
% 9.50/3.29  Main loop            : 2.13
% 9.50/3.29  Inferencing          : 0.60
% 9.50/3.29  Reduction            : 0.80
% 9.50/3.29  Demodulation         : 0.59
% 9.50/3.29  BG Simplification    : 0.07
% 9.50/3.29  Subsumption          : 0.53
% 9.50/3.29  Abstraction          : 0.09
% 9.50/3.29  MUC search           : 0.00
% 9.50/3.29  Cooper               : 0.00
% 9.50/3.29  Total                : 2.54
% 9.50/3.29  Index Insertion      : 0.00
% 9.50/3.29  Index Deletion       : 0.00
% 9.50/3.29  Index Matching       : 0.00
% 9.50/3.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
