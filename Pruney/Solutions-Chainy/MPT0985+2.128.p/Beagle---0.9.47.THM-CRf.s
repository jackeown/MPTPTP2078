%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:47 EST 2020

% Result     : Theorem 5.98s
% Output     : CNFRefutation 5.98s
% Verified   : 
% Statistics : Number of formulae       :  192 (1363 expanded)
%              Number of leaves         :   40 ( 469 expanded)
%              Depth                    :   13
%              Number of atoms          :  332 (3697 expanded)
%              Number of equality atoms :  123 (1242 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v5_ordinal1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(v5_ordinal1,type,(
    v5_ordinal1: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_150,negated_conjecture,(
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

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_73,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_63,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_111,axiom,(
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

tff(f_121,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_47,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_40,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_133,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(c_80,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_84,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_3497,plain,(
    ! [C_328,A_329,B_330] :
      ( v1_relat_1(C_328)
      | ~ m1_subset_1(C_328,k1_zfmisc_1(k2_zfmisc_1(A_329,B_330))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_3514,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_84,c_3497])).

tff(c_88,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_82,plain,(
    v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_3661,plain,(
    ! [A_345,B_346,C_347] :
      ( k2_relset_1(A_345,B_346,C_347) = k2_relat_1(C_347)
      | ~ m1_subset_1(C_347,k1_zfmisc_1(k2_zfmisc_1(A_345,B_346))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_3674,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_84,c_3661])).

tff(c_3685,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_3674])).

tff(c_38,plain,(
    ! [A_13] :
      ( k1_relat_1(k2_funct_1(A_13)) = k2_relat_1(A_13)
      | ~ v2_funct_1(A_13)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_32,plain,(
    ! [A_12] :
      ( v1_funct_1(k2_funct_1(A_12))
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_78,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_152,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_155,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_152])).

tff(c_158,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_155])).

tff(c_185,plain,(
    ! [C_48,A_49,B_50] :
      ( v1_relat_1(C_48)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_192,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_84,c_185])).

tff(c_201,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_158,c_192])).

tff(c_202,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | ~ m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_209,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_202])).

tff(c_235,plain,(
    ! [C_58,A_59,B_60] :
      ( v1_relat_1(C_58)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_248,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_84,c_235])).

tff(c_383,plain,(
    ! [A_77,B_78,C_79] :
      ( k2_relset_1(A_77,B_78,C_79) = k2_relat_1(C_79)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_390,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_84,c_383])).

tff(c_399,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_390])).

tff(c_34,plain,(
    ! [A_12] :
      ( v1_relat_1(k2_funct_1(A_12))
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_203,plain,(
    v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_28,plain,(
    ! [A_11] :
      ( k2_relat_1(A_11) != k1_xboole_0
      | k1_xboole_0 = A_11
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_256,plain,
    ( k2_relat_1('#skF_5') != k1_xboole_0
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_248,c_28])).

tff(c_258,plain,(
    k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_256])).

tff(c_400,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_399,c_258])).

tff(c_86,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_347,plain,(
    ! [A_71,B_72,C_73] :
      ( k1_relset_1(A_71,B_72,C_73) = k1_relat_1(C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_362,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_84,c_347])).

tff(c_849,plain,(
    ! [B_134,A_135,C_136] :
      ( k1_xboole_0 = B_134
      | k1_relset_1(A_135,B_134,C_136) = A_135
      | ~ v1_funct_2(C_136,A_135,B_134)
      | ~ m1_subset_1(C_136,k1_zfmisc_1(k2_zfmisc_1(A_135,B_134))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_865,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_84,c_849])).

tff(c_881,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_362,c_865])).

tff(c_882,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_400,c_881])).

tff(c_335,plain,(
    ! [A_70] :
      ( k2_relat_1(k2_funct_1(A_70)) = k1_relat_1(A_70)
      | ~ v2_funct_1(A_70)
      | ~ v1_funct_1(A_70)
      | ~ v1_relat_1(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_68,plain,(
    ! [A_27] :
      ( v1_funct_2(A_27,k1_relat_1(A_27),k2_relat_1(A_27))
      | ~ v1_funct_1(A_27)
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_1803,plain,(
    ! [A_187] :
      ( v1_funct_2(k2_funct_1(A_187),k1_relat_1(k2_funct_1(A_187)),k1_relat_1(A_187))
      | ~ v1_funct_1(k2_funct_1(A_187))
      | ~ v1_relat_1(k2_funct_1(A_187))
      | ~ v2_funct_1(A_187)
      | ~ v1_funct_1(A_187)
      | ~ v1_relat_1(A_187) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_335,c_68])).

tff(c_1806,plain,
    ( v1_funct_2(k2_funct_1('#skF_5'),k1_relat_1(k2_funct_1('#skF_5')),'#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_882,c_1803])).

tff(c_1817,plain,
    ( v1_funct_2(k2_funct_1('#skF_5'),k1_relat_1(k2_funct_1('#skF_5')),'#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_248,c_88,c_82,c_203,c_1806])).

tff(c_1820,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_1817])).

tff(c_1823,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_1820])).

tff(c_1827,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_248,c_88,c_1823])).

tff(c_1829,plain,(
    v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_1817])).

tff(c_36,plain,(
    ! [A_13] :
      ( k2_relat_1(k2_funct_1(A_13)) = k1_relat_1(A_13)
      | ~ v2_funct_1(A_13)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_460,plain,(
    ! [A_91] :
      ( m1_subset_1(A_91,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_91),k2_relat_1(A_91))))
      | ~ v1_funct_1(A_91)
      | ~ v1_relat_1(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_2203,plain,(
    ! [A_207] :
      ( m1_subset_1(k2_funct_1(A_207),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_207)),k1_relat_1(A_207))))
      | ~ v1_funct_1(k2_funct_1(A_207))
      | ~ v1_relat_1(k2_funct_1(A_207))
      | ~ v2_funct_1(A_207)
      | ~ v1_funct_1(A_207)
      | ~ v1_relat_1(A_207) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_460])).

tff(c_2221,plain,
    ( m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_5')),'#skF_3')))
    | ~ v1_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_882,c_2203])).

tff(c_2237,plain,(
    m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_5')),'#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_248,c_88,c_82,c_1829,c_203,c_2221])).

tff(c_2257,plain,
    ( m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_5'),'#skF_3')))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_2237])).

tff(c_2270,plain,(
    m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_248,c_88,c_82,c_399,c_2257])).

tff(c_2272,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_209,c_2270])).

tff(c_2273,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_256])).

tff(c_26,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2282,plain,(
    k1_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2273,c_2273,c_26])).

tff(c_30,plain,(
    ! [A_11] :
      ( k1_relat_1(A_11) != k1_xboole_0
      | k1_xboole_0 = A_11
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_255,plain,
    ( k1_relat_1('#skF_5') != k1_xboole_0
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_248,c_30])).

tff(c_257,plain,(
    k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_255])).

tff(c_2275,plain,(
    k1_relat_1('#skF_5') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2273,c_257])).

tff(c_2307,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2282,c_2275])).

tff(c_2308,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_255])).

tff(c_24,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2328,plain,(
    k2_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2308,c_2308,c_24])).

tff(c_2476,plain,(
    ! [A_222,B_223,C_224] :
      ( k2_relset_1(A_222,B_223,C_224) = k2_relat_1(C_224)
      | ~ m1_subset_1(C_224,k1_zfmisc_1(k2_zfmisc_1(A_222,B_223))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_2489,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_84,c_2476])).

tff(c_2492,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_2328,c_2489])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_2329,plain,(
    ! [A_1] : r1_tarski('#skF_5',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2308,c_2])).

tff(c_139,plain,(
    ! [C_38,A_39] :
      ( r2_hidden(C_38,k1_zfmisc_1(A_39))
      | ~ r1_tarski(C_38,A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_22,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,B_10)
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_143,plain,(
    ! [C_38,A_39] :
      ( m1_subset_1(C_38,k1_zfmisc_1(A_39))
      | ~ r1_tarski(C_38,A_39) ) ),
    inference(resolution,[status(thm)],[c_139,c_22])).

tff(c_18,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_54,plain,(
    ! [A_24] :
      ( v1_funct_2(k1_xboole_0,A_24,k1_xboole_0)
      | k1_xboole_0 = A_24
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_24,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_91,plain,(
    ! [A_24] :
      ( v1_funct_2(k1_xboole_0,A_24,k1_xboole_0)
      | k1_xboole_0 = A_24
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_54])).

tff(c_2363,plain,(
    ! [A_24] :
      ( v1_funct_2('#skF_5',A_24,'#skF_5')
      | A_24 = '#skF_5'
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2308,c_2308,c_2308,c_2308,c_2308,c_91])).

tff(c_2364,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_2363])).

tff(c_2395,plain,(
    ~ r1_tarski('#skF_5','#skF_5') ),
    inference(resolution,[status(thm)],[c_143,c_2364])).

tff(c_2399,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2329,c_2395])).

tff(c_2401,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_2363])).

tff(c_2496,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2492,c_2492,c_2401])).

tff(c_2506,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2492,c_248])).

tff(c_2514,plain,(
    v1_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2492,c_88])).

tff(c_2500,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2492,c_2492,c_2328])).

tff(c_2513,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2492,c_82])).

tff(c_2505,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2492,c_2308])).

tff(c_210,plain,(
    ! [A_53] :
      ( v1_relat_1(k2_funct_1(A_53))
      | ~ v1_funct_1(A_53)
      | ~ v1_relat_1(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_217,plain,(
    ! [A_53] :
      ( k1_relat_1(k2_funct_1(A_53)) != k1_xboole_0
      | k2_funct_1(A_53) = k1_xboole_0
      | ~ v1_funct_1(A_53)
      | ~ v1_relat_1(A_53) ) ),
    inference(resolution,[status(thm)],[c_210,c_30])).

tff(c_2880,plain,(
    ! [A_276] :
      ( k1_relat_1(k2_funct_1(A_276)) != '#skF_4'
      | k2_funct_1(A_276) = '#skF_4'
      | ~ v1_funct_1(A_276)
      | ~ v1_relat_1(A_276) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2505,c_2505,c_217])).

tff(c_3472,plain,(
    ! [A_324] :
      ( k2_relat_1(A_324) != '#skF_4'
      | k2_funct_1(A_324) = '#skF_4'
      | ~ v1_funct_1(A_324)
      | ~ v1_relat_1(A_324)
      | ~ v2_funct_1(A_324)
      | ~ v1_funct_1(A_324)
      | ~ v1_relat_1(A_324) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_2880])).

tff(c_3475,plain,
    ( k2_relat_1('#skF_4') != '#skF_4'
    | k2_funct_1('#skF_4') = '#skF_4'
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2513,c_3472])).

tff(c_3478,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2506,c_2514,c_2500,c_3475])).

tff(c_20,plain,(
    ! [B_8] : k2_zfmisc_1(k1_xboole_0,B_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2325,plain,(
    ! [B_8] : k2_zfmisc_1('#skF_5',B_8) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2308,c_2308,c_20])).

tff(c_2498,plain,(
    ! [B_8] : k2_zfmisc_1('#skF_4',B_8) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2492,c_2492,c_2325])).

tff(c_2508,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2492,c_209])).

tff(c_2670,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2498,c_2508])).

tff(c_3479,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3478,c_2670])).

tff(c_3484,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2496,c_3479])).

tff(c_3485,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_202])).

tff(c_3533,plain,
    ( k2_relat_1('#skF_5') != k1_xboole_0
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_3514,c_28])).

tff(c_3543,plain,(
    k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_3533])).

tff(c_3686,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3685,c_3543])).

tff(c_3701,plain,(
    ! [A_348,B_349,C_350] :
      ( k1_relset_1(A_348,B_349,C_350) = k1_relat_1(C_350)
      | ~ m1_subset_1(C_350,k1_zfmisc_1(k2_zfmisc_1(A_348,B_349))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_3724,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_84,c_3701])).

tff(c_4265,plain,(
    ! [B_409,A_410,C_411] :
      ( k1_xboole_0 = B_409
      | k1_relset_1(A_410,B_409,C_411) = A_410
      | ~ v1_funct_2(C_411,A_410,B_409)
      | ~ m1_subset_1(C_411,k1_zfmisc_1(k2_zfmisc_1(A_410,B_409))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_4292,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_84,c_4265])).

tff(c_4312,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_3724,c_4292])).

tff(c_4313,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_3686,c_4312])).

tff(c_3532,plain,
    ( k1_relat_1('#skF_5') != k1_xboole_0
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_3514,c_30])).

tff(c_3542,plain,(
    k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_3532])).

tff(c_4320,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4313,c_3542])).

tff(c_3486,plain,(
    m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_202])).

tff(c_3723,plain,(
    k1_relset_1('#skF_4','#skF_3',k2_funct_1('#skF_5')) = k1_relat_1(k2_funct_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_3486,c_3701])).

tff(c_4396,plain,(
    ! [B_414,C_415,A_416] :
      ( k1_xboole_0 = B_414
      | v1_funct_2(C_415,A_416,B_414)
      | k1_relset_1(A_416,B_414,C_415) != A_416
      | ~ m1_subset_1(C_415,k1_zfmisc_1(k2_zfmisc_1(A_416,B_414))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_4420,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | k1_relset_1('#skF_4','#skF_3',k2_funct_1('#skF_5')) != '#skF_4' ),
    inference(resolution,[status(thm)],[c_3486,c_4396])).

tff(c_4437,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | k1_relat_1(k2_funct_1('#skF_5')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3723,c_4420])).

tff(c_4438,plain,(
    k1_relat_1(k2_funct_1('#skF_5')) != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_3485,c_4320,c_4437])).

tff(c_4446,plain,
    ( k2_relat_1('#skF_5') != '#skF_4'
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_4438])).

tff(c_4449,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3514,c_88,c_82,c_3685,c_4446])).

tff(c_4450,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_3533])).

tff(c_4470,plain,(
    k1_relat_1('#skF_5') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4450,c_3542])).

tff(c_4458,plain,(
    k1_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4450,c_4450,c_26])).

tff(c_4477,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4470,c_4458])).

tff(c_4478,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_3532])).

tff(c_4487,plain,(
    k2_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4478,c_4478,c_24])).

tff(c_4728,plain,(
    ! [A_437,B_438,C_439] :
      ( k2_relset_1(A_437,B_438,C_439) = k2_relat_1(C_439)
      | ~ m1_subset_1(C_439,k1_zfmisc_1(k2_zfmisc_1(A_437,B_438))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_4744,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_84,c_4728])).

tff(c_4749,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_4487,c_4744])).

tff(c_4768,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4749,c_3514])).

tff(c_4773,plain,(
    v1_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4749,c_88])).

tff(c_4488,plain,(
    ! [A_1] : r1_tarski('#skF_5',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4478,c_2])).

tff(c_4762,plain,(
    ! [A_1] : r1_tarski('#skF_4',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4749,c_4488])).

tff(c_4763,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4749,c_4749,c_4487])).

tff(c_4479,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_3532])).

tff(c_4549,plain,(
    k1_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4478,c_4479])).

tff(c_4765,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4749,c_4749,c_4549])).

tff(c_5103,plain,(
    ! [B_476,A_477] :
      ( v1_funct_2(B_476,k1_relat_1(B_476),A_477)
      | ~ r1_tarski(k2_relat_1(B_476),A_477)
      | ~ v1_funct_1(B_476)
      | ~ v1_relat_1(B_476) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_5109,plain,(
    ! [A_477] :
      ( v1_funct_2('#skF_4','#skF_4',A_477)
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_477)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4765,c_5103])).

tff(c_5115,plain,(
    ! [A_477] : v1_funct_2('#skF_4','#skF_4',A_477) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4768,c_4773,c_4762,c_4763,c_5109])).

tff(c_3513,plain,(
    v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_3486,c_3497])).

tff(c_3541,plain,
    ( k2_relat_1(k2_funct_1('#skF_5')) != k1_xboole_0
    | k2_funct_1('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3513,c_28])).

tff(c_4624,plain,
    ( k2_relat_1(k2_funct_1('#skF_5')) != '#skF_5'
    | k2_funct_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4478,c_4478,c_3541])).

tff(c_4625,plain,(
    k2_relat_1(k2_funct_1('#skF_5')) != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_4624])).

tff(c_4628,plain,
    ( k1_relat_1('#skF_5') != '#skF_5'
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_4625])).

tff(c_4631,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3514,c_88,c_82,c_4549,c_4628])).

tff(c_4632,plain,(
    k2_funct_1('#skF_5') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_4624])).

tff(c_4636,plain,(
    ~ v1_funct_2('#skF_5','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4632,c_3485])).

tff(c_4755,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4749,c_4636])).

tff(c_5119,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5115,c_4755])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:31:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.98/2.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.98/2.22  
% 5.98/2.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.98/2.22  %$ v1_funct_2 > v5_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v5_ordinal1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 5.98/2.22  
% 5.98/2.22  %Foreground sorts:
% 5.98/2.22  
% 5.98/2.22  
% 5.98/2.22  %Background operators:
% 5.98/2.22  
% 5.98/2.22  
% 5.98/2.22  %Foreground operators:
% 5.98/2.22  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.98/2.22  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.98/2.22  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.98/2.22  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.98/2.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.98/2.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.98/2.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.98/2.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.98/2.22  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.98/2.22  tff(v5_ordinal1, type, v5_ordinal1: $i > $o).
% 5.98/2.22  tff('#skF_5', type, '#skF_5': $i).
% 5.98/2.22  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.98/2.22  tff('#skF_3', type, '#skF_3': $i).
% 5.98/2.22  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.98/2.22  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.98/2.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.98/2.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.98/2.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.98/2.22  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.98/2.22  tff('#skF_4', type, '#skF_4': $i).
% 5.98/2.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.98/2.22  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.98/2.22  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.98/2.22  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.98/2.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.98/2.22  
% 5.98/2.24  tff(f_150, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 5.98/2.24  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.98/2.24  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.98/2.24  tff(f_73, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 5.98/2.24  tff(f_63, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 5.98/2.24  tff(f_55, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 5.98/2.24  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.98/2.24  tff(f_111, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 5.98/2.24  tff(f_121, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 5.98/2.24  tff(f_47, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 5.98/2.24  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.98/2.24  tff(f_34, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 5.98/2.24  tff(f_44, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 5.98/2.24  tff(f_40, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.98/2.24  tff(f_133, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 5.98/2.24  tff(c_80, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_150])).
% 5.98/2.24  tff(c_84, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_150])).
% 5.98/2.24  tff(c_3497, plain, (![C_328, A_329, B_330]: (v1_relat_1(C_328) | ~m1_subset_1(C_328, k1_zfmisc_1(k2_zfmisc_1(A_329, B_330))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.98/2.24  tff(c_3514, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_84, c_3497])).
% 5.98/2.24  tff(c_88, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_150])).
% 5.98/2.24  tff(c_82, plain, (v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_150])).
% 5.98/2.24  tff(c_3661, plain, (![A_345, B_346, C_347]: (k2_relset_1(A_345, B_346, C_347)=k2_relat_1(C_347) | ~m1_subset_1(C_347, k1_zfmisc_1(k2_zfmisc_1(A_345, B_346))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.98/2.24  tff(c_3674, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_84, c_3661])).
% 5.98/2.24  tff(c_3685, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_3674])).
% 5.98/2.24  tff(c_38, plain, (![A_13]: (k1_relat_1(k2_funct_1(A_13))=k2_relat_1(A_13) | ~v2_funct_1(A_13) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.98/2.24  tff(c_32, plain, (![A_12]: (v1_funct_1(k2_funct_1(A_12)) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.98/2.24  tff(c_78, plain, (~m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | ~v1_funct_1(k2_funct_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_150])).
% 5.98/2.24  tff(c_152, plain, (~v1_funct_1(k2_funct_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_78])).
% 5.98/2.24  tff(c_155, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_32, c_152])).
% 5.98/2.24  tff(c_158, plain, (~v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_155])).
% 5.98/2.24  tff(c_185, plain, (![C_48, A_49, B_50]: (v1_relat_1(C_48) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.98/2.24  tff(c_192, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_84, c_185])).
% 5.98/2.24  tff(c_201, plain, $false, inference(negUnitSimplification, [status(thm)], [c_158, c_192])).
% 5.98/2.24  tff(c_202, plain, (~v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | ~m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitRight, [status(thm)], [c_78])).
% 5.98/2.24  tff(c_209, plain, (~m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitLeft, [status(thm)], [c_202])).
% 5.98/2.24  tff(c_235, plain, (![C_58, A_59, B_60]: (v1_relat_1(C_58) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.98/2.24  tff(c_248, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_84, c_235])).
% 5.98/2.24  tff(c_383, plain, (![A_77, B_78, C_79]: (k2_relset_1(A_77, B_78, C_79)=k2_relat_1(C_79) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.98/2.24  tff(c_390, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_84, c_383])).
% 5.98/2.24  tff(c_399, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_390])).
% 5.98/2.24  tff(c_34, plain, (![A_12]: (v1_relat_1(k2_funct_1(A_12)) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.98/2.24  tff(c_203, plain, (v1_funct_1(k2_funct_1('#skF_5'))), inference(splitRight, [status(thm)], [c_78])).
% 5.98/2.24  tff(c_28, plain, (![A_11]: (k2_relat_1(A_11)!=k1_xboole_0 | k1_xboole_0=A_11 | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.98/2.24  tff(c_256, plain, (k2_relat_1('#skF_5')!=k1_xboole_0 | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_248, c_28])).
% 5.98/2.24  tff(c_258, plain, (k2_relat_1('#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_256])).
% 5.98/2.24  tff(c_400, plain, (k1_xboole_0!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_399, c_258])).
% 5.98/2.24  tff(c_86, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_150])).
% 5.98/2.24  tff(c_347, plain, (![A_71, B_72, C_73]: (k1_relset_1(A_71, B_72, C_73)=k1_relat_1(C_73) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.98/2.24  tff(c_362, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_84, c_347])).
% 5.98/2.24  tff(c_849, plain, (![B_134, A_135, C_136]: (k1_xboole_0=B_134 | k1_relset_1(A_135, B_134, C_136)=A_135 | ~v1_funct_2(C_136, A_135, B_134) | ~m1_subset_1(C_136, k1_zfmisc_1(k2_zfmisc_1(A_135, B_134))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.98/2.24  tff(c_865, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_84, c_849])).
% 5.98/2.24  tff(c_881, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_362, c_865])).
% 5.98/2.24  tff(c_882, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_400, c_881])).
% 5.98/2.24  tff(c_335, plain, (![A_70]: (k2_relat_1(k2_funct_1(A_70))=k1_relat_1(A_70) | ~v2_funct_1(A_70) | ~v1_funct_1(A_70) | ~v1_relat_1(A_70))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.98/2.24  tff(c_68, plain, (![A_27]: (v1_funct_2(A_27, k1_relat_1(A_27), k2_relat_1(A_27)) | ~v1_funct_1(A_27) | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_121])).
% 5.98/2.24  tff(c_1803, plain, (![A_187]: (v1_funct_2(k2_funct_1(A_187), k1_relat_1(k2_funct_1(A_187)), k1_relat_1(A_187)) | ~v1_funct_1(k2_funct_1(A_187)) | ~v1_relat_1(k2_funct_1(A_187)) | ~v2_funct_1(A_187) | ~v1_funct_1(A_187) | ~v1_relat_1(A_187))), inference(superposition, [status(thm), theory('equality')], [c_335, c_68])).
% 5.98/2.24  tff(c_1806, plain, (v1_funct_2(k2_funct_1('#skF_5'), k1_relat_1(k2_funct_1('#skF_5')), '#skF_3') | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_882, c_1803])).
% 5.98/2.24  tff(c_1817, plain, (v1_funct_2(k2_funct_1('#skF_5'), k1_relat_1(k2_funct_1('#skF_5')), '#skF_3') | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_248, c_88, c_82, c_203, c_1806])).
% 5.98/2.24  tff(c_1820, plain, (~v1_relat_1(k2_funct_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_1817])).
% 5.98/2.24  tff(c_1823, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_34, c_1820])).
% 5.98/2.24  tff(c_1827, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_248, c_88, c_1823])).
% 5.98/2.24  tff(c_1829, plain, (v1_relat_1(k2_funct_1('#skF_5'))), inference(splitRight, [status(thm)], [c_1817])).
% 5.98/2.24  tff(c_36, plain, (![A_13]: (k2_relat_1(k2_funct_1(A_13))=k1_relat_1(A_13) | ~v2_funct_1(A_13) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.98/2.24  tff(c_460, plain, (![A_91]: (m1_subset_1(A_91, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_91), k2_relat_1(A_91)))) | ~v1_funct_1(A_91) | ~v1_relat_1(A_91))), inference(cnfTransformation, [status(thm)], [f_121])).
% 5.98/2.24  tff(c_2203, plain, (![A_207]: (m1_subset_1(k2_funct_1(A_207), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_207)), k1_relat_1(A_207)))) | ~v1_funct_1(k2_funct_1(A_207)) | ~v1_relat_1(k2_funct_1(A_207)) | ~v2_funct_1(A_207) | ~v1_funct_1(A_207) | ~v1_relat_1(A_207))), inference(superposition, [status(thm), theory('equality')], [c_36, c_460])).
% 5.98/2.24  tff(c_2221, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_5')), '#skF_3'))) | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_882, c_2203])).
% 5.98/2.24  tff(c_2237, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_5')), '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_248, c_88, c_82, c_1829, c_203, c_2221])).
% 5.98/2.24  tff(c_2257, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_5'), '#skF_3'))) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_38, c_2237])).
% 5.98/2.24  tff(c_2270, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_248, c_88, c_82, c_399, c_2257])).
% 5.98/2.24  tff(c_2272, plain, $false, inference(negUnitSimplification, [status(thm)], [c_209, c_2270])).
% 5.98/2.24  tff(c_2273, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_256])).
% 5.98/2.24  tff(c_26, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.98/2.24  tff(c_2282, plain, (k1_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2273, c_2273, c_26])).
% 5.98/2.24  tff(c_30, plain, (![A_11]: (k1_relat_1(A_11)!=k1_xboole_0 | k1_xboole_0=A_11 | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.98/2.24  tff(c_255, plain, (k1_relat_1('#skF_5')!=k1_xboole_0 | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_248, c_30])).
% 5.98/2.24  tff(c_257, plain, (k1_relat_1('#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_255])).
% 5.98/2.24  tff(c_2275, plain, (k1_relat_1('#skF_5')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2273, c_257])).
% 5.98/2.24  tff(c_2307, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2282, c_2275])).
% 5.98/2.24  tff(c_2308, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_255])).
% 5.98/2.24  tff(c_24, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.98/2.24  tff(c_2328, plain, (k2_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2308, c_2308, c_24])).
% 5.98/2.24  tff(c_2476, plain, (![A_222, B_223, C_224]: (k2_relset_1(A_222, B_223, C_224)=k2_relat_1(C_224) | ~m1_subset_1(C_224, k1_zfmisc_1(k2_zfmisc_1(A_222, B_223))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.98/2.24  tff(c_2489, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_84, c_2476])).
% 5.98/2.24  tff(c_2492, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_2328, c_2489])).
% 5.98/2.24  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.98/2.24  tff(c_2329, plain, (![A_1]: (r1_tarski('#skF_5', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_2308, c_2])).
% 5.98/2.24  tff(c_139, plain, (![C_38, A_39]: (r2_hidden(C_38, k1_zfmisc_1(A_39)) | ~r1_tarski(C_38, A_39))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.98/2.24  tff(c_22, plain, (![A_9, B_10]: (m1_subset_1(A_9, B_10) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.98/2.24  tff(c_143, plain, (![C_38, A_39]: (m1_subset_1(C_38, k1_zfmisc_1(A_39)) | ~r1_tarski(C_38, A_39))), inference(resolution, [status(thm)], [c_139, c_22])).
% 5.98/2.24  tff(c_18, plain, (![A_7]: (k2_zfmisc_1(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.98/2.24  tff(c_54, plain, (![A_24]: (v1_funct_2(k1_xboole_0, A_24, k1_xboole_0) | k1_xboole_0=A_24 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_24, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.98/2.24  tff(c_91, plain, (![A_24]: (v1_funct_2(k1_xboole_0, A_24, k1_xboole_0) | k1_xboole_0=A_24 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_54])).
% 5.98/2.24  tff(c_2363, plain, (![A_24]: (v1_funct_2('#skF_5', A_24, '#skF_5') | A_24='#skF_5' | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_2308, c_2308, c_2308, c_2308, c_2308, c_91])).
% 5.98/2.24  tff(c_2364, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_2363])).
% 5.98/2.24  tff(c_2395, plain, (~r1_tarski('#skF_5', '#skF_5')), inference(resolution, [status(thm)], [c_143, c_2364])).
% 5.98/2.24  tff(c_2399, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2329, c_2395])).
% 5.98/2.24  tff(c_2401, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5'))), inference(splitRight, [status(thm)], [c_2363])).
% 5.98/2.24  tff(c_2496, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2492, c_2492, c_2401])).
% 5.98/2.24  tff(c_2506, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2492, c_248])).
% 5.98/2.24  tff(c_2514, plain, (v1_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2492, c_88])).
% 5.98/2.24  tff(c_2500, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2492, c_2492, c_2328])).
% 5.98/2.24  tff(c_2513, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2492, c_82])).
% 5.98/2.24  tff(c_2505, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2492, c_2308])).
% 5.98/2.24  tff(c_210, plain, (![A_53]: (v1_relat_1(k2_funct_1(A_53)) | ~v1_funct_1(A_53) | ~v1_relat_1(A_53))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.98/2.24  tff(c_217, plain, (![A_53]: (k1_relat_1(k2_funct_1(A_53))!=k1_xboole_0 | k2_funct_1(A_53)=k1_xboole_0 | ~v1_funct_1(A_53) | ~v1_relat_1(A_53))), inference(resolution, [status(thm)], [c_210, c_30])).
% 5.98/2.24  tff(c_2880, plain, (![A_276]: (k1_relat_1(k2_funct_1(A_276))!='#skF_4' | k2_funct_1(A_276)='#skF_4' | ~v1_funct_1(A_276) | ~v1_relat_1(A_276))), inference(demodulation, [status(thm), theory('equality')], [c_2505, c_2505, c_217])).
% 5.98/2.24  tff(c_3472, plain, (![A_324]: (k2_relat_1(A_324)!='#skF_4' | k2_funct_1(A_324)='#skF_4' | ~v1_funct_1(A_324) | ~v1_relat_1(A_324) | ~v2_funct_1(A_324) | ~v1_funct_1(A_324) | ~v1_relat_1(A_324))), inference(superposition, [status(thm), theory('equality')], [c_38, c_2880])).
% 5.98/2.24  tff(c_3475, plain, (k2_relat_1('#skF_4')!='#skF_4' | k2_funct_1('#skF_4')='#skF_4' | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_2513, c_3472])).
% 5.98/2.24  tff(c_3478, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2506, c_2514, c_2500, c_3475])).
% 5.98/2.24  tff(c_20, plain, (![B_8]: (k2_zfmisc_1(k1_xboole_0, B_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.98/2.24  tff(c_2325, plain, (![B_8]: (k2_zfmisc_1('#skF_5', B_8)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2308, c_2308, c_20])).
% 5.98/2.24  tff(c_2498, plain, (![B_8]: (k2_zfmisc_1('#skF_4', B_8)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2492, c_2492, c_2325])).
% 5.98/2.24  tff(c_2508, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2492, c_209])).
% 5.98/2.24  tff(c_2670, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2498, c_2508])).
% 5.98/2.24  tff(c_3479, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3478, c_2670])).
% 5.98/2.24  tff(c_3484, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2496, c_3479])).
% 5.98/2.24  tff(c_3485, plain, (~v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_202])).
% 5.98/2.24  tff(c_3533, plain, (k2_relat_1('#skF_5')!=k1_xboole_0 | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_3514, c_28])).
% 5.98/2.24  tff(c_3543, plain, (k2_relat_1('#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_3533])).
% 5.98/2.24  tff(c_3686, plain, (k1_xboole_0!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3685, c_3543])).
% 5.98/2.24  tff(c_3701, plain, (![A_348, B_349, C_350]: (k1_relset_1(A_348, B_349, C_350)=k1_relat_1(C_350) | ~m1_subset_1(C_350, k1_zfmisc_1(k2_zfmisc_1(A_348, B_349))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.98/2.24  tff(c_3724, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_84, c_3701])).
% 5.98/2.24  tff(c_4265, plain, (![B_409, A_410, C_411]: (k1_xboole_0=B_409 | k1_relset_1(A_410, B_409, C_411)=A_410 | ~v1_funct_2(C_411, A_410, B_409) | ~m1_subset_1(C_411, k1_zfmisc_1(k2_zfmisc_1(A_410, B_409))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.98/2.24  tff(c_4292, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_84, c_4265])).
% 5.98/2.24  tff(c_4312, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_3724, c_4292])).
% 5.98/2.24  tff(c_4313, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_3686, c_4312])).
% 5.98/2.24  tff(c_3532, plain, (k1_relat_1('#skF_5')!=k1_xboole_0 | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_3514, c_30])).
% 5.98/2.24  tff(c_3542, plain, (k1_relat_1('#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_3532])).
% 5.98/2.24  tff(c_4320, plain, (k1_xboole_0!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4313, c_3542])).
% 5.98/2.24  tff(c_3486, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitRight, [status(thm)], [c_202])).
% 5.98/2.24  tff(c_3723, plain, (k1_relset_1('#skF_4', '#skF_3', k2_funct_1('#skF_5'))=k1_relat_1(k2_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_3486, c_3701])).
% 5.98/2.24  tff(c_4396, plain, (![B_414, C_415, A_416]: (k1_xboole_0=B_414 | v1_funct_2(C_415, A_416, B_414) | k1_relset_1(A_416, B_414, C_415)!=A_416 | ~m1_subset_1(C_415, k1_zfmisc_1(k2_zfmisc_1(A_416, B_414))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.98/2.24  tff(c_4420, plain, (k1_xboole_0='#skF_3' | v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | k1_relset_1('#skF_4', '#skF_3', k2_funct_1('#skF_5'))!='#skF_4'), inference(resolution, [status(thm)], [c_3486, c_4396])).
% 5.98/2.24  tff(c_4437, plain, (k1_xboole_0='#skF_3' | v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | k1_relat_1(k2_funct_1('#skF_5'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3723, c_4420])).
% 5.98/2.24  tff(c_4438, plain, (k1_relat_1(k2_funct_1('#skF_5'))!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_3485, c_4320, c_4437])).
% 5.98/2.24  tff(c_4446, plain, (k2_relat_1('#skF_5')!='#skF_4' | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_38, c_4438])).
% 5.98/2.24  tff(c_4449, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3514, c_88, c_82, c_3685, c_4446])).
% 5.98/2.24  tff(c_4450, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_3533])).
% 5.98/2.24  tff(c_4470, plain, (k1_relat_1('#skF_5')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_4450, c_3542])).
% 5.98/2.24  tff(c_4458, plain, (k1_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_4450, c_4450, c_26])).
% 5.98/2.24  tff(c_4477, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4470, c_4458])).
% 5.98/2.24  tff(c_4478, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_3532])).
% 5.98/2.24  tff(c_4487, plain, (k2_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_4478, c_4478, c_24])).
% 5.98/2.24  tff(c_4728, plain, (![A_437, B_438, C_439]: (k2_relset_1(A_437, B_438, C_439)=k2_relat_1(C_439) | ~m1_subset_1(C_439, k1_zfmisc_1(k2_zfmisc_1(A_437, B_438))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.98/2.24  tff(c_4744, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_84, c_4728])).
% 5.98/2.24  tff(c_4749, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_4487, c_4744])).
% 5.98/2.24  tff(c_4768, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4749, c_3514])).
% 5.98/2.24  tff(c_4773, plain, (v1_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4749, c_88])).
% 5.98/2.24  tff(c_4488, plain, (![A_1]: (r1_tarski('#skF_5', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_4478, c_2])).
% 5.98/2.24  tff(c_4762, plain, (![A_1]: (r1_tarski('#skF_4', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_4749, c_4488])).
% 5.98/2.24  tff(c_4763, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4749, c_4749, c_4487])).
% 5.98/2.24  tff(c_4479, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_3532])).
% 5.98/2.24  tff(c_4549, plain, (k1_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_4478, c_4479])).
% 5.98/2.24  tff(c_4765, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4749, c_4749, c_4549])).
% 5.98/2.24  tff(c_5103, plain, (![B_476, A_477]: (v1_funct_2(B_476, k1_relat_1(B_476), A_477) | ~r1_tarski(k2_relat_1(B_476), A_477) | ~v1_funct_1(B_476) | ~v1_relat_1(B_476))), inference(cnfTransformation, [status(thm)], [f_133])).
% 5.98/2.24  tff(c_5109, plain, (![A_477]: (v1_funct_2('#skF_4', '#skF_4', A_477) | ~r1_tarski(k2_relat_1('#skF_4'), A_477) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_4765, c_5103])).
% 5.98/2.24  tff(c_5115, plain, (![A_477]: (v1_funct_2('#skF_4', '#skF_4', A_477))), inference(demodulation, [status(thm), theory('equality')], [c_4768, c_4773, c_4762, c_4763, c_5109])).
% 5.98/2.24  tff(c_3513, plain, (v1_relat_1(k2_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_3486, c_3497])).
% 5.98/2.24  tff(c_3541, plain, (k2_relat_1(k2_funct_1('#skF_5'))!=k1_xboole_0 | k2_funct_1('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_3513, c_28])).
% 5.98/2.24  tff(c_4624, plain, (k2_relat_1(k2_funct_1('#skF_5'))!='#skF_5' | k2_funct_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_4478, c_4478, c_3541])).
% 5.98/2.24  tff(c_4625, plain, (k2_relat_1(k2_funct_1('#skF_5'))!='#skF_5'), inference(splitLeft, [status(thm)], [c_4624])).
% 5.98/2.24  tff(c_4628, plain, (k1_relat_1('#skF_5')!='#skF_5' | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_36, c_4625])).
% 5.98/2.24  tff(c_4631, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3514, c_88, c_82, c_4549, c_4628])).
% 5.98/2.24  tff(c_4632, plain, (k2_funct_1('#skF_5')='#skF_5'), inference(splitRight, [status(thm)], [c_4624])).
% 5.98/2.24  tff(c_4636, plain, (~v1_funct_2('#skF_5', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4632, c_3485])).
% 5.98/2.24  tff(c_4755, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4749, c_4636])).
% 5.98/2.24  tff(c_5119, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5115, c_4755])).
% 5.98/2.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.98/2.24  
% 5.98/2.24  Inference rules
% 5.98/2.24  ----------------------
% 5.98/2.24  #Ref     : 0
% 5.98/2.24  #Sup     : 1056
% 5.98/2.24  #Fact    : 0
% 5.98/2.24  #Define  : 0
% 5.98/2.24  #Split   : 19
% 5.98/2.24  #Chain   : 0
% 5.98/2.24  #Close   : 0
% 5.98/2.24  
% 5.98/2.24  Ordering : KBO
% 5.98/2.24  
% 5.98/2.24  Simplification rules
% 5.98/2.24  ----------------------
% 5.98/2.24  #Subsume      : 96
% 5.98/2.24  #Demod        : 944
% 5.98/2.24  #Tautology    : 540
% 5.98/2.24  #SimpNegUnit  : 16
% 5.98/2.24  #BackRed      : 117
% 5.98/2.24  
% 5.98/2.24  #Partial instantiations: 0
% 5.98/2.24  #Strategies tried      : 1
% 5.98/2.24  
% 5.98/2.24  Timing (in seconds)
% 5.98/2.24  ----------------------
% 5.98/2.25  Preprocessing        : 0.36
% 5.98/2.25  Parsing              : 0.20
% 5.98/2.25  CNF conversion       : 0.02
% 5.98/2.25  Main loop            : 1.02
% 5.98/2.25  Inferencing          : 0.39
% 5.98/2.25  Reduction            : 0.31
% 5.98/2.25  Demodulation         : 0.22
% 5.98/2.25  BG Simplification    : 0.05
% 5.98/2.25  Subsumption          : 0.18
% 5.98/2.25  Abstraction          : 0.06
% 5.98/2.25  MUC search           : 0.00
% 5.98/2.25  Cooper               : 0.00
% 5.98/2.25  Total                : 1.44
% 5.98/2.25  Index Insertion      : 0.00
% 5.98/2.25  Index Deletion       : 0.00
% 5.98/2.25  Index Matching       : 0.00
% 5.98/2.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
