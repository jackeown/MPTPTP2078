%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:42 EST 2020

% Result     : Theorem 7.47s
% Output     : CNFRefutation 7.86s
% Verified   : 
% Statistics : Number of formulae       :  235 (2399 expanded)
%              Number of leaves         :   42 ( 787 expanded)
%              Depth                    :   16
%              Number of atoms          :  444 (6898 expanded)
%              Number of equality atoms :  135 (2199 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_148,negated_conjecture,(
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

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_71,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_61,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_108,axiom,(
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

tff(f_131,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_121,axiom,(
    ! [A,B] :
    ? [C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
      & v1_relat_1(C)
      & v4_relat_1(C,A)
      & v5_relat_1(C,B)
      & v1_funct_1(C)
      & v1_funct_2(C,A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_funct_2)).

tff(f_82,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_76,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_162,plain,(
    ! [C_66,A_67,B_68] :
      ( v1_relat_1(C_66)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_166,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_76,c_162])).

tff(c_80,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_74,plain,(
    v2_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_72,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_4901,plain,(
    ! [A_1439,B_1440,C_1441] :
      ( k2_relset_1(A_1439,B_1440,C_1441) = k2_relat_1(C_1441)
      | ~ m1_subset_1(C_1441,k1_zfmisc_1(k2_zfmisc_1(A_1439,B_1440))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_4919,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_76,c_4901])).

tff(c_4926,plain,(
    k2_relat_1('#skF_6') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_4919])).

tff(c_30,plain,(
    ! [A_14] :
      ( k1_relat_1(k2_funct_1(A_14)) = k2_relat_1(A_14)
      | ~ v2_funct_1(A_14)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_24,plain,(
    ! [A_13] :
      ( v1_funct_1(k2_funct_1(A_13))
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_70,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4')))
    | ~ v1_funct_2(k2_funct_1('#skF_6'),'#skF_5','#skF_4')
    | ~ v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_123,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_126,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_24,c_123])).

tff(c_129,plain,(
    ~ v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_126])).

tff(c_151,plain,(
    ! [C_61,A_62,B_63] :
      ( v1_relat_1(C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_154,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_76,c_151])).

tff(c_158,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_129,c_154])).

tff(c_159,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_6'),'#skF_5','#skF_4')
    | ~ m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_214,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_159])).

tff(c_426,plain,(
    ! [A_114,B_115,C_116] :
      ( k2_relset_1(A_114,B_115,C_116) = k2_relat_1(C_116)
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1(A_114,B_115))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_435,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_76,c_426])).

tff(c_439,plain,(
    k2_relat_1('#skF_6') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_435])).

tff(c_26,plain,(
    ! [A_13] :
      ( v1_relat_1(k2_funct_1(A_13))
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_160,plain,(
    v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_20,plain,(
    ! [A_12] :
      ( k2_relat_1(A_12) != k1_xboole_0
      | k1_xboole_0 = A_12
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_174,plain,
    ( k2_relat_1('#skF_6') != k1_xboole_0
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_166,c_20])).

tff(c_176,plain,(
    k2_relat_1('#skF_6') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_174])).

tff(c_440,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_439,c_176])).

tff(c_78,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_537,plain,(
    ! [A_125,B_126,C_127] :
      ( k1_relset_1(A_125,B_126,C_127) = k1_relat_1(C_127)
      | ~ m1_subset_1(C_127,k1_zfmisc_1(k2_zfmisc_1(A_125,B_126))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_557,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_76,c_537])).

tff(c_1047,plain,(
    ! [B_164,A_165,C_166] :
      ( k1_xboole_0 = B_164
      | k1_relset_1(A_165,B_164,C_166) = A_165
      | ~ v1_funct_2(C_166,A_165,B_164)
      | ~ m1_subset_1(C_166,k1_zfmisc_1(k2_zfmisc_1(A_165,B_164))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1068,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_76,c_1047])).

tff(c_1085,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_557,c_1068])).

tff(c_1086,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_440,c_1085])).

tff(c_328,plain,(
    ! [A_100] :
      ( k2_relat_1(k2_funct_1(A_100)) = k1_relat_1(A_100)
      | ~ v2_funct_1(A_100)
      | ~ v1_funct_1(A_100)
      | ~ v1_relat_1(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_66,plain,(
    ! [A_34] :
      ( v1_funct_2(A_34,k1_relat_1(A_34),k2_relat_1(A_34))
      | ~ v1_funct_1(A_34)
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_2916,plain,(
    ! [A_1338] :
      ( v1_funct_2(k2_funct_1(A_1338),k1_relat_1(k2_funct_1(A_1338)),k1_relat_1(A_1338))
      | ~ v1_funct_1(k2_funct_1(A_1338))
      | ~ v1_relat_1(k2_funct_1(A_1338))
      | ~ v2_funct_1(A_1338)
      | ~ v1_funct_1(A_1338)
      | ~ v1_relat_1(A_1338) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_328,c_66])).

tff(c_2925,plain,
    ( v1_funct_2(k2_funct_1('#skF_6'),k1_relat_1(k2_funct_1('#skF_6')),'#skF_4')
    | ~ v1_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6'))
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1086,c_2916])).

tff(c_2943,plain,
    ( v1_funct_2(k2_funct_1('#skF_6'),k1_relat_1(k2_funct_1('#skF_6')),'#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_80,c_74,c_160,c_2925])).

tff(c_2948,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_2943])).

tff(c_2951,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_26,c_2948])).

tff(c_2955,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_80,c_2951])).

tff(c_2957,plain,(
    v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_2943])).

tff(c_28,plain,(
    ! [A_14] :
      ( k2_relat_1(k2_funct_1(A_14)) = k1_relat_1(A_14)
      | ~ v2_funct_1(A_14)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_450,plain,(
    ! [A_117] :
      ( m1_subset_1(A_117,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_117),k2_relat_1(A_117))))
      | ~ v1_funct_1(A_117)
      | ~ v1_relat_1(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_4402,plain,(
    ! [A_1376] :
      ( m1_subset_1(k2_funct_1(A_1376),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_1376)),k1_relat_1(A_1376))))
      | ~ v1_funct_1(k2_funct_1(A_1376))
      | ~ v1_relat_1(k2_funct_1(A_1376))
      | ~ v2_funct_1(A_1376)
      | ~ v1_funct_1(A_1376)
      | ~ v1_relat_1(A_1376) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_450])).

tff(c_4429,plain,
    ( m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_6')),'#skF_4')))
    | ~ v1_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6'))
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1086,c_4402])).

tff(c_4453,plain,(
    m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_6')),'#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_80,c_74,c_2957,c_160,c_4429])).

tff(c_4478,plain,
    ( m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_6'),'#skF_4')))
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_4453])).

tff(c_4492,plain,(
    m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_80,c_74,c_439,c_4478])).

tff(c_4494,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_214,c_4492])).

tff(c_4495,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_6'),'#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_159])).

tff(c_4927,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4926,c_176])).

tff(c_4726,plain,(
    ! [A_1410,B_1411,C_1412] :
      ( k1_relset_1(A_1410,B_1411,C_1412) = k1_relat_1(C_1412)
      | ~ m1_subset_1(C_1412,k1_zfmisc_1(k2_zfmisc_1(A_1410,B_1411))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_4742,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_76,c_4726])).

tff(c_5407,plain,(
    ! [B_1470,A_1471,C_1472] :
      ( k1_xboole_0 = B_1470
      | k1_relset_1(A_1471,B_1470,C_1472) = A_1471
      | ~ v1_funct_2(C_1472,A_1471,B_1470)
      | ~ m1_subset_1(C_1472,k1_zfmisc_1(k2_zfmisc_1(A_1471,B_1470))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_5431,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_76,c_5407])).

tff(c_5450,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_4742,c_5431])).

tff(c_5451,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_4927,c_5450])).

tff(c_22,plain,(
    ! [A_12] :
      ( k1_relat_1(A_12) != k1_xboole_0
      | k1_xboole_0 = A_12
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_173,plain,
    ( k1_relat_1('#skF_6') != k1_xboole_0
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_166,c_22])).

tff(c_175,plain,(
    k1_relat_1('#skF_6') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_173])).

tff(c_5458,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5451,c_175])).

tff(c_4496,plain,(
    m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_159])).

tff(c_4741,plain,(
    k1_relset_1('#skF_5','#skF_4',k2_funct_1('#skF_6')) = k1_relat_1(k2_funct_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_4496,c_4726])).

tff(c_5975,plain,(
    ! [B_2703,C_2704,A_2705] :
      ( k1_xboole_0 = B_2703
      | v1_funct_2(C_2704,A_2705,B_2703)
      | k1_relset_1(A_2705,B_2703,C_2704) != A_2705
      | ~ m1_subset_1(C_2704,k1_zfmisc_1(k2_zfmisc_1(A_2705,B_2703))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_5993,plain,
    ( k1_xboole_0 = '#skF_4'
    | v1_funct_2(k2_funct_1('#skF_6'),'#skF_5','#skF_4')
    | k1_relset_1('#skF_5','#skF_4',k2_funct_1('#skF_6')) != '#skF_5' ),
    inference(resolution,[status(thm)],[c_4496,c_5975])).

tff(c_6006,plain,
    ( k1_xboole_0 = '#skF_4'
    | v1_funct_2(k2_funct_1('#skF_6'),'#skF_5','#skF_4')
    | k1_relat_1(k2_funct_1('#skF_6')) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4741,c_5993])).

tff(c_6007,plain,(
    k1_relat_1(k2_funct_1('#skF_6')) != '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_4495,c_5458,c_6006])).

tff(c_6014,plain,
    ( k2_relat_1('#skF_6') != '#skF_5'
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_6007])).

tff(c_6017,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_80,c_74,c_4926,c_6014])).

tff(c_6018,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_174])).

tff(c_6020,plain,(
    k1_relat_1('#skF_6') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6018,c_175])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6023,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6018,c_12])).

tff(c_62,plain,(
    ! [A_31,B_32] : m1_subset_1('#skF_3'(A_31,B_32),k1_zfmisc_1(k2_zfmisc_1(A_31,B_32))) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_6140,plain,(
    ! [C_2731,A_2732,B_2733] :
      ( v1_xboole_0(C_2731)
      | ~ m1_subset_1(C_2731,k1_zfmisc_1(k2_zfmisc_1(A_2732,B_2733)))
      | ~ v1_xboole_0(A_2732) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_6150,plain,(
    ! [A_2734,B_2735] :
      ( v1_xboole_0('#skF_3'(A_2734,B_2735))
      | ~ v1_xboole_0(A_2734) ) ),
    inference(resolution,[status(thm)],[c_62,c_6140])).

tff(c_118,plain,(
    ! [A_53,B_54] :
      ( r2_hidden('#skF_2'(A_53,B_54),A_53)
      | r1_tarski(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_122,plain,(
    ! [A_53,B_54] :
      ( ~ v1_xboole_0(A_53)
      | r1_tarski(A_53,B_54) ) ),
    inference(resolution,[status(thm)],[c_118,c_2])).

tff(c_6069,plain,(
    ! [B_2710,A_2711] :
      ( B_2710 = A_2711
      | ~ r1_tarski(B_2710,A_2711)
      | ~ r1_tarski(A_2711,B_2710) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_6079,plain,(
    ! [B_2712,A_2713] :
      ( B_2712 = A_2713
      | ~ r1_tarski(B_2712,A_2713)
      | ~ v1_xboole_0(A_2713) ) ),
    inference(resolution,[status(thm)],[c_122,c_6069])).

tff(c_6089,plain,(
    ! [B_2714,A_2715] :
      ( B_2714 = A_2715
      | ~ v1_xboole_0(B_2714)
      | ~ v1_xboole_0(A_2715) ) ),
    inference(resolution,[status(thm)],[c_122,c_6079])).

tff(c_6092,plain,(
    ! [A_2715] :
      ( A_2715 = '#skF_6'
      | ~ v1_xboole_0(A_2715) ) ),
    inference(resolution,[status(thm)],[c_6023,c_6089])).

tff(c_6158,plain,(
    ! [A_2736,B_2737] :
      ( '#skF_3'(A_2736,B_2737) = '#skF_6'
      | ~ v1_xboole_0(A_2736) ) ),
    inference(resolution,[status(thm)],[c_6150,c_6092])).

tff(c_6165,plain,(
    ! [B_2738] : '#skF_3'('#skF_6',B_2738) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_6023,c_6158])).

tff(c_52,plain,(
    ! [A_31,B_32] : v1_funct_2('#skF_3'(A_31,B_32),A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_6182,plain,(
    ! [B_2738] : v1_funct_2('#skF_6','#skF_6',B_2738) ),
    inference(superposition,[status(thm),theory(equality)],[c_6165,c_52])).

tff(c_6179,plain,(
    ! [B_2738] : m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_6',B_2738))) ),
    inference(superposition,[status(thm),theory(equality)],[c_6165,c_62])).

tff(c_6447,plain,(
    ! [A_2768,B_2769,C_2770] :
      ( k1_relset_1(A_2768,B_2769,C_2770) = k1_relat_1(C_2770)
      | ~ m1_subset_1(C_2770,k1_zfmisc_1(k2_zfmisc_1(A_2768,B_2769))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_6470,plain,(
    ! [B_2738] : k1_relset_1('#skF_6',B_2738,'#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_6179,c_6447])).

tff(c_48,plain,(
    ! [B_29,C_30] :
      ( k1_relset_1(k1_xboole_0,B_29,C_30) = k1_xboole_0
      | ~ v1_funct_2(C_30,k1_xboole_0,B_29)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_6919,plain,(
    ! [B_2802,C_2803] :
      ( k1_relset_1('#skF_6',B_2802,C_2803) = '#skF_6'
      | ~ v1_funct_2(C_2803,'#skF_6',B_2802)
      | ~ m1_subset_1(C_2803,k1_zfmisc_1(k2_zfmisc_1('#skF_6',B_2802))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6018,c_6018,c_6018,c_6018,c_48])).

tff(c_6926,plain,(
    ! [B_2738] :
      ( k1_relset_1('#skF_6',B_2738,'#skF_6') = '#skF_6'
      | ~ v1_funct_2('#skF_6','#skF_6',B_2738) ) ),
    inference(resolution,[status(thm)],[c_6179,c_6919])).

tff(c_6938,plain,(
    k1_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6182,c_6470,c_6926])).

tff(c_6940,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6020,c_6938])).

tff(c_6941,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_173])).

tff(c_6945,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6941,c_12])).

tff(c_9780,plain,(
    ! [C_3969,A_3970,B_3971] :
      ( v1_xboole_0(C_3969)
      | ~ m1_subset_1(C_3969,k1_zfmisc_1(k2_zfmisc_1(A_3970,B_3971)))
      | ~ v1_xboole_0(A_3970) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_9795,plain,(
    ! [A_3972,B_3973] :
      ( v1_xboole_0('#skF_3'(A_3972,B_3973))
      | ~ v1_xboole_0(A_3972) ) ),
    inference(resolution,[status(thm)],[c_62,c_9780])).

tff(c_6970,plain,(
    ! [B_2805,A_2806] :
      ( B_2805 = A_2806
      | ~ r1_tarski(B_2805,A_2806)
      | ~ r1_tarski(A_2806,B_2805) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_6996,plain,(
    ! [B_2808,A_2809] :
      ( B_2808 = A_2809
      | ~ r1_tarski(B_2808,A_2809)
      | ~ v1_xboole_0(A_2809) ) ),
    inference(resolution,[status(thm)],[c_122,c_6970])).

tff(c_7006,plain,(
    ! [B_2810,A_2811] :
      ( B_2810 = A_2811
      | ~ v1_xboole_0(B_2810)
      | ~ v1_xboole_0(A_2811) ) ),
    inference(resolution,[status(thm)],[c_122,c_6996])).

tff(c_7009,plain,(
    ! [A_2811] :
      ( A_2811 = '#skF_6'
      | ~ v1_xboole_0(A_2811) ) ),
    inference(resolution,[status(thm)],[c_6945,c_7006])).

tff(c_9803,plain,(
    ! [A_3974,B_3975] :
      ( '#skF_3'(A_3974,B_3975) = '#skF_6'
      | ~ v1_xboole_0(A_3974) ) ),
    inference(resolution,[status(thm)],[c_9795,c_7009])).

tff(c_9810,plain,(
    ! [B_3976] : '#skF_3'('#skF_6',B_3976) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_6945,c_9803])).

tff(c_9827,plain,(
    ! [B_3976] : v1_funct_2('#skF_6','#skF_6',B_3976) ),
    inference(superposition,[status(thm),theory(equality)],[c_9810,c_52])).

tff(c_6942,plain,(
    k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_173])).

tff(c_6950,plain,(
    k1_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6941,c_6942])).

tff(c_9653,plain,(
    ! [A_3952] :
      ( k2_relat_1(k2_funct_1(A_3952)) = k1_relat_1(A_3952)
      | ~ v2_funct_1(A_3952)
      | ~ v1_funct_1(A_3952)
      | ~ v1_relat_1(A_3952) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_7053,plain,(
    ! [C_2825,A_2826,B_2827] :
      ( v1_xboole_0(C_2825)
      | ~ m1_subset_1(C_2825,k1_zfmisc_1(k2_zfmisc_1(A_2826,B_2827)))
      | ~ v1_xboole_0(A_2826) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_7063,plain,(
    ! [A_2828,B_2829] :
      ( v1_xboole_0('#skF_3'(A_2828,B_2829))
      | ~ v1_xboole_0(A_2828) ) ),
    inference(resolution,[status(thm)],[c_62,c_7053])).

tff(c_7071,plain,(
    ! [A_2830,B_2831] :
      ( '#skF_3'(A_2830,B_2831) = '#skF_6'
      | ~ v1_xboole_0(A_2830) ) ),
    inference(resolution,[status(thm)],[c_7063,c_7009])).

tff(c_7078,plain,(
    ! [B_2832] : '#skF_3'('#skF_6',B_2832) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_6945,c_7071])).

tff(c_7089,plain,(
    ! [B_2832] : m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_6',B_2832))) ),
    inference(superposition,[status(thm),theory(equality)],[c_7078,c_62])).

tff(c_7343,plain,(
    ! [A_2870,B_2871,C_2872] :
      ( k1_relset_1(A_2870,B_2871,C_2872) = k1_relat_1(C_2872)
      | ~ m1_subset_1(C_2872,k1_zfmisc_1(k2_zfmisc_1(A_2870,B_2871))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_7358,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_76,c_7343])).

tff(c_7366,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6950,c_7358])).

tff(c_50,plain,(
    ! [B_29,A_28,C_30] :
      ( k1_xboole_0 = B_29
      | k1_relset_1(A_28,B_29,C_30) = A_28
      | ~ v1_funct_2(C_30,A_28,B_29)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_8057,plain,(
    ! [B_2913,A_2914,C_2915] :
      ( B_2913 = '#skF_6'
      | k1_relset_1(A_2914,B_2913,C_2915) = A_2914
      | ~ v1_funct_2(C_2915,A_2914,B_2913)
      | ~ m1_subset_1(C_2915,k1_zfmisc_1(k2_zfmisc_1(A_2914,B_2913))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6941,c_50])).

tff(c_8075,plain,
    ( '#skF_5' = '#skF_6'
    | k1_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_76,c_8057])).

tff(c_8088,plain,
    ( '#skF_5' = '#skF_6'
    | '#skF_6' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_7366,c_8075])).

tff(c_8089,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_8088])).

tff(c_7010,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_159])).

tff(c_8127,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8089,c_7010])).

tff(c_8134,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8089,c_166])).

tff(c_8140,plain,(
    v1_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8089,c_80])).

tff(c_8139,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8089,c_74])).

tff(c_8131,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8089,c_8089,c_6950])).

tff(c_8135,plain,(
    v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8089,c_160])).

tff(c_7396,plain,(
    ! [A_2877,B_2878,C_2879] :
      ( k2_relset_1(A_2877,B_2878,C_2879) = k2_relat_1(C_2879)
      | ~ m1_subset_1(C_2879,k1_zfmisc_1(k2_zfmisc_1(A_2877,B_2878))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_7411,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_76,c_7396])).

tff(c_7417,plain,(
    k2_relat_1('#skF_6') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_7411])).

tff(c_8110,plain,(
    k2_relat_1('#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8089,c_7417])).

tff(c_7149,plain,(
    ! [A_2839] :
      ( k1_relat_1(k2_funct_1(A_2839)) = k2_relat_1(A_2839)
      | ~ v2_funct_1(A_2839)
      | ~ v1_funct_1(A_2839)
      | ~ v1_relat_1(A_2839) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_8330,plain,(
    ! [A_2923] :
      ( v1_funct_2(k2_funct_1(A_2923),k2_relat_1(A_2923),k2_relat_1(k2_funct_1(A_2923)))
      | ~ v1_funct_1(k2_funct_1(A_2923))
      | ~ v1_relat_1(k2_funct_1(A_2923))
      | ~ v2_funct_1(A_2923)
      | ~ v1_funct_1(A_2923)
      | ~ v1_relat_1(A_2923) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7149,c_66])).

tff(c_8333,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_5',k2_relat_1(k2_funct_1('#skF_4')))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_8110,c_8330])).

tff(c_8341,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_5',k2_relat_1(k2_funct_1('#skF_4')))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8134,c_8140,c_8139,c_8135,c_8333])).

tff(c_8431,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_8341])).

tff(c_8434,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_8431])).

tff(c_8438,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8134,c_8140,c_8434])).

tff(c_8440,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_8341])).

tff(c_7264,plain,(
    ! [A_2858] :
      ( m1_subset_1(A_2858,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_2858),k2_relat_1(A_2858))))
      | ~ v1_funct_1(A_2858)
      | ~ v1_relat_1(A_2858) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_8492,plain,(
    ! [A_2933] :
      ( m1_subset_1(k2_funct_1(A_2933),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_2933),k2_relat_1(k2_funct_1(A_2933)))))
      | ~ v1_funct_1(k2_funct_1(A_2933))
      | ~ v1_relat_1(k2_funct_1(A_2933))
      | ~ v2_funct_1(A_2933)
      | ~ v1_funct_1(A_2933)
      | ~ v1_relat_1(A_2933) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_7264])).

tff(c_8507,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_5',k2_relat_1(k2_funct_1('#skF_4')))))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_8110,c_8492])).

tff(c_8519,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_5',k2_relat_1(k2_funct_1('#skF_4'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8134,c_8140,c_8139,c_8440,c_8135,c_8507])).

tff(c_8624,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_relat_1('#skF_4'))))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_8519])).

tff(c_8631,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8134,c_8140,c_8139,c_8131,c_8624])).

tff(c_8633,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8127,c_8631])).

tff(c_8634,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_8088])).

tff(c_8639,plain,(
    k2_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8634,c_7417])).

tff(c_9470,plain,(
    ! [A_3930] :
      ( v1_funct_2(k2_funct_1(A_3930),k2_relat_1(A_3930),k2_relat_1(k2_funct_1(A_3930)))
      | ~ v1_funct_1(k2_funct_1(A_3930))
      | ~ v1_relat_1(k2_funct_1(A_3930))
      | ~ v2_funct_1(A_3930)
      | ~ v1_funct_1(A_3930)
      | ~ v1_relat_1(A_3930) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7149,c_66])).

tff(c_9473,plain,
    ( v1_funct_2(k2_funct_1('#skF_6'),'#skF_6',k2_relat_1(k2_funct_1('#skF_6')))
    | ~ v1_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6'))
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_8639,c_9470])).

tff(c_9484,plain,
    ( v1_funct_2(k2_funct_1('#skF_6'),'#skF_6',k2_relat_1(k2_funct_1('#skF_6')))
    | ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_80,c_74,c_160,c_9473])).

tff(c_9487,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_9484])).

tff(c_9490,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_26,c_9487])).

tff(c_9494,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_80,c_9490])).

tff(c_9496,plain,(
    v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_9484])).

tff(c_6944,plain,(
    ! [A_12] :
      ( k2_relat_1(A_12) != '#skF_6'
      | A_12 = '#skF_6'
      | ~ v1_relat_1(A_12) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6941,c_6941,c_20])).

tff(c_9504,plain,
    ( k2_relat_1(k2_funct_1('#skF_6')) != '#skF_6'
    | k2_funct_1('#skF_6') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_9496,c_6944])).

tff(c_9510,plain,(
    k2_relat_1(k2_funct_1('#skF_6')) != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_9504])).

tff(c_9513,plain,
    ( k1_relat_1('#skF_6') != '#skF_6'
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_9510])).

tff(c_9516,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_80,c_74,c_6950,c_9513])).

tff(c_9517,plain,(
    k2_funct_1('#skF_6') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_9504])).

tff(c_8641,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8634,c_7010])).

tff(c_9522,plain,(
    ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9517,c_8641])).

tff(c_9529,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7089,c_9522])).

tff(c_9531,plain,(
    m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_159])).

tff(c_32,plain,(
    ! [C_17,A_15,B_16] :
      ( v1_relat_1(C_17)
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1(A_15,B_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_9541,plain,(
    v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_9531,c_32])).

tff(c_9549,plain,
    ( k2_relat_1(k2_funct_1('#skF_6')) != '#skF_6'
    | k2_funct_1('#skF_6') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_9541,c_6944])).

tff(c_9551,plain,(
    k2_relat_1(k2_funct_1('#skF_6')) != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_9549])).

tff(c_9662,plain,
    ( k1_relat_1('#skF_6') != '#skF_6'
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_9653,c_9551])).

tff(c_9669,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_80,c_74,c_6950,c_9662])).

tff(c_9670,plain,(
    k2_funct_1('#skF_6') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_9549])).

tff(c_6943,plain,(
    ! [A_12] :
      ( k1_relat_1(A_12) != '#skF_6'
      | A_12 = '#skF_6'
      | ~ v1_relat_1(A_12) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6941,c_6941,c_22])).

tff(c_9548,plain,
    ( k1_relat_1(k2_funct_1('#skF_6')) != '#skF_6'
    | k2_funct_1('#skF_6') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_9541,c_6943])).

tff(c_9550,plain,(
    k1_relat_1(k2_funct_1('#skF_6')) != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_9548])).

tff(c_9703,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6950,c_9670,c_9550])).

tff(c_9704,plain,(
    k2_funct_1('#skF_6') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_9548])).

tff(c_9849,plain,(
    ! [A_3977] :
      ( k2_relat_1(k2_funct_1(A_3977)) = k1_relat_1(A_3977)
      | ~ v2_funct_1(A_3977)
      | ~ v1_funct_1(A_3977)
      | ~ v1_relat_1(A_3977) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_9861,plain,
    ( k2_relat_1('#skF_6') = k1_relat_1('#skF_6')
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_9704,c_9849])).

tff(c_9865,plain,(
    k2_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_80,c_74,c_6950,c_9861])).

tff(c_10035,plain,(
    ! [A_3998,B_3999,C_4000] :
      ( k2_relset_1(A_3998,B_3999,C_4000) = k2_relat_1(C_4000)
      | ~ m1_subset_1(C_4000,k1_zfmisc_1(k2_zfmisc_1(A_3998,B_3999))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_10047,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_76,c_10035])).

tff(c_10054,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9865,c_72,c_10047])).

tff(c_9530,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_6'),'#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_159])).

tff(c_9708,plain,(
    ~ v1_funct_2('#skF_6','#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9704,c_9530])).

tff(c_10058,plain,(
    ~ v1_funct_2('#skF_6','#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10054,c_9708])).

tff(c_10066,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9827,c_10058])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n016.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 20:37:04 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.47/2.54  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.47/2.59  
% 7.47/2.59  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.47/2.59  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 7.47/2.59  
% 7.47/2.59  %Foreground sorts:
% 7.47/2.59  
% 7.47/2.59  
% 7.47/2.59  %Background operators:
% 7.47/2.59  
% 7.47/2.59  
% 7.47/2.59  %Foreground operators:
% 7.47/2.59  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 7.47/2.59  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.47/2.59  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 7.47/2.59  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 7.47/2.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.47/2.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.47/2.59  tff('#skF_1', type, '#skF_1': $i > $i).
% 7.47/2.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.47/2.59  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 7.47/2.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.47/2.59  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.47/2.59  tff('#skF_5', type, '#skF_5': $i).
% 7.47/2.59  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.47/2.59  tff('#skF_6', type, '#skF_6': $i).
% 7.47/2.59  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 7.47/2.59  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.47/2.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.47/2.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.47/2.59  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.47/2.59  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.47/2.59  tff('#skF_4', type, '#skF_4': $i).
% 7.47/2.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.47/2.59  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.47/2.59  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.47/2.59  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.47/2.59  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.47/2.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.47/2.59  
% 7.86/2.63  tff(f_148, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 7.86/2.63  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.86/2.63  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 7.86/2.63  tff(f_71, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 7.86/2.63  tff(f_61, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 7.86/2.63  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 7.86/2.63  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 7.86/2.63  tff(f_108, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 7.86/2.63  tff(f_131, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 7.86/2.63  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 7.86/2.63  tff(f_121, axiom, (![A, B]: (?[C]: (((((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & v1_relat_1(C)) & v4_relat_1(C, A)) & v5_relat_1(C, B)) & v1_funct_1(C)) & v1_funct_2(C, A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_funct_2)).
% 7.86/2.63  tff(f_82, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc3_relset_1)).
% 7.86/2.63  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 7.86/2.63  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 7.86/2.63  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.86/2.63  tff(c_76, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_148])).
% 7.86/2.63  tff(c_162, plain, (![C_66, A_67, B_68]: (v1_relat_1(C_66) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 7.86/2.63  tff(c_166, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_76, c_162])).
% 7.86/2.63  tff(c_80, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_148])).
% 7.86/2.63  tff(c_74, plain, (v2_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_148])).
% 7.86/2.63  tff(c_72, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_5'), inference(cnfTransformation, [status(thm)], [f_148])).
% 7.86/2.63  tff(c_4901, plain, (![A_1439, B_1440, C_1441]: (k2_relset_1(A_1439, B_1440, C_1441)=k2_relat_1(C_1441) | ~m1_subset_1(C_1441, k1_zfmisc_1(k2_zfmisc_1(A_1439, B_1440))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 7.86/2.63  tff(c_4919, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_76, c_4901])).
% 7.86/2.63  tff(c_4926, plain, (k2_relat_1('#skF_6')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_4919])).
% 7.86/2.63  tff(c_30, plain, (![A_14]: (k1_relat_1(k2_funct_1(A_14))=k2_relat_1(A_14) | ~v2_funct_1(A_14) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.86/2.63  tff(c_24, plain, (![A_13]: (v1_funct_1(k2_funct_1(A_13)) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.86/2.63  tff(c_70, plain, (~m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4'))) | ~v1_funct_2(k2_funct_1('#skF_6'), '#skF_5', '#skF_4') | ~v1_funct_1(k2_funct_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_148])).
% 7.86/2.63  tff(c_123, plain, (~v1_funct_1(k2_funct_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_70])).
% 7.86/2.63  tff(c_126, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_24, c_123])).
% 7.86/2.63  tff(c_129, plain, (~v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_126])).
% 7.86/2.63  tff(c_151, plain, (![C_61, A_62, B_63]: (v1_relat_1(C_61) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 7.86/2.63  tff(c_154, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_76, c_151])).
% 7.86/2.63  tff(c_158, plain, $false, inference(negUnitSimplification, [status(thm)], [c_129, c_154])).
% 7.86/2.63  tff(c_159, plain, (~v1_funct_2(k2_funct_1('#skF_6'), '#skF_5', '#skF_4') | ~m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4')))), inference(splitRight, [status(thm)], [c_70])).
% 7.86/2.63  tff(c_214, plain, (~m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4')))), inference(splitLeft, [status(thm)], [c_159])).
% 7.86/2.63  tff(c_426, plain, (![A_114, B_115, C_116]: (k2_relset_1(A_114, B_115, C_116)=k2_relat_1(C_116) | ~m1_subset_1(C_116, k1_zfmisc_1(k2_zfmisc_1(A_114, B_115))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 7.86/2.63  tff(c_435, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_76, c_426])).
% 7.86/2.63  tff(c_439, plain, (k2_relat_1('#skF_6')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_435])).
% 7.86/2.63  tff(c_26, plain, (![A_13]: (v1_relat_1(k2_funct_1(A_13)) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.86/2.63  tff(c_160, plain, (v1_funct_1(k2_funct_1('#skF_6'))), inference(splitRight, [status(thm)], [c_70])).
% 7.86/2.63  tff(c_20, plain, (![A_12]: (k2_relat_1(A_12)!=k1_xboole_0 | k1_xboole_0=A_12 | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.86/2.63  tff(c_174, plain, (k2_relat_1('#skF_6')!=k1_xboole_0 | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_166, c_20])).
% 7.86/2.63  tff(c_176, plain, (k2_relat_1('#skF_6')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_174])).
% 7.86/2.63  tff(c_440, plain, (k1_xboole_0!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_439, c_176])).
% 7.86/2.63  tff(c_78, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_148])).
% 7.86/2.63  tff(c_537, plain, (![A_125, B_126, C_127]: (k1_relset_1(A_125, B_126, C_127)=k1_relat_1(C_127) | ~m1_subset_1(C_127, k1_zfmisc_1(k2_zfmisc_1(A_125, B_126))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.86/2.63  tff(c_557, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_76, c_537])).
% 7.86/2.63  tff(c_1047, plain, (![B_164, A_165, C_166]: (k1_xboole_0=B_164 | k1_relset_1(A_165, B_164, C_166)=A_165 | ~v1_funct_2(C_166, A_165, B_164) | ~m1_subset_1(C_166, k1_zfmisc_1(k2_zfmisc_1(A_165, B_164))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 7.86/2.63  tff(c_1068, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_76, c_1047])).
% 7.86/2.63  tff(c_1085, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_557, c_1068])).
% 7.86/2.63  tff(c_1086, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_440, c_1085])).
% 7.86/2.63  tff(c_328, plain, (![A_100]: (k2_relat_1(k2_funct_1(A_100))=k1_relat_1(A_100) | ~v2_funct_1(A_100) | ~v1_funct_1(A_100) | ~v1_relat_1(A_100))), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.86/2.63  tff(c_66, plain, (![A_34]: (v1_funct_2(A_34, k1_relat_1(A_34), k2_relat_1(A_34)) | ~v1_funct_1(A_34) | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_131])).
% 7.86/2.63  tff(c_2916, plain, (![A_1338]: (v1_funct_2(k2_funct_1(A_1338), k1_relat_1(k2_funct_1(A_1338)), k1_relat_1(A_1338)) | ~v1_funct_1(k2_funct_1(A_1338)) | ~v1_relat_1(k2_funct_1(A_1338)) | ~v2_funct_1(A_1338) | ~v1_funct_1(A_1338) | ~v1_relat_1(A_1338))), inference(superposition, [status(thm), theory('equality')], [c_328, c_66])).
% 7.86/2.63  tff(c_2925, plain, (v1_funct_2(k2_funct_1('#skF_6'), k1_relat_1(k2_funct_1('#skF_6')), '#skF_4') | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')) | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1086, c_2916])).
% 7.86/2.63  tff(c_2943, plain, (v1_funct_2(k2_funct_1('#skF_6'), k1_relat_1(k2_funct_1('#skF_6')), '#skF_4') | ~v1_relat_1(k2_funct_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_166, c_80, c_74, c_160, c_2925])).
% 7.86/2.63  tff(c_2948, plain, (~v1_relat_1(k2_funct_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_2943])).
% 7.86/2.63  tff(c_2951, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_26, c_2948])).
% 7.86/2.63  tff(c_2955, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_166, c_80, c_2951])).
% 7.86/2.63  tff(c_2957, plain, (v1_relat_1(k2_funct_1('#skF_6'))), inference(splitRight, [status(thm)], [c_2943])).
% 7.86/2.63  tff(c_28, plain, (![A_14]: (k2_relat_1(k2_funct_1(A_14))=k1_relat_1(A_14) | ~v2_funct_1(A_14) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.86/2.63  tff(c_450, plain, (![A_117]: (m1_subset_1(A_117, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_117), k2_relat_1(A_117)))) | ~v1_funct_1(A_117) | ~v1_relat_1(A_117))), inference(cnfTransformation, [status(thm)], [f_131])).
% 7.86/2.63  tff(c_4402, plain, (![A_1376]: (m1_subset_1(k2_funct_1(A_1376), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_1376)), k1_relat_1(A_1376)))) | ~v1_funct_1(k2_funct_1(A_1376)) | ~v1_relat_1(k2_funct_1(A_1376)) | ~v2_funct_1(A_1376) | ~v1_funct_1(A_1376) | ~v1_relat_1(A_1376))), inference(superposition, [status(thm), theory('equality')], [c_28, c_450])).
% 7.86/2.63  tff(c_4429, plain, (m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_6')), '#skF_4'))) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')) | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1086, c_4402])).
% 7.86/2.63  tff(c_4453, plain, (m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_6')), '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_166, c_80, c_74, c_2957, c_160, c_4429])).
% 7.86/2.63  tff(c_4478, plain, (m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_6'), '#skF_4'))) | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_30, c_4453])).
% 7.86/2.63  tff(c_4492, plain, (m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_166, c_80, c_74, c_439, c_4478])).
% 7.86/2.63  tff(c_4494, plain, $false, inference(negUnitSimplification, [status(thm)], [c_214, c_4492])).
% 7.86/2.63  tff(c_4495, plain, (~v1_funct_2(k2_funct_1('#skF_6'), '#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_159])).
% 7.86/2.63  tff(c_4927, plain, (k1_xboole_0!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_4926, c_176])).
% 7.86/2.63  tff(c_4726, plain, (![A_1410, B_1411, C_1412]: (k1_relset_1(A_1410, B_1411, C_1412)=k1_relat_1(C_1412) | ~m1_subset_1(C_1412, k1_zfmisc_1(k2_zfmisc_1(A_1410, B_1411))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.86/2.63  tff(c_4742, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_76, c_4726])).
% 7.86/2.63  tff(c_5407, plain, (![B_1470, A_1471, C_1472]: (k1_xboole_0=B_1470 | k1_relset_1(A_1471, B_1470, C_1472)=A_1471 | ~v1_funct_2(C_1472, A_1471, B_1470) | ~m1_subset_1(C_1472, k1_zfmisc_1(k2_zfmisc_1(A_1471, B_1470))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 7.86/2.63  tff(c_5431, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_76, c_5407])).
% 7.86/2.63  tff(c_5450, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_4742, c_5431])).
% 7.86/2.63  tff(c_5451, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_4927, c_5450])).
% 7.86/2.63  tff(c_22, plain, (![A_12]: (k1_relat_1(A_12)!=k1_xboole_0 | k1_xboole_0=A_12 | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.86/2.63  tff(c_173, plain, (k1_relat_1('#skF_6')!=k1_xboole_0 | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_166, c_22])).
% 7.86/2.63  tff(c_175, plain, (k1_relat_1('#skF_6')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_173])).
% 7.86/2.63  tff(c_5458, plain, (k1_xboole_0!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5451, c_175])).
% 7.86/2.63  tff(c_4496, plain, (m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4')))), inference(splitRight, [status(thm)], [c_159])).
% 7.86/2.63  tff(c_4741, plain, (k1_relset_1('#skF_5', '#skF_4', k2_funct_1('#skF_6'))=k1_relat_1(k2_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_4496, c_4726])).
% 7.86/2.63  tff(c_5975, plain, (![B_2703, C_2704, A_2705]: (k1_xboole_0=B_2703 | v1_funct_2(C_2704, A_2705, B_2703) | k1_relset_1(A_2705, B_2703, C_2704)!=A_2705 | ~m1_subset_1(C_2704, k1_zfmisc_1(k2_zfmisc_1(A_2705, B_2703))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 7.86/2.63  tff(c_5993, plain, (k1_xboole_0='#skF_4' | v1_funct_2(k2_funct_1('#skF_6'), '#skF_5', '#skF_4') | k1_relset_1('#skF_5', '#skF_4', k2_funct_1('#skF_6'))!='#skF_5'), inference(resolution, [status(thm)], [c_4496, c_5975])).
% 7.86/2.63  tff(c_6006, plain, (k1_xboole_0='#skF_4' | v1_funct_2(k2_funct_1('#skF_6'), '#skF_5', '#skF_4') | k1_relat_1(k2_funct_1('#skF_6'))!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_4741, c_5993])).
% 7.86/2.63  tff(c_6007, plain, (k1_relat_1(k2_funct_1('#skF_6'))!='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_4495, c_5458, c_6006])).
% 7.86/2.63  tff(c_6014, plain, (k2_relat_1('#skF_6')!='#skF_5' | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_30, c_6007])).
% 7.86/2.63  tff(c_6017, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_166, c_80, c_74, c_4926, c_6014])).
% 7.86/2.63  tff(c_6018, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_174])).
% 7.86/2.63  tff(c_6020, plain, (k1_relat_1('#skF_6')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_6018, c_175])).
% 7.86/2.63  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.86/2.63  tff(c_6023, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_6018, c_12])).
% 7.86/2.63  tff(c_62, plain, (![A_31, B_32]: (m1_subset_1('#skF_3'(A_31, B_32), k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 7.86/2.63  tff(c_6140, plain, (![C_2731, A_2732, B_2733]: (v1_xboole_0(C_2731) | ~m1_subset_1(C_2731, k1_zfmisc_1(k2_zfmisc_1(A_2732, B_2733))) | ~v1_xboole_0(A_2732))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.86/2.63  tff(c_6150, plain, (![A_2734, B_2735]: (v1_xboole_0('#skF_3'(A_2734, B_2735)) | ~v1_xboole_0(A_2734))), inference(resolution, [status(thm)], [c_62, c_6140])).
% 7.86/2.63  tff(c_118, plain, (![A_53, B_54]: (r2_hidden('#skF_2'(A_53, B_54), A_53) | r1_tarski(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.86/2.63  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.86/2.63  tff(c_122, plain, (![A_53, B_54]: (~v1_xboole_0(A_53) | r1_tarski(A_53, B_54))), inference(resolution, [status(thm)], [c_118, c_2])).
% 7.86/2.63  tff(c_6069, plain, (![B_2710, A_2711]: (B_2710=A_2711 | ~r1_tarski(B_2710, A_2711) | ~r1_tarski(A_2711, B_2710))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.86/2.63  tff(c_6079, plain, (![B_2712, A_2713]: (B_2712=A_2713 | ~r1_tarski(B_2712, A_2713) | ~v1_xboole_0(A_2713))), inference(resolution, [status(thm)], [c_122, c_6069])).
% 7.86/2.63  tff(c_6089, plain, (![B_2714, A_2715]: (B_2714=A_2715 | ~v1_xboole_0(B_2714) | ~v1_xboole_0(A_2715))), inference(resolution, [status(thm)], [c_122, c_6079])).
% 7.86/2.63  tff(c_6092, plain, (![A_2715]: (A_2715='#skF_6' | ~v1_xboole_0(A_2715))), inference(resolution, [status(thm)], [c_6023, c_6089])).
% 7.86/2.63  tff(c_6158, plain, (![A_2736, B_2737]: ('#skF_3'(A_2736, B_2737)='#skF_6' | ~v1_xboole_0(A_2736))), inference(resolution, [status(thm)], [c_6150, c_6092])).
% 7.86/2.63  tff(c_6165, plain, (![B_2738]: ('#skF_3'('#skF_6', B_2738)='#skF_6')), inference(resolution, [status(thm)], [c_6023, c_6158])).
% 7.86/2.63  tff(c_52, plain, (![A_31, B_32]: (v1_funct_2('#skF_3'(A_31, B_32), A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_121])).
% 7.86/2.63  tff(c_6182, plain, (![B_2738]: (v1_funct_2('#skF_6', '#skF_6', B_2738))), inference(superposition, [status(thm), theory('equality')], [c_6165, c_52])).
% 7.86/2.63  tff(c_6179, plain, (![B_2738]: (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_6', B_2738))))), inference(superposition, [status(thm), theory('equality')], [c_6165, c_62])).
% 7.86/2.63  tff(c_6447, plain, (![A_2768, B_2769, C_2770]: (k1_relset_1(A_2768, B_2769, C_2770)=k1_relat_1(C_2770) | ~m1_subset_1(C_2770, k1_zfmisc_1(k2_zfmisc_1(A_2768, B_2769))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.86/2.63  tff(c_6470, plain, (![B_2738]: (k1_relset_1('#skF_6', B_2738, '#skF_6')=k1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_6179, c_6447])).
% 7.86/2.63  tff(c_48, plain, (![B_29, C_30]: (k1_relset_1(k1_xboole_0, B_29, C_30)=k1_xboole_0 | ~v1_funct_2(C_30, k1_xboole_0, B_29) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_29))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 7.86/2.63  tff(c_6919, plain, (![B_2802, C_2803]: (k1_relset_1('#skF_6', B_2802, C_2803)='#skF_6' | ~v1_funct_2(C_2803, '#skF_6', B_2802) | ~m1_subset_1(C_2803, k1_zfmisc_1(k2_zfmisc_1('#skF_6', B_2802))))), inference(demodulation, [status(thm), theory('equality')], [c_6018, c_6018, c_6018, c_6018, c_48])).
% 7.86/2.63  tff(c_6926, plain, (![B_2738]: (k1_relset_1('#skF_6', B_2738, '#skF_6')='#skF_6' | ~v1_funct_2('#skF_6', '#skF_6', B_2738))), inference(resolution, [status(thm)], [c_6179, c_6919])).
% 7.86/2.63  tff(c_6938, plain, (k1_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_6182, c_6470, c_6926])).
% 7.86/2.63  tff(c_6940, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6020, c_6938])).
% 7.86/2.63  tff(c_6941, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_173])).
% 7.86/2.63  tff(c_6945, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_6941, c_12])).
% 7.86/2.63  tff(c_9780, plain, (![C_3969, A_3970, B_3971]: (v1_xboole_0(C_3969) | ~m1_subset_1(C_3969, k1_zfmisc_1(k2_zfmisc_1(A_3970, B_3971))) | ~v1_xboole_0(A_3970))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.86/2.63  tff(c_9795, plain, (![A_3972, B_3973]: (v1_xboole_0('#skF_3'(A_3972, B_3973)) | ~v1_xboole_0(A_3972))), inference(resolution, [status(thm)], [c_62, c_9780])).
% 7.86/2.63  tff(c_6970, plain, (![B_2805, A_2806]: (B_2805=A_2806 | ~r1_tarski(B_2805, A_2806) | ~r1_tarski(A_2806, B_2805))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.86/2.63  tff(c_6996, plain, (![B_2808, A_2809]: (B_2808=A_2809 | ~r1_tarski(B_2808, A_2809) | ~v1_xboole_0(A_2809))), inference(resolution, [status(thm)], [c_122, c_6970])).
% 7.86/2.63  tff(c_7006, plain, (![B_2810, A_2811]: (B_2810=A_2811 | ~v1_xboole_0(B_2810) | ~v1_xboole_0(A_2811))), inference(resolution, [status(thm)], [c_122, c_6996])).
% 7.86/2.63  tff(c_7009, plain, (![A_2811]: (A_2811='#skF_6' | ~v1_xboole_0(A_2811))), inference(resolution, [status(thm)], [c_6945, c_7006])).
% 7.86/2.63  tff(c_9803, plain, (![A_3974, B_3975]: ('#skF_3'(A_3974, B_3975)='#skF_6' | ~v1_xboole_0(A_3974))), inference(resolution, [status(thm)], [c_9795, c_7009])).
% 7.86/2.63  tff(c_9810, plain, (![B_3976]: ('#skF_3'('#skF_6', B_3976)='#skF_6')), inference(resolution, [status(thm)], [c_6945, c_9803])).
% 7.86/2.63  tff(c_9827, plain, (![B_3976]: (v1_funct_2('#skF_6', '#skF_6', B_3976))), inference(superposition, [status(thm), theory('equality')], [c_9810, c_52])).
% 7.86/2.63  tff(c_6942, plain, (k1_relat_1('#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_173])).
% 7.86/2.63  tff(c_6950, plain, (k1_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_6941, c_6942])).
% 7.86/2.63  tff(c_9653, plain, (![A_3952]: (k2_relat_1(k2_funct_1(A_3952))=k1_relat_1(A_3952) | ~v2_funct_1(A_3952) | ~v1_funct_1(A_3952) | ~v1_relat_1(A_3952))), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.86/2.63  tff(c_7053, plain, (![C_2825, A_2826, B_2827]: (v1_xboole_0(C_2825) | ~m1_subset_1(C_2825, k1_zfmisc_1(k2_zfmisc_1(A_2826, B_2827))) | ~v1_xboole_0(A_2826))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.86/2.63  tff(c_7063, plain, (![A_2828, B_2829]: (v1_xboole_0('#skF_3'(A_2828, B_2829)) | ~v1_xboole_0(A_2828))), inference(resolution, [status(thm)], [c_62, c_7053])).
% 7.86/2.63  tff(c_7071, plain, (![A_2830, B_2831]: ('#skF_3'(A_2830, B_2831)='#skF_6' | ~v1_xboole_0(A_2830))), inference(resolution, [status(thm)], [c_7063, c_7009])).
% 7.86/2.63  tff(c_7078, plain, (![B_2832]: ('#skF_3'('#skF_6', B_2832)='#skF_6')), inference(resolution, [status(thm)], [c_6945, c_7071])).
% 7.86/2.63  tff(c_7089, plain, (![B_2832]: (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_6', B_2832))))), inference(superposition, [status(thm), theory('equality')], [c_7078, c_62])).
% 7.86/2.63  tff(c_7343, plain, (![A_2870, B_2871, C_2872]: (k1_relset_1(A_2870, B_2871, C_2872)=k1_relat_1(C_2872) | ~m1_subset_1(C_2872, k1_zfmisc_1(k2_zfmisc_1(A_2870, B_2871))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.86/2.63  tff(c_7358, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_76, c_7343])).
% 7.86/2.63  tff(c_7366, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_6950, c_7358])).
% 7.86/2.63  tff(c_50, plain, (![B_29, A_28, C_30]: (k1_xboole_0=B_29 | k1_relset_1(A_28, B_29, C_30)=A_28 | ~v1_funct_2(C_30, A_28, B_29) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 7.86/2.63  tff(c_8057, plain, (![B_2913, A_2914, C_2915]: (B_2913='#skF_6' | k1_relset_1(A_2914, B_2913, C_2915)=A_2914 | ~v1_funct_2(C_2915, A_2914, B_2913) | ~m1_subset_1(C_2915, k1_zfmisc_1(k2_zfmisc_1(A_2914, B_2913))))), inference(demodulation, [status(thm), theory('equality')], [c_6941, c_50])).
% 7.86/2.63  tff(c_8075, plain, ('#skF_5'='#skF_6' | k1_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_76, c_8057])).
% 7.86/2.63  tff(c_8088, plain, ('#skF_5'='#skF_6' | '#skF_6'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_7366, c_8075])).
% 7.86/2.63  tff(c_8089, plain, ('#skF_6'='#skF_4'), inference(splitLeft, [status(thm)], [c_8088])).
% 7.86/2.63  tff(c_7010, plain, (~m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4')))), inference(splitLeft, [status(thm)], [c_159])).
% 7.86/2.63  tff(c_8127, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_8089, c_7010])).
% 7.86/2.63  tff(c_8134, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8089, c_166])).
% 7.86/2.63  tff(c_8140, plain, (v1_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8089, c_80])).
% 7.86/2.63  tff(c_8139, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8089, c_74])).
% 7.86/2.63  tff(c_8131, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_8089, c_8089, c_6950])).
% 7.86/2.63  tff(c_8135, plain, (v1_funct_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_8089, c_160])).
% 7.86/2.63  tff(c_7396, plain, (![A_2877, B_2878, C_2879]: (k2_relset_1(A_2877, B_2878, C_2879)=k2_relat_1(C_2879) | ~m1_subset_1(C_2879, k1_zfmisc_1(k2_zfmisc_1(A_2877, B_2878))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 7.86/2.63  tff(c_7411, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_76, c_7396])).
% 7.86/2.63  tff(c_7417, plain, (k2_relat_1('#skF_6')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_7411])).
% 7.86/2.63  tff(c_8110, plain, (k2_relat_1('#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_8089, c_7417])).
% 7.86/2.63  tff(c_7149, plain, (![A_2839]: (k1_relat_1(k2_funct_1(A_2839))=k2_relat_1(A_2839) | ~v2_funct_1(A_2839) | ~v1_funct_1(A_2839) | ~v1_relat_1(A_2839))), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.86/2.63  tff(c_8330, plain, (![A_2923]: (v1_funct_2(k2_funct_1(A_2923), k2_relat_1(A_2923), k2_relat_1(k2_funct_1(A_2923))) | ~v1_funct_1(k2_funct_1(A_2923)) | ~v1_relat_1(k2_funct_1(A_2923)) | ~v2_funct_1(A_2923) | ~v1_funct_1(A_2923) | ~v1_relat_1(A_2923))), inference(superposition, [status(thm), theory('equality')], [c_7149, c_66])).
% 7.86/2.63  tff(c_8333, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_5', k2_relat_1(k2_funct_1('#skF_4'))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_8110, c_8330])).
% 7.86/2.63  tff(c_8341, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_5', k2_relat_1(k2_funct_1('#skF_4'))) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_8134, c_8140, c_8139, c_8135, c_8333])).
% 7.86/2.63  tff(c_8431, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_8341])).
% 7.86/2.63  tff(c_8434, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_26, c_8431])).
% 7.86/2.63  tff(c_8438, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8134, c_8140, c_8434])).
% 7.86/2.63  tff(c_8440, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_8341])).
% 7.86/2.63  tff(c_7264, plain, (![A_2858]: (m1_subset_1(A_2858, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_2858), k2_relat_1(A_2858)))) | ~v1_funct_1(A_2858) | ~v1_relat_1(A_2858))), inference(cnfTransformation, [status(thm)], [f_131])).
% 7.86/2.63  tff(c_8492, plain, (![A_2933]: (m1_subset_1(k2_funct_1(A_2933), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_2933), k2_relat_1(k2_funct_1(A_2933))))) | ~v1_funct_1(k2_funct_1(A_2933)) | ~v1_relat_1(k2_funct_1(A_2933)) | ~v2_funct_1(A_2933) | ~v1_funct_1(A_2933) | ~v1_relat_1(A_2933))), inference(superposition, [status(thm), theory('equality')], [c_30, c_7264])).
% 7.86/2.63  tff(c_8507, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', k2_relat_1(k2_funct_1('#skF_4'))))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_8110, c_8492])).
% 7.86/2.63  tff(c_8519, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', k2_relat_1(k2_funct_1('#skF_4')))))), inference(demodulation, [status(thm), theory('equality')], [c_8134, c_8140, c_8139, c_8440, c_8135, c_8507])).
% 7.86/2.63  tff(c_8624, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_relat_1('#skF_4')))) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_28, c_8519])).
% 7.86/2.63  tff(c_8631, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_8134, c_8140, c_8139, c_8131, c_8624])).
% 7.86/2.63  tff(c_8633, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8127, c_8631])).
% 7.86/2.63  tff(c_8634, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_8088])).
% 7.86/2.63  tff(c_8639, plain, (k2_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_8634, c_7417])).
% 7.86/2.63  tff(c_9470, plain, (![A_3930]: (v1_funct_2(k2_funct_1(A_3930), k2_relat_1(A_3930), k2_relat_1(k2_funct_1(A_3930))) | ~v1_funct_1(k2_funct_1(A_3930)) | ~v1_relat_1(k2_funct_1(A_3930)) | ~v2_funct_1(A_3930) | ~v1_funct_1(A_3930) | ~v1_relat_1(A_3930))), inference(superposition, [status(thm), theory('equality')], [c_7149, c_66])).
% 7.86/2.63  tff(c_9473, plain, (v1_funct_2(k2_funct_1('#skF_6'), '#skF_6', k2_relat_1(k2_funct_1('#skF_6'))) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')) | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_8639, c_9470])).
% 7.86/2.63  tff(c_9484, plain, (v1_funct_2(k2_funct_1('#skF_6'), '#skF_6', k2_relat_1(k2_funct_1('#skF_6'))) | ~v1_relat_1(k2_funct_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_166, c_80, c_74, c_160, c_9473])).
% 7.86/2.63  tff(c_9487, plain, (~v1_relat_1(k2_funct_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_9484])).
% 7.86/2.63  tff(c_9490, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_26, c_9487])).
% 7.86/2.63  tff(c_9494, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_166, c_80, c_9490])).
% 7.86/2.63  tff(c_9496, plain, (v1_relat_1(k2_funct_1('#skF_6'))), inference(splitRight, [status(thm)], [c_9484])).
% 7.86/2.63  tff(c_6944, plain, (![A_12]: (k2_relat_1(A_12)!='#skF_6' | A_12='#skF_6' | ~v1_relat_1(A_12))), inference(demodulation, [status(thm), theory('equality')], [c_6941, c_6941, c_20])).
% 7.86/2.63  tff(c_9504, plain, (k2_relat_1(k2_funct_1('#skF_6'))!='#skF_6' | k2_funct_1('#skF_6')='#skF_6'), inference(resolution, [status(thm)], [c_9496, c_6944])).
% 7.86/2.63  tff(c_9510, plain, (k2_relat_1(k2_funct_1('#skF_6'))!='#skF_6'), inference(splitLeft, [status(thm)], [c_9504])).
% 7.86/2.63  tff(c_9513, plain, (k1_relat_1('#skF_6')!='#skF_6' | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_28, c_9510])).
% 7.86/2.63  tff(c_9516, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_166, c_80, c_74, c_6950, c_9513])).
% 7.86/2.63  tff(c_9517, plain, (k2_funct_1('#skF_6')='#skF_6'), inference(splitRight, [status(thm)], [c_9504])).
% 7.86/2.63  tff(c_8641, plain, (~m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_8634, c_7010])).
% 7.86/2.63  tff(c_9522, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_9517, c_8641])).
% 7.86/2.63  tff(c_9529, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7089, c_9522])).
% 7.86/2.63  tff(c_9531, plain, (m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4')))), inference(splitRight, [status(thm)], [c_159])).
% 7.86/2.63  tff(c_32, plain, (![C_17, A_15, B_16]: (v1_relat_1(C_17) | ~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1(A_15, B_16))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 7.86/2.63  tff(c_9541, plain, (v1_relat_1(k2_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_9531, c_32])).
% 7.86/2.63  tff(c_9549, plain, (k2_relat_1(k2_funct_1('#skF_6'))!='#skF_6' | k2_funct_1('#skF_6')='#skF_6'), inference(resolution, [status(thm)], [c_9541, c_6944])).
% 7.86/2.63  tff(c_9551, plain, (k2_relat_1(k2_funct_1('#skF_6'))!='#skF_6'), inference(splitLeft, [status(thm)], [c_9549])).
% 7.86/2.63  tff(c_9662, plain, (k1_relat_1('#skF_6')!='#skF_6' | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_9653, c_9551])).
% 7.86/2.63  tff(c_9669, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_166, c_80, c_74, c_6950, c_9662])).
% 7.86/2.63  tff(c_9670, plain, (k2_funct_1('#skF_6')='#skF_6'), inference(splitRight, [status(thm)], [c_9549])).
% 7.86/2.63  tff(c_6943, plain, (![A_12]: (k1_relat_1(A_12)!='#skF_6' | A_12='#skF_6' | ~v1_relat_1(A_12))), inference(demodulation, [status(thm), theory('equality')], [c_6941, c_6941, c_22])).
% 7.86/2.63  tff(c_9548, plain, (k1_relat_1(k2_funct_1('#skF_6'))!='#skF_6' | k2_funct_1('#skF_6')='#skF_6'), inference(resolution, [status(thm)], [c_9541, c_6943])).
% 7.86/2.63  tff(c_9550, plain, (k1_relat_1(k2_funct_1('#skF_6'))!='#skF_6'), inference(splitLeft, [status(thm)], [c_9548])).
% 7.86/2.63  tff(c_9703, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6950, c_9670, c_9550])).
% 7.86/2.63  tff(c_9704, plain, (k2_funct_1('#skF_6')='#skF_6'), inference(splitRight, [status(thm)], [c_9548])).
% 7.86/2.63  tff(c_9849, plain, (![A_3977]: (k2_relat_1(k2_funct_1(A_3977))=k1_relat_1(A_3977) | ~v2_funct_1(A_3977) | ~v1_funct_1(A_3977) | ~v1_relat_1(A_3977))), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.86/2.63  tff(c_9861, plain, (k2_relat_1('#skF_6')=k1_relat_1('#skF_6') | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_9704, c_9849])).
% 7.86/2.63  tff(c_9865, plain, (k2_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_166, c_80, c_74, c_6950, c_9861])).
% 7.86/2.63  tff(c_10035, plain, (![A_3998, B_3999, C_4000]: (k2_relset_1(A_3998, B_3999, C_4000)=k2_relat_1(C_4000) | ~m1_subset_1(C_4000, k1_zfmisc_1(k2_zfmisc_1(A_3998, B_3999))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 7.86/2.63  tff(c_10047, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_76, c_10035])).
% 7.86/2.63  tff(c_10054, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_9865, c_72, c_10047])).
% 7.86/2.63  tff(c_9530, plain, (~v1_funct_2(k2_funct_1('#skF_6'), '#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_159])).
% 7.86/2.63  tff(c_9708, plain, (~v1_funct_2('#skF_6', '#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9704, c_9530])).
% 7.86/2.63  tff(c_10058, plain, (~v1_funct_2('#skF_6', '#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10054, c_9708])).
% 7.86/2.63  tff(c_10066, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9827, c_10058])).
% 7.86/2.63  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.86/2.63  
% 7.86/2.63  Inference rules
% 7.86/2.63  ----------------------
% 7.86/2.63  #Ref     : 0
% 7.86/2.63  #Sup     : 2463
% 7.86/2.63  #Fact    : 0
% 7.86/2.63  #Define  : 0
% 7.86/2.63  #Split   : 29
% 7.86/2.63  #Chain   : 0
% 7.86/2.63  #Close   : 0
% 7.86/2.63  
% 7.86/2.63  Ordering : KBO
% 7.86/2.63  
% 7.86/2.63  Simplification rules
% 7.86/2.63  ----------------------
% 7.86/2.63  #Subsume      : 726
% 7.86/2.63  #Demod        : 1463
% 7.86/2.63  #Tautology    : 953
% 7.86/2.63  #SimpNegUnit  : 38
% 7.86/2.63  #BackRed      : 117
% 7.86/2.63  
% 7.86/2.63  #Partial instantiations: 462
% 7.86/2.63  #Strategies tried      : 1
% 7.86/2.63  
% 7.86/2.63  Timing (in seconds)
% 7.86/2.63  ----------------------
% 7.86/2.63  Preprocessing        : 0.33
% 7.86/2.63  Parsing              : 0.17
% 7.86/2.63  CNF conversion       : 0.02
% 7.86/2.63  Main loop            : 1.46
% 7.86/2.63  Inferencing          : 0.55
% 7.86/2.63  Reduction            : 0.48
% 7.86/2.63  Demodulation         : 0.34
% 7.86/2.63  BG Simplification    : 0.05
% 7.86/2.63  Subsumption          : 0.28
% 7.86/2.63  Abstraction          : 0.06
% 7.86/2.63  MUC search           : 0.00
% 7.86/2.63  Cooper               : 0.00
% 7.86/2.63  Total                : 1.89
% 7.86/2.63  Index Insertion      : 0.00
% 7.86/2.64  Index Deletion       : 0.00
% 7.86/2.64  Index Matching       : 0.00
% 7.86/2.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
