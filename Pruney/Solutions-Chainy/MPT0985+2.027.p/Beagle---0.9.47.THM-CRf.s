%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:29 EST 2020

% Result     : Theorem 8.38s
% Output     : CNFRefutation 8.38s
% Verified   : 
% Statistics : Number of formulae       :  357 (11016 expanded)
%              Number of leaves         :   42 (3548 expanded)
%              Depth                    :   22
%              Number of atoms          :  636 (26582 expanded)
%              Number of equality atoms :  187 (5504 expanded)
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

tff(f_45,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_147,negated_conjecture,(
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

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_77,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_67,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_107,axiom,(
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

tff(f_130,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_120,axiom,(
    ! [A,B] :
    ? [C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
      & v1_relat_1(C)
      & v4_relat_1(C,A)
      & v5_relat_1(C,B)
      & v1_funct_1(C)
      & v1_funct_2(C,A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_funct_2)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_18,plain,(
    ! [B_11] : r1_tarski(B_11,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_82,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_211,plain,(
    ! [C_71,A_72,B_73] :
      ( v1_relat_1(C_71)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_229,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_82,c_211])).

tff(c_86,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_80,plain,(
    v2_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_78,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_10517,plain,(
    ! [A_3094,B_3095,C_3096] :
      ( k2_relset_1(A_3094,B_3095,C_3096) = k2_relat_1(C_3096)
      | ~ m1_subset_1(C_3096,k1_zfmisc_1(k2_zfmisc_1(A_3094,B_3095))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_10533,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_82,c_10517])).

tff(c_10545,plain,(
    k2_relat_1('#skF_6') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_10533])).

tff(c_38,plain,(
    ! [A_18] :
      ( k1_relat_1(k2_funct_1(A_18)) = k2_relat_1(A_18)
      | ~ v2_funct_1(A_18)
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_32,plain,(
    ! [A_17] :
      ( v1_funct_1(k2_funct_1(A_17))
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_76,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4')))
    | ~ v1_funct_2(k2_funct_1('#skF_6'),'#skF_5','#skF_4')
    | ~ v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_136,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_139,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_32,c_136])).

tff(c_142,plain,(
    ~ v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_139])).

tff(c_154,plain,(
    ! [C_58,A_59,B_60] :
      ( v1_relat_1(C_58)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_161,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_82,c_154])).

tff(c_170,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_161])).

tff(c_171,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_6'),'#skF_5','#skF_4')
    | ~ m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_236,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_171])).

tff(c_84,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_623,plain,(
    ! [A_126,B_127,C_128] :
      ( k1_relset_1(A_126,B_127,C_128) = k1_relat_1(C_128)
      | ~ m1_subset_1(C_128,k1_zfmisc_1(k2_zfmisc_1(A_126,B_127))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_642,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_82,c_623])).

tff(c_2933,plain,(
    ! [B_301,A_302,C_303] :
      ( k1_xboole_0 = B_301
      | k1_relset_1(A_302,B_301,C_303) = A_302
      | ~ v1_funct_2(C_303,A_302,B_301)
      | ~ m1_subset_1(C_303,k1_zfmisc_1(k2_zfmisc_1(A_302,B_301))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_2949,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_82,c_2933])).

tff(c_2963,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_642,c_2949])).

tff(c_2965,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_2963])).

tff(c_782,plain,(
    ! [A_140,B_141,C_142] :
      ( k2_relset_1(A_140,B_141,C_142) = k2_relat_1(C_142)
      | ~ m1_subset_1(C_142,k1_zfmisc_1(k2_zfmisc_1(A_140,B_141))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_795,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_82,c_782])).

tff(c_806,plain,(
    k2_relat_1('#skF_6') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_795])).

tff(c_34,plain,(
    ! [A_17] :
      ( v1_relat_1(k2_funct_1(A_17))
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_172,plain,(
    v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_1263,plain,(
    ! [B_191,A_192,C_193] :
      ( k1_xboole_0 = B_191
      | k1_relset_1(A_192,B_191,C_193) = A_192
      | ~ v1_funct_2(C_193,A_192,B_191)
      | ~ m1_subset_1(C_193,k1_zfmisc_1(k2_zfmisc_1(A_192,B_191))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_1279,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_82,c_1263])).

tff(c_1296,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_642,c_1279])).

tff(c_1298,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1296])).

tff(c_573,plain,(
    ! [A_118] :
      ( k2_relat_1(k2_funct_1(A_118)) = k1_relat_1(A_118)
      | ~ v2_funct_1(A_118)
      | ~ v1_funct_1(A_118)
      | ~ v1_relat_1(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_72,plain,(
    ! [A_34] :
      ( v1_funct_2(A_34,k1_relat_1(A_34),k2_relat_1(A_34))
      | ~ v1_funct_1(A_34)
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_2037,plain,(
    ! [A_247] :
      ( v1_funct_2(k2_funct_1(A_247),k1_relat_1(k2_funct_1(A_247)),k1_relat_1(A_247))
      | ~ v1_funct_1(k2_funct_1(A_247))
      | ~ v1_relat_1(k2_funct_1(A_247))
      | ~ v2_funct_1(A_247)
      | ~ v1_funct_1(A_247)
      | ~ v1_relat_1(A_247) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_573,c_72])).

tff(c_2046,plain,
    ( v1_funct_2(k2_funct_1('#skF_6'),k1_relat_1(k2_funct_1('#skF_6')),'#skF_4')
    | ~ v1_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6'))
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1298,c_2037])).

tff(c_2060,plain,
    ( v1_funct_2(k2_funct_1('#skF_6'),k1_relat_1(k2_funct_1('#skF_6')),'#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_86,c_80,c_172,c_2046])).

tff(c_2063,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_2060])).

tff(c_2066,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_34,c_2063])).

tff(c_2070,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_86,c_2066])).

tff(c_2072,plain,(
    v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_2060])).

tff(c_36,plain,(
    ! [A_18] :
      ( k2_relat_1(k2_funct_1(A_18)) = k1_relat_1(A_18)
      | ~ v2_funct_1(A_18)
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_737,plain,(
    ! [A_134] :
      ( m1_subset_1(A_134,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_134),k2_relat_1(A_134))))
      | ~ v1_funct_1(A_134)
      | ~ v1_relat_1(A_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_2522,plain,(
    ! [A_287] :
      ( m1_subset_1(k2_funct_1(A_287),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_287)),k1_relat_1(A_287))))
      | ~ v1_funct_1(k2_funct_1(A_287))
      | ~ v1_relat_1(k2_funct_1(A_287))
      | ~ v2_funct_1(A_287)
      | ~ v1_funct_1(A_287)
      | ~ v1_relat_1(A_287) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_737])).

tff(c_2546,plain,
    ( m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_6')),'#skF_4')))
    | ~ v1_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6'))
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1298,c_2522])).

tff(c_2565,plain,(
    m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_6')),'#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_86,c_80,c_2072,c_172,c_2546])).

tff(c_2588,plain,
    ( m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_6'),'#skF_4')))
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_2565])).

tff(c_2600,plain,(
    m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_86,c_80,c_806,c_2588])).

tff(c_2602,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_236,c_2600])).

tff(c_2603,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1296])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_24,plain,(
    ! [B_13] : k2_zfmisc_1(k1_xboole_0,B_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_195,plain,(
    ! [A_68,B_69] : m1_subset_1('#skF_3'(A_68,B_69),k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_206,plain,(
    ! [B_70] : m1_subset_1('#skF_3'(k1_xboole_0,B_70),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_195])).

tff(c_26,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(A_14,B_15)
      | ~ m1_subset_1(A_14,k1_zfmisc_1(B_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_210,plain,(
    ! [B_70] : r1_tarski('#skF_3'(k1_xboole_0,B_70),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_206,c_26])).

tff(c_329,plain,(
    ! [A_88,B_89] :
      ( r2_hidden('#skF_2'(A_88,B_89),A_88)
      | r1_tarski(A_88,B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_334,plain,(
    ! [A_90,B_91] :
      ( ~ v1_xboole_0(A_90)
      | r1_tarski(A_90,B_91) ) ),
    inference(resolution,[status(thm)],[c_329,c_2])).

tff(c_14,plain,(
    ! [B_11,A_10] :
      ( B_11 = A_10
      | ~ r1_tarski(B_11,A_10)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_365,plain,(
    ! [B_95,A_96] :
      ( B_95 = A_96
      | ~ r1_tarski(B_95,A_96)
      | ~ v1_xboole_0(A_96) ) ),
    inference(resolution,[status(thm)],[c_334,c_14])).

tff(c_377,plain,(
    ! [B_70] :
      ( '#skF_3'(k1_xboole_0,B_70) = k1_xboole_0
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_210,c_365])).

tff(c_391,plain,(
    ! [B_70] : '#skF_3'(k1_xboole_0,B_70) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_377])).

tff(c_205,plain,(
    ! [A_68,B_69] : r1_tarski('#skF_3'(A_68,B_69),k2_zfmisc_1(A_68,B_69)) ),
    inference(resolution,[status(thm)],[c_195,c_26])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_491,plain,(
    ! [C_101,B_102,A_103] :
      ( r2_hidden(C_101,B_102)
      | ~ r2_hidden(C_101,A_103)
      | ~ r1_tarski(A_103,B_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_597,plain,(
    ! [A_120,B_121,B_122] :
      ( r2_hidden('#skF_2'(A_120,B_121),B_122)
      | ~ r1_tarski(A_120,B_122)
      | r1_tarski(A_120,B_121) ) ),
    inference(resolution,[status(thm)],[c_10,c_491])).

tff(c_610,plain,(
    ! [B_123,A_124,B_125] :
      ( ~ v1_xboole_0(B_123)
      | ~ r1_tarski(A_124,B_123)
      | r1_tarski(A_124,B_125) ) ),
    inference(resolution,[status(thm)],[c_597,c_2])).

tff(c_647,plain,(
    ! [A_129,B_130,B_131] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_129,B_130))
      | r1_tarski('#skF_3'(A_129,B_130),B_131) ) ),
    inference(resolution,[status(thm)],[c_205,c_610])).

tff(c_668,plain,(
    ! [B_70,B_131] :
      ( ~ v1_xboole_0(k2_zfmisc_1(k1_xboole_0,B_70))
      | r1_tarski(k1_xboole_0,B_131) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_391,c_647])).

tff(c_681,plain,(
    ! [B_131] : r1_tarski(k1_xboole_0,B_131) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_24,c_668])).

tff(c_2628,plain,(
    ! [B_131] : r1_tarski('#skF_5',B_131) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2603,c_681])).

tff(c_22,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2643,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2603,c_2603,c_22])).

tff(c_70,plain,(
    ! [A_34] :
      ( m1_subset_1(A_34,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_34),k2_relat_1(A_34))))
      | ~ v1_funct_1(A_34)
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_810,plain,
    ( m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'),'#skF_5')))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_806,c_70])).

tff(c_817,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'),'#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_86,c_810])).

tff(c_838,plain,(
    r1_tarski('#skF_6',k2_zfmisc_1(k1_relat_1('#skF_6'),'#skF_5')) ),
    inference(resolution,[status(thm)],[c_817,c_26])).

tff(c_859,plain,
    ( k2_zfmisc_1(k1_relat_1('#skF_6'),'#skF_5') = '#skF_6'
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_6'),'#skF_5'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_838,c_14])).

tff(c_1090,plain,(
    ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_6'),'#skF_5'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_859])).

tff(c_2755,plain,(
    ~ r1_tarski('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2643,c_1090])).

tff(c_2765,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2628,c_2755])).

tff(c_2766,plain,(
    k2_zfmisc_1(k1_relat_1('#skF_6'),'#skF_5') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_859])).

tff(c_2968,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2965,c_2766])).

tff(c_173,plain,(
    ! [A_61,B_62] :
      ( r1_tarski(A_61,B_62)
      | ~ m1_subset_1(A_61,k1_zfmisc_1(B_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_177,plain,(
    r1_tarski('#skF_6',k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_82,c_173])).

tff(c_303,plain,(
    ! [B_84,A_85] :
      ( B_84 = A_85
      | ~ r1_tarski(B_84,A_85)
      | ~ r1_tarski(A_85,B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_317,plain,
    ( k2_zfmisc_1('#skF_4','#skF_5') = '#skF_6'
    | ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_177,c_303])).

tff(c_500,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_317])).

tff(c_2989,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2968,c_500])).

tff(c_2995,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_2989])).

tff(c_2996,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_2963])).

tff(c_3023,plain,(
    ! [B_131] : r1_tarski('#skF_5',B_131) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2996,c_681])).

tff(c_3038,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2996,c_2996,c_22])).

tff(c_3155,plain,(
    ~ r1_tarski('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3038,c_500])).

tff(c_3161,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3023,c_3155])).

tff(c_3162,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_317])).

tff(c_3166,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3162,c_82])).

tff(c_3503,plain,(
    ! [A_342,B_343,C_344] :
      ( k1_relset_1(A_342,B_343,C_344) = k1_relat_1(C_344)
      | ~ m1_subset_1(C_344,k1_zfmisc_1(k2_zfmisc_1(A_342,B_343))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_3646,plain,(
    ! [C_361] :
      ( k1_relset_1('#skF_4','#skF_5',C_361) = k1_relat_1(C_361)
      | ~ m1_subset_1(C_361,k1_zfmisc_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3162,c_3503])).

tff(c_3659,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_3166,c_3646])).

tff(c_4005,plain,(
    ! [B_390,A_391,C_392] :
      ( k1_xboole_0 = B_390
      | k1_relset_1(A_391,B_390,C_392) = A_391
      | ~ v1_funct_2(C_392,A_391,B_390)
      | ~ m1_subset_1(C_392,k1_zfmisc_1(k2_zfmisc_1(A_391,B_390))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_4014,plain,(
    ! [C_392] :
      ( k1_xboole_0 = '#skF_5'
      | k1_relset_1('#skF_4','#skF_5',C_392) = '#skF_4'
      | ~ v1_funct_2(C_392,'#skF_4','#skF_5')
      | ~ m1_subset_1(C_392,k1_zfmisc_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3162,c_4005])).

tff(c_4095,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_4014])).

tff(c_4138,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4095,c_12])).

tff(c_4137,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4095,c_4095,c_22])).

tff(c_392,plain,
    ( k2_zfmisc_1('#skF_4','#skF_5') = '#skF_6'
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_177,c_365])).

tff(c_435,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_392])).

tff(c_3164,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3162,c_435])).

tff(c_3707,plain,(
    ! [A_366,B_367,C_368] :
      ( k2_relset_1(A_366,B_367,C_368) = k2_relat_1(C_368)
      | ~ m1_subset_1(C_368,k1_zfmisc_1(k2_zfmisc_1(A_366,B_367))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_3769,plain,(
    ! [C_373] :
      ( k2_relset_1('#skF_4','#skF_5',C_373) = k2_relat_1(C_373)
      | ~ m1_subset_1(C_373,k1_zfmisc_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3162,c_3707])).

tff(c_3775,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_3166,c_3769])).

tff(c_3783,plain,(
    k2_relat_1('#skF_6') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_3775])).

tff(c_3788,plain,
    ( m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'),'#skF_5')))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_3783,c_70])).

tff(c_3795,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'),'#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_86,c_3788])).

tff(c_3816,plain,(
    r1_tarski('#skF_6',k2_zfmisc_1(k1_relat_1('#skF_6'),'#skF_5')) ),
    inference(resolution,[status(thm)],[c_3795,c_26])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3259,plain,(
    ! [A_318,B_319] :
      ( r2_hidden('#skF_1'(A_318),B_319)
      | ~ r1_tarski(A_318,B_319)
      | v1_xboole_0(A_318) ) ),
    inference(resolution,[status(thm)],[c_4,c_491])).

tff(c_3266,plain,(
    ! [B_319,A_318] :
      ( ~ v1_xboole_0(B_319)
      | ~ r1_tarski(A_318,B_319)
      | v1_xboole_0(A_318) ) ),
    inference(resolution,[status(thm)],[c_3259,c_2])).

tff(c_3825,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_6'),'#skF_5'))
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_3816,c_3266])).

tff(c_3837,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_6'),'#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_3164,c_3825])).

tff(c_4252,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4137,c_3837])).

tff(c_4257,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4138,c_4252])).

tff(c_4352,plain,(
    ! [C_420] :
      ( k1_relset_1('#skF_4','#skF_5',C_420) = '#skF_4'
      | ~ v1_funct_2(C_420,'#skF_4','#skF_5')
      | ~ m1_subset_1(C_420,k1_zfmisc_1('#skF_6')) ) ),
    inference(splitRight,[status(thm)],[c_4014])).

tff(c_4358,plain,
    ( k1_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_3166,c_4352])).

tff(c_4368,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_3659,c_4358])).

tff(c_3300,plain,(
    ! [A_324] :
      ( k2_relat_1(k2_funct_1(A_324)) = k1_relat_1(A_324)
      | ~ v2_funct_1(A_324)
      | ~ v1_funct_1(A_324)
      | ~ v1_relat_1(A_324) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_5329,plain,(
    ! [A_475] :
      ( v1_funct_2(k2_funct_1(A_475),k1_relat_1(k2_funct_1(A_475)),k1_relat_1(A_475))
      | ~ v1_funct_1(k2_funct_1(A_475))
      | ~ v1_relat_1(k2_funct_1(A_475))
      | ~ v2_funct_1(A_475)
      | ~ v1_funct_1(A_475)
      | ~ v1_relat_1(A_475) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3300,c_72])).

tff(c_5338,plain,
    ( v1_funct_2(k2_funct_1('#skF_6'),k1_relat_1(k2_funct_1('#skF_6')),'#skF_4')
    | ~ v1_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6'))
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_4368,c_5329])).

tff(c_5355,plain,
    ( v1_funct_2(k2_funct_1('#skF_6'),k1_relat_1(k2_funct_1('#skF_6')),'#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_86,c_80,c_172,c_5338])).

tff(c_5360,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_5355])).

tff(c_5363,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_34,c_5360])).

tff(c_5367,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_86,c_5363])).

tff(c_5369,plain,(
    v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_5355])).

tff(c_3450,plain,(
    ! [A_338] :
      ( m1_subset_1(A_338,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_338),k2_relat_1(A_338))))
      | ~ v1_funct_1(A_338)
      | ~ v1_relat_1(A_338) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_5798,plain,(
    ! [A_518] :
      ( m1_subset_1(k2_funct_1(A_518),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_518),k2_relat_1(k2_funct_1(A_518)))))
      | ~ v1_funct_1(k2_funct_1(A_518))
      | ~ v1_relat_1(k2_funct_1(A_518))
      | ~ v2_funct_1(A_518)
      | ~ v1_funct_1(A_518)
      | ~ v1_relat_1(A_518) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_3450])).

tff(c_5819,plain,
    ( m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_5',k2_relat_1(k2_funct_1('#skF_6')))))
    | ~ v1_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6'))
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_3783,c_5798])).

tff(c_5833,plain,(
    m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_5',k2_relat_1(k2_funct_1('#skF_6'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_86,c_80,c_5369,c_172,c_5819])).

tff(c_5854,plain,
    ( m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_relat_1('#skF_6'))))
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_5833])).

tff(c_5866,plain,(
    m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_86,c_80,c_4368,c_5854])).

tff(c_5868,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_236,c_5866])).

tff(c_5869,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_392])).

tff(c_5872,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_317])).

tff(c_5985,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_5869,c_5872])).

tff(c_5986,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_317])).

tff(c_5989,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5986,c_82])).

tff(c_5870,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_392])).

tff(c_6078,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5986,c_5870])).

tff(c_333,plain,(
    ! [A_88,B_89] :
      ( ~ v1_xboole_0(A_88)
      | r1_tarski(A_88,B_89) ) ),
    inference(resolution,[status(thm)],[c_329,c_2])).

tff(c_6164,plain,(
    ! [B_534,A_535] :
      ( B_534 = A_535
      | ~ v1_xboole_0(B_534)
      | ~ v1_xboole_0(A_535) ) ),
    inference(resolution,[status(thm)],[c_333,c_365])).

tff(c_6171,plain,(
    ! [A_536] :
      ( k1_xboole_0 = A_536
      | ~ v1_xboole_0(A_536) ) ),
    inference(resolution,[status(thm)],[c_12,c_6164])).

tff(c_6178,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_6078,c_6171])).

tff(c_6194,plain,(
    ! [B_13] : k2_zfmisc_1('#skF_6',B_13) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6178,c_6178,c_24])).

tff(c_20,plain,(
    ! [B_13,A_12] :
      ( k1_xboole_0 = B_13
      | k1_xboole_0 = A_12
      | k2_zfmisc_1(A_12,B_13) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_6006,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 != '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_5986,c_20])).

tff(c_6238,plain,
    ( '#skF_5' = '#skF_6'
    | '#skF_6' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6178,c_6178,c_6178,c_6006])).

tff(c_6239,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_6238])).

tff(c_6195,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6178,c_6178,c_22])).

tff(c_6385,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6239,c_6239,c_6195])).

tff(c_6254,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6239,c_236])).

tff(c_6476,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6385,c_6254])).

tff(c_6255,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6239,c_229])).

tff(c_6260,plain,(
    v1_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6239,c_86])).

tff(c_6259,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6239,c_80])).

tff(c_6185,plain,(
    ! [B_70] : '#skF_3'('#skF_6',B_70) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6178,c_6178,c_391])).

tff(c_6296,plain,(
    ! [B_70] : '#skF_3'('#skF_4',B_70) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6239,c_6239,c_6185])).

tff(c_58,plain,(
    ! [A_31,B_32] : v1_funct_2('#skF_3'(A_31,B_32),A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_68,plain,(
    ! [A_31,B_32] : m1_subset_1('#skF_3'(A_31,B_32),k1_zfmisc_1(k2_zfmisc_1(A_31,B_32))) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_6499,plain,(
    ! [A_557,B_558,C_559] :
      ( k1_relset_1(A_557,B_558,C_559) = k1_relat_1(C_559)
      | ~ m1_subset_1(C_559,k1_zfmisc_1(k2_zfmisc_1(A_557,B_558))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_6513,plain,(
    ! [A_31,B_32] : k1_relset_1(A_31,B_32,'#skF_3'(A_31,B_32)) = k1_relat_1('#skF_3'(A_31,B_32)) ),
    inference(resolution,[status(thm)],[c_68,c_6499])).

tff(c_6245,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6239,c_6178])).

tff(c_56,plain,(
    ! [B_29,A_28,C_30] :
      ( k1_xboole_0 = B_29
      | k1_relset_1(A_28,B_29,C_30) = A_28
      | ~ v1_funct_2(C_30,A_28,B_29)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_6662,plain,(
    ! [B_577,A_578,C_579] :
      ( B_577 = '#skF_4'
      | k1_relset_1(A_578,B_577,C_579) = A_578
      | ~ v1_funct_2(C_579,A_578,B_577)
      | ~ m1_subset_1(C_579,k1_zfmisc_1(k2_zfmisc_1(A_578,B_577))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6245,c_56])).

tff(c_6674,plain,(
    ! [B_32,A_31] :
      ( B_32 = '#skF_4'
      | k1_relset_1(A_31,B_32,'#skF_3'(A_31,B_32)) = A_31
      | ~ v1_funct_2('#skF_3'(A_31,B_32),A_31,B_32) ) ),
    inference(resolution,[status(thm)],[c_68,c_6662])).

tff(c_6687,plain,(
    ! [B_580,A_581] :
      ( B_580 = '#skF_4'
      | k1_relat_1('#skF_3'(A_581,B_580)) = A_581 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_6513,c_6674])).

tff(c_6705,plain,(
    ! [B_70] :
      ( B_70 = '#skF_4'
      | k1_relat_1('#skF_4') = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6296,c_6687])).

tff(c_6713,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_6705])).

tff(c_6256,plain,(
    v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6239,c_172])).

tff(c_6373,plain,(
    ! [A_549] :
      ( k2_relat_1(k2_funct_1(A_549)) = k1_relat_1(A_549)
      | ~ v2_funct_1(A_549)
      | ~ v1_funct_1(A_549)
      | ~ v1_relat_1(A_549) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_7521,plain,(
    ! [A_669] :
      ( v1_funct_2(k2_funct_1(A_669),k1_relat_1(k2_funct_1(A_669)),k1_relat_1(A_669))
      | ~ v1_funct_1(k2_funct_1(A_669))
      | ~ v1_relat_1(k2_funct_1(A_669))
      | ~ v2_funct_1(A_669)
      | ~ v1_funct_1(A_669)
      | ~ v1_relat_1(A_669) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6373,c_72])).

tff(c_7524,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),k1_relat_1(k2_funct_1('#skF_4')),'#skF_4')
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_6713,c_7521])).

tff(c_7535,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),k1_relat_1(k2_funct_1('#skF_4')),'#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6255,c_6260,c_6259,c_6256,c_7524])).

tff(c_7538,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_7535])).

tff(c_7541,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_7538])).

tff(c_7545,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6255,c_6260,c_7541])).

tff(c_7547,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_7535])).

tff(c_6602,plain,(
    ! [A_570,B_571,C_572] :
      ( k2_relset_1(A_570,B_571,C_572) = k2_relat_1(C_572)
      | ~ m1_subset_1(C_572,k1_zfmisc_1(k2_zfmisc_1(A_570,B_571))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_6763,plain,(
    ! [A_586,B_587] : k2_relset_1(A_586,B_587,'#skF_3'(A_586,B_587)) = k2_relat_1('#skF_3'(A_586,B_587)) ),
    inference(resolution,[status(thm)],[c_68,c_6602])).

tff(c_6775,plain,(
    ! [B_70] : k2_relat_1('#skF_3'('#skF_4',B_70)) = k2_relset_1('#skF_4',B_70,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_6296,c_6763])).

tff(c_6787,plain,(
    ! [B_589] : k2_relset_1('#skF_4',B_589,'#skF_4') = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6296,c_6775])).

tff(c_6257,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6239,c_78])).

tff(c_6794,plain,(
    k2_relat_1('#skF_4') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_6787,c_6257])).

tff(c_6532,plain,(
    ! [A_561] :
      ( m1_subset_1(A_561,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_561),k2_relat_1(A_561))))
      | ~ v1_funct_1(A_561)
      | ~ v1_relat_1(A_561) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_7861,plain,(
    ! [A_699] :
      ( m1_subset_1(k2_funct_1(A_699),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_699),k2_relat_1(k2_funct_1(A_699)))))
      | ~ v1_funct_1(k2_funct_1(A_699))
      | ~ v1_relat_1(k2_funct_1(A_699))
      | ~ v2_funct_1(A_699)
      | ~ v1_funct_1(A_699)
      | ~ v1_relat_1(A_699) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_6532])).

tff(c_7882,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_5',k2_relat_1(k2_funct_1('#skF_4')))))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_6794,c_7861])).

tff(c_7896,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_5',k2_relat_1(k2_funct_1('#skF_4'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6255,c_6260,c_6259,c_7547,c_6256,c_7882])).

tff(c_7936,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_relat_1('#skF_4'))))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_7896])).

tff(c_7948,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6255,c_6260,c_6259,c_6385,c_6713,c_7936])).

tff(c_7950,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6476,c_7948])).

tff(c_7976,plain,(
    ! [B_705] : B_705 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_6705])).

tff(c_28,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(A_14,k1_zfmisc_1(B_15))
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_6480,plain,(
    ~ r1_tarski(k2_funct_1('#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_6476])).

tff(c_8012,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_7976,c_6480])).

tff(c_8088,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_8012])).

tff(c_8089,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_6238])).

tff(c_8094,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8089,c_236])).

tff(c_8098,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6194,c_8094])).

tff(c_231,plain,(
    ! [A_75] : m1_subset_1('#skF_3'(A_75,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_195])).

tff(c_235,plain,(
    ! [A_75] : r1_tarski('#skF_3'(A_75,k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_231,c_26])).

tff(c_374,plain,(
    ! [A_75] :
      ( '#skF_3'(A_75,k1_xboole_0) = k1_xboole_0
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_235,c_365])).

tff(c_388,plain,(
    ! [A_75] : '#skF_3'(A_75,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_374])).

tff(c_6188,plain,(
    ! [A_75] : '#skF_3'(A_75,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6178,c_6178,c_388])).

tff(c_8507,plain,(
    ! [A_1732,B_1733,C_1734] :
      ( k2_relset_1(A_1732,B_1733,C_1734) = k2_relat_1(C_1734)
      | ~ m1_subset_1(C_1734,k1_zfmisc_1(k2_zfmisc_1(A_1732,B_1733))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_8577,plain,(
    ! [A_1741,B_1742] : k2_relset_1(A_1741,B_1742,'#skF_3'(A_1741,B_1742)) = k2_relat_1('#skF_3'(A_1741,B_1742)) ),
    inference(resolution,[status(thm)],[c_68,c_8507])).

tff(c_8589,plain,(
    ! [A_75] : k2_relat_1('#skF_3'(A_75,'#skF_6')) = k2_relset_1(A_75,'#skF_6','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_6188,c_8577])).

tff(c_8622,plain,(
    ! [A_1746] : k2_relset_1(A_1746,'#skF_6','#skF_6') = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6188,c_8589])).

tff(c_8095,plain,(
    k2_relset_1('#skF_4','#skF_6','#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8089,c_8089,c_78])).

tff(c_8629,plain,(
    k2_relat_1('#skF_6') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_8622,c_8095])).

tff(c_8103,plain,(
    ! [A_1701] :
      ( k1_relat_1(k2_funct_1(A_1701)) = k2_relat_1(A_1701)
      | ~ v2_funct_1(A_1701)
      | ~ v1_funct_1(A_1701)
      | ~ v1_relat_1(A_1701) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_9335,plain,(
    ! [A_1824] :
      ( v1_funct_2(k2_funct_1(A_1824),k2_relat_1(A_1824),k2_relat_1(k2_funct_1(A_1824)))
      | ~ v1_funct_1(k2_funct_1(A_1824))
      | ~ v1_relat_1(k2_funct_1(A_1824))
      | ~ v2_funct_1(A_1824)
      | ~ v1_funct_1(A_1824)
      | ~ v1_relat_1(A_1824) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8103,c_72])).

tff(c_9338,plain,
    ( v1_funct_2(k2_funct_1('#skF_6'),'#skF_6',k2_relat_1(k2_funct_1('#skF_6')))
    | ~ v1_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6'))
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_8629,c_9335])).

tff(c_9346,plain,
    ( v1_funct_2(k2_funct_1('#skF_6'),'#skF_6',k2_relat_1(k2_funct_1('#skF_6')))
    | ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_86,c_80,c_172,c_9338])).

tff(c_9347,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_9346])).

tff(c_9350,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_34,c_9347])).

tff(c_9354,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_86,c_9350])).

tff(c_9356,plain,(
    v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_9346])).

tff(c_8434,plain,(
    ! [A_1727,B_1728,C_1729] :
      ( k1_relset_1(A_1727,B_1728,C_1729) = k1_relat_1(C_1729)
      | ~ m1_subset_1(C_1729,k1_zfmisc_1(k2_zfmisc_1(A_1727,B_1728))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_8452,plain,(
    ! [A_31,B_32] : k1_relset_1(A_31,B_32,'#skF_3'(A_31,B_32)) = k1_relat_1('#skF_3'(A_31,B_32)) ),
    inference(resolution,[status(thm)],[c_68,c_8434])).

tff(c_8757,plain,(
    ! [B_1764,A_1765,C_1766] :
      ( B_1764 = '#skF_6'
      | k1_relset_1(A_1765,B_1764,C_1766) = A_1765
      | ~ v1_funct_2(C_1766,A_1765,B_1764)
      | ~ m1_subset_1(C_1766,k1_zfmisc_1(k2_zfmisc_1(A_1765,B_1764))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6178,c_56])).

tff(c_8769,plain,(
    ! [B_32,A_31] :
      ( B_32 = '#skF_6'
      | k1_relset_1(A_31,B_32,'#skF_3'(A_31,B_32)) = A_31
      | ~ v1_funct_2('#skF_3'(A_31,B_32),A_31,B_32) ) ),
    inference(resolution,[status(thm)],[c_68,c_8757])).

tff(c_8782,plain,(
    ! [B_1767,A_1768] :
      ( B_1767 = '#skF_6'
      | k1_relat_1('#skF_3'(A_1768,B_1767)) = A_1768 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_8452,c_8769])).

tff(c_8797,plain,(
    ! [B_70] :
      ( B_70 = '#skF_6'
      | k1_relat_1('#skF_6') = '#skF_6' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6185,c_8782])).

tff(c_8808,plain,(
    k1_relat_1('#skF_6') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_8797])).

tff(c_8318,plain,(
    ! [A_1711] :
      ( m1_subset_1(A_1711,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_1711),k2_relat_1(A_1711))))
      | ~ v1_funct_1(A_1711)
      | ~ v1_relat_1(A_1711) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_9693,plain,(
    ! [A_1854] :
      ( m1_subset_1(k2_funct_1(A_1854),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_1854)),k1_relat_1(A_1854))))
      | ~ v1_funct_1(k2_funct_1(A_1854))
      | ~ v1_relat_1(k2_funct_1(A_1854))
      | ~ v2_funct_1(A_1854)
      | ~ v1_funct_1(A_1854)
      | ~ v1_relat_1(A_1854) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_8318])).

tff(c_9714,plain,
    ( m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_6')),'#skF_6')))
    | ~ v1_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6'))
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_8808,c_9693])).

tff(c_9731,plain,(
    m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_86,c_80,c_9356,c_172,c_6195,c_9714])).

tff(c_9733,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8098,c_9731])).

tff(c_9736,plain,(
    ! [B_1855] : B_1855 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_8797])).

tff(c_9819,plain,(
    ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_9736,c_8098])).

tff(c_9937,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5989,c_9819])).

tff(c_9938,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_6'),'#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_171])).

tff(c_9939,plain,(
    m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_171])).

tff(c_10603,plain,(
    ! [A_3097,B_3098,C_3099] :
      ( k1_relset_1(A_3097,B_3098,C_3099) = k1_relat_1(C_3099)
      | ~ m1_subset_1(C_3099,k1_zfmisc_1(k2_zfmisc_1(A_3097,B_3098))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_10631,plain,(
    k1_relset_1('#skF_5','#skF_4',k2_funct_1('#skF_6')) = k1_relat_1(k2_funct_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_9939,c_10603])).

tff(c_11030,plain,(
    ! [B_3140,C_3141,A_3142] :
      ( k1_xboole_0 = B_3140
      | v1_funct_2(C_3141,A_3142,B_3140)
      | k1_relset_1(A_3142,B_3140,C_3141) != A_3142
      | ~ m1_subset_1(C_3141,k1_zfmisc_1(k2_zfmisc_1(A_3142,B_3140))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_11036,plain,
    ( k1_xboole_0 = '#skF_4'
    | v1_funct_2(k2_funct_1('#skF_6'),'#skF_5','#skF_4')
    | k1_relset_1('#skF_5','#skF_4',k2_funct_1('#skF_6')) != '#skF_5' ),
    inference(resolution,[status(thm)],[c_9939,c_11030])).

tff(c_11055,plain,
    ( k1_xboole_0 = '#skF_4'
    | v1_funct_2(k2_funct_1('#skF_6'),'#skF_5','#skF_4')
    | k1_relat_1(k2_funct_1('#skF_6')) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10631,c_11036])).

tff(c_11056,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1(k2_funct_1('#skF_6')) != '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_9938,c_11055])).

tff(c_11064,plain,(
    k1_relat_1(k2_funct_1('#skF_6')) != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_11056])).

tff(c_11067,plain,
    ( k2_relat_1('#skF_6') != '#skF_5'
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_11064])).

tff(c_11070,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_86,c_80,c_10545,c_11067])).

tff(c_11071,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_11056])).

tff(c_11113,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11071,c_12])).

tff(c_11111,plain,(
    ! [B_13] : k2_zfmisc_1('#skF_4',B_13) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11071,c_11071,c_24])).

tff(c_10016,plain,(
    ! [A_3039,B_3040] :
      ( r2_hidden('#skF_2'(A_3039,B_3040),A_3039)
      | r1_tarski(A_3039,B_3040) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_10026,plain,(
    ! [A_3039,B_3040] :
      ( ~ v1_xboole_0(A_3039)
      | r1_tarski(A_3039,B_3040) ) ),
    inference(resolution,[status(thm)],[c_10016,c_2])).

tff(c_10051,plain,(
    ! [B_3046,A_3047] :
      ( B_3046 = A_3047
      | ~ r1_tarski(B_3046,A_3047)
      | ~ r1_tarski(A_3047,B_3046) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_10083,plain,(
    ! [B_3051,A_3052] :
      ( B_3051 = A_3052
      | ~ r1_tarski(B_3051,A_3052)
      | ~ v1_xboole_0(A_3052) ) ),
    inference(resolution,[status(thm)],[c_10026,c_10051])).

tff(c_10114,plain,
    ( k2_zfmisc_1('#skF_4','#skF_5') = '#skF_6'
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_177,c_10083])).

tff(c_10157,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_10114])).

tff(c_11165,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11111,c_10157])).

tff(c_11170,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11113,c_11165])).

tff(c_11171,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_10114])).

tff(c_10071,plain,
    ( k2_zfmisc_1('#skF_4','#skF_5') = '#skF_6'
    | ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_177,c_10051])).

tff(c_11227,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_10071])).

tff(c_11275,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_11171,c_11227])).

tff(c_11276,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_10071])).

tff(c_11298,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 != '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_11276,c_20])).

tff(c_11397,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_11298])).

tff(c_11172,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_10114])).

tff(c_11309,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11276,c_11172])).

tff(c_11390,plain,(
    ! [B_3155,A_3156] :
      ( B_3155 = A_3156
      | ~ v1_xboole_0(B_3155)
      | ~ v1_xboole_0(A_3156) ) ),
    inference(resolution,[status(thm)],[c_10026,c_10083])).

tff(c_11398,plain,(
    ! [A_3157] :
      ( A_3157 = '#skF_6'
      | ~ v1_xboole_0(A_3157) ) ),
    inference(resolution,[status(thm)],[c_11309,c_11390])).

tff(c_11404,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_12,c_11398])).

tff(c_11410,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11397,c_11404])).

tff(c_11412,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_11298])).

tff(c_10098,plain,(
    ! [B_70] :
      ( '#skF_3'(k1_xboole_0,B_70) = k1_xboole_0
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_210,c_10083])).

tff(c_11188,plain,(
    ! [B_3144] : '#skF_3'(k1_xboole_0,B_3144) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_10098])).

tff(c_11202,plain,(
    ! [B_3144] : v1_funct_2(k1_xboole_0,k1_xboole_0,B_3144) ),
    inference(superposition,[status(thm),theory(equality)],[c_11188,c_58])).

tff(c_11414,plain,(
    ! [B_3144] : v1_funct_2('#skF_6','#skF_6',B_3144) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11412,c_11412,c_11202])).

tff(c_11425,plain,(
    ! [B_13] : k2_zfmisc_1('#skF_6',B_13) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11412,c_11412,c_24])).

tff(c_11411,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_11298])).

tff(c_11533,plain,
    ( '#skF_6' = '#skF_4'
    | '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11412,c_11412,c_11411])).

tff(c_11534,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_11533])).

tff(c_9948,plain,(
    r1_tarski(k2_funct_1('#skF_6'),k2_zfmisc_1('#skF_5','#skF_4')) ),
    inference(resolution,[status(thm)],[c_9939,c_26])).

tff(c_11537,plain,(
    r1_tarski(k2_funct_1('#skF_6'),k2_zfmisc_1('#skF_6','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11534,c_9948])).

tff(c_11544,plain,(
    r1_tarski(k2_funct_1('#skF_6'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11425,c_11537])).

tff(c_10066,plain,(
    ! [B_3040,A_3039] :
      ( B_3040 = A_3039
      | ~ r1_tarski(B_3040,A_3039)
      | ~ v1_xboole_0(A_3039) ) ),
    inference(resolution,[status(thm)],[c_10026,c_10051])).

tff(c_11595,plain,
    ( k2_funct_1('#skF_6') = '#skF_6'
    | ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_11544,c_10066])).

tff(c_11602,plain,(
    k2_funct_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11309,c_11595])).

tff(c_11539,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_6'),'#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11534,c_9938])).

tff(c_11694,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11414,c_11602,c_11539])).

tff(c_11695,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_11533])).

tff(c_10095,plain,(
    ! [A_75] :
      ( '#skF_3'(A_75,k1_xboole_0) = k1_xboole_0
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_235,c_10083])).

tff(c_10110,plain,(
    ! [A_75] : '#skF_3'(A_75,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_10095])).

tff(c_11419,plain,(
    ! [A_75] : '#skF_3'(A_75,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11412,c_11412,c_10110])).

tff(c_11777,plain,(
    ! [A_3174] : '#skF_3'(A_3174,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11695,c_11695,c_11419])).

tff(c_11788,plain,(
    ! [A_3174] : v1_funct_2('#skF_4',A_3174,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_11777,c_58])).

tff(c_11706,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11695,c_11309])).

tff(c_11426,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11412,c_11412,c_22])).

tff(c_11699,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11695,c_11695,c_11426])).

tff(c_11711,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11695,c_9939])).

tff(c_11989,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11699,c_11711])).

tff(c_11993,plain,(
    r1_tarski(k2_funct_1('#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_11989,c_26])).

tff(c_11999,plain,
    ( k2_funct_1('#skF_4') = '#skF_4'
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_11993,c_10066])).

tff(c_12006,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11706,c_11999])).

tff(c_11712,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11695,c_9938])).

tff(c_12010,plain,(
    ~ v1_funct_2('#skF_4','#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12006,c_11712])).

tff(c_12017,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11788,c_12010])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:48:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.38/2.90  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.38/2.95  
% 8.38/2.95  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.38/2.96  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 8.38/2.96  
% 8.38/2.96  %Foreground sorts:
% 8.38/2.96  
% 8.38/2.96  
% 8.38/2.96  %Background operators:
% 8.38/2.96  
% 8.38/2.96  
% 8.38/2.96  %Foreground operators:
% 8.38/2.96  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 8.38/2.96  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.38/2.96  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 8.38/2.96  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 8.38/2.96  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.38/2.96  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.38/2.96  tff('#skF_1', type, '#skF_1': $i > $i).
% 8.38/2.96  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.38/2.96  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 8.38/2.96  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.38/2.96  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.38/2.96  tff('#skF_5', type, '#skF_5': $i).
% 8.38/2.96  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.38/2.96  tff('#skF_6', type, '#skF_6': $i).
% 8.38/2.96  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 8.38/2.96  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 8.38/2.96  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.38/2.96  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.38/2.96  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.38/2.96  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.38/2.96  tff('#skF_4', type, '#skF_4': $i).
% 8.38/2.96  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.38/2.96  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 8.38/2.96  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 8.38/2.96  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.38/2.96  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.38/2.96  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.38/2.96  
% 8.38/2.99  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.38/2.99  tff(f_147, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 8.38/2.99  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 8.38/2.99  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 8.38/2.99  tff(f_77, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 8.38/2.99  tff(f_67, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 8.38/2.99  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 8.38/2.99  tff(f_107, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 8.38/2.99  tff(f_130, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 8.38/2.99  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 8.38/2.99  tff(f_51, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 8.38/2.99  tff(f_120, axiom, (![A, B]: (?[C]: (((((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & v1_relat_1(C)) & v4_relat_1(C, A)) & v5_relat_1(C, B)) & v1_funct_1(C)) & v1_funct_2(C, A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_funct_2)).
% 8.38/2.99  tff(f_55, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 8.38/2.99  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 8.38/2.99  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 8.38/2.99  tff(c_18, plain, (![B_11]: (r1_tarski(B_11, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.38/2.99  tff(c_82, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_147])).
% 8.38/2.99  tff(c_211, plain, (![C_71, A_72, B_73]: (v1_relat_1(C_71) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.38/2.99  tff(c_229, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_82, c_211])).
% 8.38/2.99  tff(c_86, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_147])).
% 8.38/2.99  tff(c_80, plain, (v2_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_147])).
% 8.38/2.99  tff(c_78, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_5'), inference(cnfTransformation, [status(thm)], [f_147])).
% 8.38/2.99  tff(c_10517, plain, (![A_3094, B_3095, C_3096]: (k2_relset_1(A_3094, B_3095, C_3096)=k2_relat_1(C_3096) | ~m1_subset_1(C_3096, k1_zfmisc_1(k2_zfmisc_1(A_3094, B_3095))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 8.38/2.99  tff(c_10533, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_82, c_10517])).
% 8.38/2.99  tff(c_10545, plain, (k2_relat_1('#skF_6')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_10533])).
% 8.38/2.99  tff(c_38, plain, (![A_18]: (k1_relat_1(k2_funct_1(A_18))=k2_relat_1(A_18) | ~v2_funct_1(A_18) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_77])).
% 8.38/2.99  tff(c_32, plain, (![A_17]: (v1_funct_1(k2_funct_1(A_17)) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.38/2.99  tff(c_76, plain, (~m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4'))) | ~v1_funct_2(k2_funct_1('#skF_6'), '#skF_5', '#skF_4') | ~v1_funct_1(k2_funct_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_147])).
% 8.38/2.99  tff(c_136, plain, (~v1_funct_1(k2_funct_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_76])).
% 8.38/2.99  tff(c_139, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_32, c_136])).
% 8.38/2.99  tff(c_142, plain, (~v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_139])).
% 8.38/2.99  tff(c_154, plain, (![C_58, A_59, B_60]: (v1_relat_1(C_58) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.38/2.99  tff(c_161, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_82, c_154])).
% 8.38/2.99  tff(c_170, plain, $false, inference(negUnitSimplification, [status(thm)], [c_142, c_161])).
% 8.38/2.99  tff(c_171, plain, (~v1_funct_2(k2_funct_1('#skF_6'), '#skF_5', '#skF_4') | ~m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4')))), inference(splitRight, [status(thm)], [c_76])).
% 8.38/2.99  tff(c_236, plain, (~m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4')))), inference(splitLeft, [status(thm)], [c_171])).
% 8.38/2.99  tff(c_84, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_147])).
% 8.38/2.99  tff(c_623, plain, (![A_126, B_127, C_128]: (k1_relset_1(A_126, B_127, C_128)=k1_relat_1(C_128) | ~m1_subset_1(C_128, k1_zfmisc_1(k2_zfmisc_1(A_126, B_127))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 8.38/2.99  tff(c_642, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_82, c_623])).
% 8.38/2.99  tff(c_2933, plain, (![B_301, A_302, C_303]: (k1_xboole_0=B_301 | k1_relset_1(A_302, B_301, C_303)=A_302 | ~v1_funct_2(C_303, A_302, B_301) | ~m1_subset_1(C_303, k1_zfmisc_1(k2_zfmisc_1(A_302, B_301))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 8.38/2.99  tff(c_2949, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_82, c_2933])).
% 8.38/2.99  tff(c_2963, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_642, c_2949])).
% 8.38/2.99  tff(c_2965, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitLeft, [status(thm)], [c_2963])).
% 8.38/2.99  tff(c_782, plain, (![A_140, B_141, C_142]: (k2_relset_1(A_140, B_141, C_142)=k2_relat_1(C_142) | ~m1_subset_1(C_142, k1_zfmisc_1(k2_zfmisc_1(A_140, B_141))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 8.38/2.99  tff(c_795, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_82, c_782])).
% 8.38/2.99  tff(c_806, plain, (k2_relat_1('#skF_6')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_795])).
% 8.38/2.99  tff(c_34, plain, (![A_17]: (v1_relat_1(k2_funct_1(A_17)) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.38/2.99  tff(c_172, plain, (v1_funct_1(k2_funct_1('#skF_6'))), inference(splitRight, [status(thm)], [c_76])).
% 8.38/2.99  tff(c_1263, plain, (![B_191, A_192, C_193]: (k1_xboole_0=B_191 | k1_relset_1(A_192, B_191, C_193)=A_192 | ~v1_funct_2(C_193, A_192, B_191) | ~m1_subset_1(C_193, k1_zfmisc_1(k2_zfmisc_1(A_192, B_191))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 8.38/2.99  tff(c_1279, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_82, c_1263])).
% 8.38/2.99  tff(c_1296, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_642, c_1279])).
% 8.38/2.99  tff(c_1298, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitLeft, [status(thm)], [c_1296])).
% 8.38/2.99  tff(c_573, plain, (![A_118]: (k2_relat_1(k2_funct_1(A_118))=k1_relat_1(A_118) | ~v2_funct_1(A_118) | ~v1_funct_1(A_118) | ~v1_relat_1(A_118))), inference(cnfTransformation, [status(thm)], [f_77])).
% 8.38/2.99  tff(c_72, plain, (![A_34]: (v1_funct_2(A_34, k1_relat_1(A_34), k2_relat_1(A_34)) | ~v1_funct_1(A_34) | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_130])).
% 8.38/2.99  tff(c_2037, plain, (![A_247]: (v1_funct_2(k2_funct_1(A_247), k1_relat_1(k2_funct_1(A_247)), k1_relat_1(A_247)) | ~v1_funct_1(k2_funct_1(A_247)) | ~v1_relat_1(k2_funct_1(A_247)) | ~v2_funct_1(A_247) | ~v1_funct_1(A_247) | ~v1_relat_1(A_247))), inference(superposition, [status(thm), theory('equality')], [c_573, c_72])).
% 8.38/2.99  tff(c_2046, plain, (v1_funct_2(k2_funct_1('#skF_6'), k1_relat_1(k2_funct_1('#skF_6')), '#skF_4') | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')) | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1298, c_2037])).
% 8.38/2.99  tff(c_2060, plain, (v1_funct_2(k2_funct_1('#skF_6'), k1_relat_1(k2_funct_1('#skF_6')), '#skF_4') | ~v1_relat_1(k2_funct_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_229, c_86, c_80, c_172, c_2046])).
% 8.38/2.99  tff(c_2063, plain, (~v1_relat_1(k2_funct_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_2060])).
% 8.38/2.99  tff(c_2066, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_34, c_2063])).
% 8.38/2.99  tff(c_2070, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_229, c_86, c_2066])).
% 8.38/2.99  tff(c_2072, plain, (v1_relat_1(k2_funct_1('#skF_6'))), inference(splitRight, [status(thm)], [c_2060])).
% 8.38/2.99  tff(c_36, plain, (![A_18]: (k2_relat_1(k2_funct_1(A_18))=k1_relat_1(A_18) | ~v2_funct_1(A_18) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_77])).
% 8.38/2.99  tff(c_737, plain, (![A_134]: (m1_subset_1(A_134, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_134), k2_relat_1(A_134)))) | ~v1_funct_1(A_134) | ~v1_relat_1(A_134))), inference(cnfTransformation, [status(thm)], [f_130])).
% 8.38/2.99  tff(c_2522, plain, (![A_287]: (m1_subset_1(k2_funct_1(A_287), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_287)), k1_relat_1(A_287)))) | ~v1_funct_1(k2_funct_1(A_287)) | ~v1_relat_1(k2_funct_1(A_287)) | ~v2_funct_1(A_287) | ~v1_funct_1(A_287) | ~v1_relat_1(A_287))), inference(superposition, [status(thm), theory('equality')], [c_36, c_737])).
% 8.38/2.99  tff(c_2546, plain, (m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_6')), '#skF_4'))) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')) | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1298, c_2522])).
% 8.38/2.99  tff(c_2565, plain, (m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_6')), '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_229, c_86, c_80, c_2072, c_172, c_2546])).
% 8.38/2.99  tff(c_2588, plain, (m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_6'), '#skF_4'))) | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_38, c_2565])).
% 8.38/2.99  tff(c_2600, plain, (m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_229, c_86, c_80, c_806, c_2588])).
% 8.38/2.99  tff(c_2602, plain, $false, inference(negUnitSimplification, [status(thm)], [c_236, c_2600])).
% 8.38/2.99  tff(c_2603, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_1296])).
% 8.38/2.99  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.38/2.99  tff(c_24, plain, (![B_13]: (k2_zfmisc_1(k1_xboole_0, B_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.38/2.99  tff(c_195, plain, (![A_68, B_69]: (m1_subset_1('#skF_3'(A_68, B_69), k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 8.38/2.99  tff(c_206, plain, (![B_70]: (m1_subset_1('#skF_3'(k1_xboole_0, B_70), k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_195])).
% 8.38/2.99  tff(c_26, plain, (![A_14, B_15]: (r1_tarski(A_14, B_15) | ~m1_subset_1(A_14, k1_zfmisc_1(B_15)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.38/2.99  tff(c_210, plain, (![B_70]: (r1_tarski('#skF_3'(k1_xboole_0, B_70), k1_xboole_0))), inference(resolution, [status(thm)], [c_206, c_26])).
% 8.38/2.99  tff(c_329, plain, (![A_88, B_89]: (r2_hidden('#skF_2'(A_88, B_89), A_88) | r1_tarski(A_88, B_89))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.38/2.99  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.38/2.99  tff(c_334, plain, (![A_90, B_91]: (~v1_xboole_0(A_90) | r1_tarski(A_90, B_91))), inference(resolution, [status(thm)], [c_329, c_2])).
% 8.38/2.99  tff(c_14, plain, (![B_11, A_10]: (B_11=A_10 | ~r1_tarski(B_11, A_10) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.38/2.99  tff(c_365, plain, (![B_95, A_96]: (B_95=A_96 | ~r1_tarski(B_95, A_96) | ~v1_xboole_0(A_96))), inference(resolution, [status(thm)], [c_334, c_14])).
% 8.38/2.99  tff(c_377, plain, (![B_70]: ('#skF_3'(k1_xboole_0, B_70)=k1_xboole_0 | ~v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_210, c_365])).
% 8.38/2.99  tff(c_391, plain, (![B_70]: ('#skF_3'(k1_xboole_0, B_70)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_377])).
% 8.38/2.99  tff(c_205, plain, (![A_68, B_69]: (r1_tarski('#skF_3'(A_68, B_69), k2_zfmisc_1(A_68, B_69)))), inference(resolution, [status(thm)], [c_195, c_26])).
% 8.38/2.99  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.38/2.99  tff(c_491, plain, (![C_101, B_102, A_103]: (r2_hidden(C_101, B_102) | ~r2_hidden(C_101, A_103) | ~r1_tarski(A_103, B_102))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.38/2.99  tff(c_597, plain, (![A_120, B_121, B_122]: (r2_hidden('#skF_2'(A_120, B_121), B_122) | ~r1_tarski(A_120, B_122) | r1_tarski(A_120, B_121))), inference(resolution, [status(thm)], [c_10, c_491])).
% 8.38/2.99  tff(c_610, plain, (![B_123, A_124, B_125]: (~v1_xboole_0(B_123) | ~r1_tarski(A_124, B_123) | r1_tarski(A_124, B_125))), inference(resolution, [status(thm)], [c_597, c_2])).
% 8.38/2.99  tff(c_647, plain, (![A_129, B_130, B_131]: (~v1_xboole_0(k2_zfmisc_1(A_129, B_130)) | r1_tarski('#skF_3'(A_129, B_130), B_131))), inference(resolution, [status(thm)], [c_205, c_610])).
% 8.38/2.99  tff(c_668, plain, (![B_70, B_131]: (~v1_xboole_0(k2_zfmisc_1(k1_xboole_0, B_70)) | r1_tarski(k1_xboole_0, B_131))), inference(superposition, [status(thm), theory('equality')], [c_391, c_647])).
% 8.38/2.99  tff(c_681, plain, (![B_131]: (r1_tarski(k1_xboole_0, B_131))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_24, c_668])).
% 8.38/2.99  tff(c_2628, plain, (![B_131]: (r1_tarski('#skF_5', B_131))), inference(demodulation, [status(thm), theory('equality')], [c_2603, c_681])).
% 8.38/2.99  tff(c_22, plain, (![A_12]: (k2_zfmisc_1(A_12, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.38/2.99  tff(c_2643, plain, (![A_12]: (k2_zfmisc_1(A_12, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2603, c_2603, c_22])).
% 8.38/2.99  tff(c_70, plain, (![A_34]: (m1_subset_1(A_34, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_34), k2_relat_1(A_34)))) | ~v1_funct_1(A_34) | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_130])).
% 8.38/2.99  tff(c_810, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'), '#skF_5'))) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_806, c_70])).
% 8.38/2.99  tff(c_817, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'), '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_229, c_86, c_810])).
% 8.38/2.99  tff(c_838, plain, (r1_tarski('#skF_6', k2_zfmisc_1(k1_relat_1('#skF_6'), '#skF_5'))), inference(resolution, [status(thm)], [c_817, c_26])).
% 8.38/2.99  tff(c_859, plain, (k2_zfmisc_1(k1_relat_1('#skF_6'), '#skF_5')='#skF_6' | ~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_6'), '#skF_5'), '#skF_6')), inference(resolution, [status(thm)], [c_838, c_14])).
% 8.38/2.99  tff(c_1090, plain, (~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_6'), '#skF_5'), '#skF_6')), inference(splitLeft, [status(thm)], [c_859])).
% 8.38/2.99  tff(c_2755, plain, (~r1_tarski('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2643, c_1090])).
% 8.38/2.99  tff(c_2765, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2628, c_2755])).
% 8.38/2.99  tff(c_2766, plain, (k2_zfmisc_1(k1_relat_1('#skF_6'), '#skF_5')='#skF_6'), inference(splitRight, [status(thm)], [c_859])).
% 8.38/2.99  tff(c_2968, plain, (k2_zfmisc_1('#skF_4', '#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_2965, c_2766])).
% 8.38/2.99  tff(c_173, plain, (![A_61, B_62]: (r1_tarski(A_61, B_62) | ~m1_subset_1(A_61, k1_zfmisc_1(B_62)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.38/2.99  tff(c_177, plain, (r1_tarski('#skF_6', k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_82, c_173])).
% 8.38/2.99  tff(c_303, plain, (![B_84, A_85]: (B_84=A_85 | ~r1_tarski(B_84, A_85) | ~r1_tarski(A_85, B_84))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.38/2.99  tff(c_317, plain, (k2_zfmisc_1('#skF_4', '#skF_5')='#skF_6' | ~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), '#skF_6')), inference(resolution, [status(thm)], [c_177, c_303])).
% 8.38/2.99  tff(c_500, plain, (~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), '#skF_6')), inference(splitLeft, [status(thm)], [c_317])).
% 8.38/2.99  tff(c_2989, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2968, c_500])).
% 8.38/2.99  tff(c_2995, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_2989])).
% 8.38/2.99  tff(c_2996, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_2963])).
% 8.38/2.99  tff(c_3023, plain, (![B_131]: (r1_tarski('#skF_5', B_131))), inference(demodulation, [status(thm), theory('equality')], [c_2996, c_681])).
% 8.38/2.99  tff(c_3038, plain, (![A_12]: (k2_zfmisc_1(A_12, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2996, c_2996, c_22])).
% 8.38/2.99  tff(c_3155, plain, (~r1_tarski('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3038, c_500])).
% 8.38/2.99  tff(c_3161, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3023, c_3155])).
% 8.38/2.99  tff(c_3162, plain, (k2_zfmisc_1('#skF_4', '#skF_5')='#skF_6'), inference(splitRight, [status(thm)], [c_317])).
% 8.38/2.99  tff(c_3166, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_3162, c_82])).
% 8.38/2.99  tff(c_3503, plain, (![A_342, B_343, C_344]: (k1_relset_1(A_342, B_343, C_344)=k1_relat_1(C_344) | ~m1_subset_1(C_344, k1_zfmisc_1(k2_zfmisc_1(A_342, B_343))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 8.38/2.99  tff(c_3646, plain, (![C_361]: (k1_relset_1('#skF_4', '#skF_5', C_361)=k1_relat_1(C_361) | ~m1_subset_1(C_361, k1_zfmisc_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_3162, c_3503])).
% 8.38/2.99  tff(c_3659, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_3166, c_3646])).
% 8.38/2.99  tff(c_4005, plain, (![B_390, A_391, C_392]: (k1_xboole_0=B_390 | k1_relset_1(A_391, B_390, C_392)=A_391 | ~v1_funct_2(C_392, A_391, B_390) | ~m1_subset_1(C_392, k1_zfmisc_1(k2_zfmisc_1(A_391, B_390))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 8.38/2.99  tff(c_4014, plain, (![C_392]: (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', C_392)='#skF_4' | ~v1_funct_2(C_392, '#skF_4', '#skF_5') | ~m1_subset_1(C_392, k1_zfmisc_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_3162, c_4005])).
% 8.38/2.99  tff(c_4095, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_4014])).
% 8.38/2.99  tff(c_4138, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4095, c_12])).
% 8.38/2.99  tff(c_4137, plain, (![A_12]: (k2_zfmisc_1(A_12, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4095, c_4095, c_22])).
% 8.38/2.99  tff(c_392, plain, (k2_zfmisc_1('#skF_4', '#skF_5')='#skF_6' | ~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_177, c_365])).
% 8.38/2.99  tff(c_435, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_392])).
% 8.38/2.99  tff(c_3164, plain, (~v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3162, c_435])).
% 8.38/2.99  tff(c_3707, plain, (![A_366, B_367, C_368]: (k2_relset_1(A_366, B_367, C_368)=k2_relat_1(C_368) | ~m1_subset_1(C_368, k1_zfmisc_1(k2_zfmisc_1(A_366, B_367))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 8.38/2.99  tff(c_3769, plain, (![C_373]: (k2_relset_1('#skF_4', '#skF_5', C_373)=k2_relat_1(C_373) | ~m1_subset_1(C_373, k1_zfmisc_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_3162, c_3707])).
% 8.38/2.99  tff(c_3775, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_3166, c_3769])).
% 8.38/2.99  tff(c_3783, plain, (k2_relat_1('#skF_6')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_3775])).
% 8.38/2.99  tff(c_3788, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'), '#skF_5'))) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_3783, c_70])).
% 8.38/2.99  tff(c_3795, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'), '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_229, c_86, c_3788])).
% 8.38/2.99  tff(c_3816, plain, (r1_tarski('#skF_6', k2_zfmisc_1(k1_relat_1('#skF_6'), '#skF_5'))), inference(resolution, [status(thm)], [c_3795, c_26])).
% 8.38/2.99  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.38/2.99  tff(c_3259, plain, (![A_318, B_319]: (r2_hidden('#skF_1'(A_318), B_319) | ~r1_tarski(A_318, B_319) | v1_xboole_0(A_318))), inference(resolution, [status(thm)], [c_4, c_491])).
% 8.38/2.99  tff(c_3266, plain, (![B_319, A_318]: (~v1_xboole_0(B_319) | ~r1_tarski(A_318, B_319) | v1_xboole_0(A_318))), inference(resolution, [status(thm)], [c_3259, c_2])).
% 8.38/2.99  tff(c_3825, plain, (~v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_6'), '#skF_5')) | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_3816, c_3266])).
% 8.38/2.99  tff(c_3837, plain, (~v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_6'), '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_3164, c_3825])).
% 8.38/2.99  tff(c_4252, plain, (~v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4137, c_3837])).
% 8.38/2.99  tff(c_4257, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4138, c_4252])).
% 8.38/2.99  tff(c_4352, plain, (![C_420]: (k1_relset_1('#skF_4', '#skF_5', C_420)='#skF_4' | ~v1_funct_2(C_420, '#skF_4', '#skF_5') | ~m1_subset_1(C_420, k1_zfmisc_1('#skF_6')))), inference(splitRight, [status(thm)], [c_4014])).
% 8.38/2.99  tff(c_4358, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_3166, c_4352])).
% 8.38/2.99  tff(c_4368, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_3659, c_4358])).
% 8.38/2.99  tff(c_3300, plain, (![A_324]: (k2_relat_1(k2_funct_1(A_324))=k1_relat_1(A_324) | ~v2_funct_1(A_324) | ~v1_funct_1(A_324) | ~v1_relat_1(A_324))), inference(cnfTransformation, [status(thm)], [f_77])).
% 8.38/2.99  tff(c_5329, plain, (![A_475]: (v1_funct_2(k2_funct_1(A_475), k1_relat_1(k2_funct_1(A_475)), k1_relat_1(A_475)) | ~v1_funct_1(k2_funct_1(A_475)) | ~v1_relat_1(k2_funct_1(A_475)) | ~v2_funct_1(A_475) | ~v1_funct_1(A_475) | ~v1_relat_1(A_475))), inference(superposition, [status(thm), theory('equality')], [c_3300, c_72])).
% 8.38/2.99  tff(c_5338, plain, (v1_funct_2(k2_funct_1('#skF_6'), k1_relat_1(k2_funct_1('#skF_6')), '#skF_4') | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')) | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_4368, c_5329])).
% 8.38/2.99  tff(c_5355, plain, (v1_funct_2(k2_funct_1('#skF_6'), k1_relat_1(k2_funct_1('#skF_6')), '#skF_4') | ~v1_relat_1(k2_funct_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_229, c_86, c_80, c_172, c_5338])).
% 8.38/2.99  tff(c_5360, plain, (~v1_relat_1(k2_funct_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_5355])).
% 8.38/2.99  tff(c_5363, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_34, c_5360])).
% 8.38/2.99  tff(c_5367, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_229, c_86, c_5363])).
% 8.38/2.99  tff(c_5369, plain, (v1_relat_1(k2_funct_1('#skF_6'))), inference(splitRight, [status(thm)], [c_5355])).
% 8.38/2.99  tff(c_3450, plain, (![A_338]: (m1_subset_1(A_338, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_338), k2_relat_1(A_338)))) | ~v1_funct_1(A_338) | ~v1_relat_1(A_338))), inference(cnfTransformation, [status(thm)], [f_130])).
% 8.38/2.99  tff(c_5798, plain, (![A_518]: (m1_subset_1(k2_funct_1(A_518), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_518), k2_relat_1(k2_funct_1(A_518))))) | ~v1_funct_1(k2_funct_1(A_518)) | ~v1_relat_1(k2_funct_1(A_518)) | ~v2_funct_1(A_518) | ~v1_funct_1(A_518) | ~v1_relat_1(A_518))), inference(superposition, [status(thm), theory('equality')], [c_38, c_3450])).
% 8.38/2.99  tff(c_5819, plain, (m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', k2_relat_1(k2_funct_1('#skF_6'))))) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')) | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_3783, c_5798])).
% 8.38/2.99  tff(c_5833, plain, (m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', k2_relat_1(k2_funct_1('#skF_6')))))), inference(demodulation, [status(thm), theory('equality')], [c_229, c_86, c_80, c_5369, c_172, c_5819])).
% 8.38/2.99  tff(c_5854, plain, (m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_relat_1('#skF_6')))) | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_36, c_5833])).
% 8.38/2.99  tff(c_5866, plain, (m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_229, c_86, c_80, c_4368, c_5854])).
% 8.38/2.99  tff(c_5868, plain, $false, inference(negUnitSimplification, [status(thm)], [c_236, c_5866])).
% 8.38/2.99  tff(c_5869, plain, (k2_zfmisc_1('#skF_4', '#skF_5')='#skF_6'), inference(splitRight, [status(thm)], [c_392])).
% 8.38/2.99  tff(c_5872, plain, (~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), '#skF_6')), inference(splitLeft, [status(thm)], [c_317])).
% 8.38/2.99  tff(c_5985, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_5869, c_5872])).
% 8.38/2.99  tff(c_5986, plain, (k2_zfmisc_1('#skF_4', '#skF_5')='#skF_6'), inference(splitRight, [status(thm)], [c_317])).
% 8.38/2.99  tff(c_5989, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_5986, c_82])).
% 8.38/2.99  tff(c_5870, plain, (v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_392])).
% 8.38/2.99  tff(c_6078, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_5986, c_5870])).
% 8.38/2.99  tff(c_333, plain, (![A_88, B_89]: (~v1_xboole_0(A_88) | r1_tarski(A_88, B_89))), inference(resolution, [status(thm)], [c_329, c_2])).
% 8.38/2.99  tff(c_6164, plain, (![B_534, A_535]: (B_534=A_535 | ~v1_xboole_0(B_534) | ~v1_xboole_0(A_535))), inference(resolution, [status(thm)], [c_333, c_365])).
% 8.38/2.99  tff(c_6171, plain, (![A_536]: (k1_xboole_0=A_536 | ~v1_xboole_0(A_536))), inference(resolution, [status(thm)], [c_12, c_6164])).
% 8.38/2.99  tff(c_6178, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_6078, c_6171])).
% 8.38/2.99  tff(c_6194, plain, (![B_13]: (k2_zfmisc_1('#skF_6', B_13)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_6178, c_6178, c_24])).
% 8.38/2.99  tff(c_20, plain, (![B_13, A_12]: (k1_xboole_0=B_13 | k1_xboole_0=A_12 | k2_zfmisc_1(A_12, B_13)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.38/2.99  tff(c_6006, plain, (k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0!='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_5986, c_20])).
% 8.38/2.99  tff(c_6238, plain, ('#skF_5'='#skF_6' | '#skF_6'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6178, c_6178, c_6178, c_6006])).
% 8.38/2.99  tff(c_6239, plain, ('#skF_6'='#skF_4'), inference(splitLeft, [status(thm)], [c_6238])).
% 8.38/2.99  tff(c_6195, plain, (![A_12]: (k2_zfmisc_1(A_12, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_6178, c_6178, c_22])).
% 8.38/2.99  tff(c_6385, plain, (![A_12]: (k2_zfmisc_1(A_12, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6239, c_6239, c_6195])).
% 8.38/2.99  tff(c_6254, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_6239, c_236])).
% 8.38/2.99  tff(c_6476, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_6385, c_6254])).
% 8.38/2.99  tff(c_6255, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6239, c_229])).
% 8.38/2.99  tff(c_6260, plain, (v1_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6239, c_86])).
% 8.38/2.99  tff(c_6259, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6239, c_80])).
% 8.38/2.99  tff(c_6185, plain, (![B_70]: ('#skF_3'('#skF_6', B_70)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_6178, c_6178, c_391])).
% 8.38/2.99  tff(c_6296, plain, (![B_70]: ('#skF_3'('#skF_4', B_70)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6239, c_6239, c_6185])).
% 8.38/2.99  tff(c_58, plain, (![A_31, B_32]: (v1_funct_2('#skF_3'(A_31, B_32), A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_120])).
% 8.38/2.99  tff(c_68, plain, (![A_31, B_32]: (m1_subset_1('#skF_3'(A_31, B_32), k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 8.38/2.99  tff(c_6499, plain, (![A_557, B_558, C_559]: (k1_relset_1(A_557, B_558, C_559)=k1_relat_1(C_559) | ~m1_subset_1(C_559, k1_zfmisc_1(k2_zfmisc_1(A_557, B_558))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 8.38/2.99  tff(c_6513, plain, (![A_31, B_32]: (k1_relset_1(A_31, B_32, '#skF_3'(A_31, B_32))=k1_relat_1('#skF_3'(A_31, B_32)))), inference(resolution, [status(thm)], [c_68, c_6499])).
% 8.38/2.99  tff(c_6245, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6239, c_6178])).
% 8.38/2.99  tff(c_56, plain, (![B_29, A_28, C_30]: (k1_xboole_0=B_29 | k1_relset_1(A_28, B_29, C_30)=A_28 | ~v1_funct_2(C_30, A_28, B_29) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 8.38/2.99  tff(c_6662, plain, (![B_577, A_578, C_579]: (B_577='#skF_4' | k1_relset_1(A_578, B_577, C_579)=A_578 | ~v1_funct_2(C_579, A_578, B_577) | ~m1_subset_1(C_579, k1_zfmisc_1(k2_zfmisc_1(A_578, B_577))))), inference(demodulation, [status(thm), theory('equality')], [c_6245, c_56])).
% 8.38/2.99  tff(c_6674, plain, (![B_32, A_31]: (B_32='#skF_4' | k1_relset_1(A_31, B_32, '#skF_3'(A_31, B_32))=A_31 | ~v1_funct_2('#skF_3'(A_31, B_32), A_31, B_32))), inference(resolution, [status(thm)], [c_68, c_6662])).
% 8.38/2.99  tff(c_6687, plain, (![B_580, A_581]: (B_580='#skF_4' | k1_relat_1('#skF_3'(A_581, B_580))=A_581)), inference(demodulation, [status(thm), theory('equality')], [c_58, c_6513, c_6674])).
% 8.38/2.99  tff(c_6705, plain, (![B_70]: (B_70='#skF_4' | k1_relat_1('#skF_4')='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_6296, c_6687])).
% 8.38/2.99  tff(c_6713, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(splitLeft, [status(thm)], [c_6705])).
% 8.38/2.99  tff(c_6256, plain, (v1_funct_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_6239, c_172])).
% 8.38/2.99  tff(c_6373, plain, (![A_549]: (k2_relat_1(k2_funct_1(A_549))=k1_relat_1(A_549) | ~v2_funct_1(A_549) | ~v1_funct_1(A_549) | ~v1_relat_1(A_549))), inference(cnfTransformation, [status(thm)], [f_77])).
% 8.38/2.99  tff(c_7521, plain, (![A_669]: (v1_funct_2(k2_funct_1(A_669), k1_relat_1(k2_funct_1(A_669)), k1_relat_1(A_669)) | ~v1_funct_1(k2_funct_1(A_669)) | ~v1_relat_1(k2_funct_1(A_669)) | ~v2_funct_1(A_669) | ~v1_funct_1(A_669) | ~v1_relat_1(A_669))), inference(superposition, [status(thm), theory('equality')], [c_6373, c_72])).
% 8.38/2.99  tff(c_7524, plain, (v1_funct_2(k2_funct_1('#skF_4'), k1_relat_1(k2_funct_1('#skF_4')), '#skF_4') | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_6713, c_7521])).
% 8.38/2.99  tff(c_7535, plain, (v1_funct_2(k2_funct_1('#skF_4'), k1_relat_1(k2_funct_1('#skF_4')), '#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_6255, c_6260, c_6259, c_6256, c_7524])).
% 8.38/2.99  tff(c_7538, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_7535])).
% 8.38/2.99  tff(c_7541, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_34, c_7538])).
% 8.38/2.99  tff(c_7545, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6255, c_6260, c_7541])).
% 8.38/2.99  tff(c_7547, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_7535])).
% 8.38/2.99  tff(c_6602, plain, (![A_570, B_571, C_572]: (k2_relset_1(A_570, B_571, C_572)=k2_relat_1(C_572) | ~m1_subset_1(C_572, k1_zfmisc_1(k2_zfmisc_1(A_570, B_571))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 8.38/2.99  tff(c_6763, plain, (![A_586, B_587]: (k2_relset_1(A_586, B_587, '#skF_3'(A_586, B_587))=k2_relat_1('#skF_3'(A_586, B_587)))), inference(resolution, [status(thm)], [c_68, c_6602])).
% 8.38/2.99  tff(c_6775, plain, (![B_70]: (k2_relat_1('#skF_3'('#skF_4', B_70))=k2_relset_1('#skF_4', B_70, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_6296, c_6763])).
% 8.38/2.99  tff(c_6787, plain, (![B_589]: (k2_relset_1('#skF_4', B_589, '#skF_4')=k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_6296, c_6775])).
% 8.38/2.99  tff(c_6257, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_6239, c_78])).
% 8.38/2.99  tff(c_6794, plain, (k2_relat_1('#skF_4')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_6787, c_6257])).
% 8.38/2.99  tff(c_6532, plain, (![A_561]: (m1_subset_1(A_561, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_561), k2_relat_1(A_561)))) | ~v1_funct_1(A_561) | ~v1_relat_1(A_561))), inference(cnfTransformation, [status(thm)], [f_130])).
% 8.38/2.99  tff(c_7861, plain, (![A_699]: (m1_subset_1(k2_funct_1(A_699), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_699), k2_relat_1(k2_funct_1(A_699))))) | ~v1_funct_1(k2_funct_1(A_699)) | ~v1_relat_1(k2_funct_1(A_699)) | ~v2_funct_1(A_699) | ~v1_funct_1(A_699) | ~v1_relat_1(A_699))), inference(superposition, [status(thm), theory('equality')], [c_38, c_6532])).
% 8.38/2.99  tff(c_7882, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', k2_relat_1(k2_funct_1('#skF_4'))))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_6794, c_7861])).
% 8.38/2.99  tff(c_7896, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', k2_relat_1(k2_funct_1('#skF_4')))))), inference(demodulation, [status(thm), theory('equality')], [c_6255, c_6260, c_6259, c_7547, c_6256, c_7882])).
% 8.38/2.99  tff(c_7936, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_relat_1('#skF_4')))) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_36, c_7896])).
% 8.38/2.99  tff(c_7948, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_6255, c_6260, c_6259, c_6385, c_6713, c_7936])).
% 8.38/2.99  tff(c_7950, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6476, c_7948])).
% 8.38/2.99  tff(c_7976, plain, (![B_705]: (B_705='#skF_4')), inference(splitRight, [status(thm)], [c_6705])).
% 8.38/2.99  tff(c_28, plain, (![A_14, B_15]: (m1_subset_1(A_14, k1_zfmisc_1(B_15)) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.38/2.99  tff(c_6480, plain, (~r1_tarski(k2_funct_1('#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_28, c_6476])).
% 8.38/2.99  tff(c_8012, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_7976, c_6480])).
% 8.38/2.99  tff(c_8088, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_8012])).
% 8.38/2.99  tff(c_8089, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_6238])).
% 8.38/2.99  tff(c_8094, plain, (~m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_8089, c_236])).
% 8.38/2.99  tff(c_8098, plain, (~m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_6194, c_8094])).
% 8.38/2.99  tff(c_231, plain, (![A_75]: (m1_subset_1('#skF_3'(A_75, k1_xboole_0), k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_195])).
% 8.38/2.99  tff(c_235, plain, (![A_75]: (r1_tarski('#skF_3'(A_75, k1_xboole_0), k1_xboole_0))), inference(resolution, [status(thm)], [c_231, c_26])).
% 8.38/2.99  tff(c_374, plain, (![A_75]: ('#skF_3'(A_75, k1_xboole_0)=k1_xboole_0 | ~v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_235, c_365])).
% 8.38/2.99  tff(c_388, plain, (![A_75]: ('#skF_3'(A_75, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_374])).
% 8.38/2.99  tff(c_6188, plain, (![A_75]: ('#skF_3'(A_75, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_6178, c_6178, c_388])).
% 8.38/2.99  tff(c_8507, plain, (![A_1732, B_1733, C_1734]: (k2_relset_1(A_1732, B_1733, C_1734)=k2_relat_1(C_1734) | ~m1_subset_1(C_1734, k1_zfmisc_1(k2_zfmisc_1(A_1732, B_1733))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 8.38/2.99  tff(c_8577, plain, (![A_1741, B_1742]: (k2_relset_1(A_1741, B_1742, '#skF_3'(A_1741, B_1742))=k2_relat_1('#skF_3'(A_1741, B_1742)))), inference(resolution, [status(thm)], [c_68, c_8507])).
% 8.38/2.99  tff(c_8589, plain, (![A_75]: (k2_relat_1('#skF_3'(A_75, '#skF_6'))=k2_relset_1(A_75, '#skF_6', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_6188, c_8577])).
% 8.38/2.99  tff(c_8622, plain, (![A_1746]: (k2_relset_1(A_1746, '#skF_6', '#skF_6')=k2_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_6188, c_8589])).
% 8.38/2.99  tff(c_8095, plain, (k2_relset_1('#skF_4', '#skF_6', '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_8089, c_8089, c_78])).
% 8.38/2.99  tff(c_8629, plain, (k2_relat_1('#skF_6')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_8622, c_8095])).
% 8.38/2.99  tff(c_8103, plain, (![A_1701]: (k1_relat_1(k2_funct_1(A_1701))=k2_relat_1(A_1701) | ~v2_funct_1(A_1701) | ~v1_funct_1(A_1701) | ~v1_relat_1(A_1701))), inference(cnfTransformation, [status(thm)], [f_77])).
% 8.38/2.99  tff(c_9335, plain, (![A_1824]: (v1_funct_2(k2_funct_1(A_1824), k2_relat_1(A_1824), k2_relat_1(k2_funct_1(A_1824))) | ~v1_funct_1(k2_funct_1(A_1824)) | ~v1_relat_1(k2_funct_1(A_1824)) | ~v2_funct_1(A_1824) | ~v1_funct_1(A_1824) | ~v1_relat_1(A_1824))), inference(superposition, [status(thm), theory('equality')], [c_8103, c_72])).
% 8.38/2.99  tff(c_9338, plain, (v1_funct_2(k2_funct_1('#skF_6'), '#skF_6', k2_relat_1(k2_funct_1('#skF_6'))) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')) | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_8629, c_9335])).
% 8.38/2.99  tff(c_9346, plain, (v1_funct_2(k2_funct_1('#skF_6'), '#skF_6', k2_relat_1(k2_funct_1('#skF_6'))) | ~v1_relat_1(k2_funct_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_229, c_86, c_80, c_172, c_9338])).
% 8.38/2.99  tff(c_9347, plain, (~v1_relat_1(k2_funct_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_9346])).
% 8.38/2.99  tff(c_9350, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_34, c_9347])).
% 8.38/2.99  tff(c_9354, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_229, c_86, c_9350])).
% 8.38/2.99  tff(c_9356, plain, (v1_relat_1(k2_funct_1('#skF_6'))), inference(splitRight, [status(thm)], [c_9346])).
% 8.38/2.99  tff(c_8434, plain, (![A_1727, B_1728, C_1729]: (k1_relset_1(A_1727, B_1728, C_1729)=k1_relat_1(C_1729) | ~m1_subset_1(C_1729, k1_zfmisc_1(k2_zfmisc_1(A_1727, B_1728))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 8.38/2.99  tff(c_8452, plain, (![A_31, B_32]: (k1_relset_1(A_31, B_32, '#skF_3'(A_31, B_32))=k1_relat_1('#skF_3'(A_31, B_32)))), inference(resolution, [status(thm)], [c_68, c_8434])).
% 8.38/2.99  tff(c_8757, plain, (![B_1764, A_1765, C_1766]: (B_1764='#skF_6' | k1_relset_1(A_1765, B_1764, C_1766)=A_1765 | ~v1_funct_2(C_1766, A_1765, B_1764) | ~m1_subset_1(C_1766, k1_zfmisc_1(k2_zfmisc_1(A_1765, B_1764))))), inference(demodulation, [status(thm), theory('equality')], [c_6178, c_56])).
% 8.38/2.99  tff(c_8769, plain, (![B_32, A_31]: (B_32='#skF_6' | k1_relset_1(A_31, B_32, '#skF_3'(A_31, B_32))=A_31 | ~v1_funct_2('#skF_3'(A_31, B_32), A_31, B_32))), inference(resolution, [status(thm)], [c_68, c_8757])).
% 8.38/2.99  tff(c_8782, plain, (![B_1767, A_1768]: (B_1767='#skF_6' | k1_relat_1('#skF_3'(A_1768, B_1767))=A_1768)), inference(demodulation, [status(thm), theory('equality')], [c_58, c_8452, c_8769])).
% 8.38/2.99  tff(c_8797, plain, (![B_70]: (B_70='#skF_6' | k1_relat_1('#skF_6')='#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_6185, c_8782])).
% 8.38/2.99  tff(c_8808, plain, (k1_relat_1('#skF_6')='#skF_6'), inference(splitLeft, [status(thm)], [c_8797])).
% 8.38/2.99  tff(c_8318, plain, (![A_1711]: (m1_subset_1(A_1711, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_1711), k2_relat_1(A_1711)))) | ~v1_funct_1(A_1711) | ~v1_relat_1(A_1711))), inference(cnfTransformation, [status(thm)], [f_130])).
% 8.38/2.99  tff(c_9693, plain, (![A_1854]: (m1_subset_1(k2_funct_1(A_1854), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_1854)), k1_relat_1(A_1854)))) | ~v1_funct_1(k2_funct_1(A_1854)) | ~v1_relat_1(k2_funct_1(A_1854)) | ~v2_funct_1(A_1854) | ~v1_funct_1(A_1854) | ~v1_relat_1(A_1854))), inference(superposition, [status(thm), theory('equality')], [c_36, c_8318])).
% 8.38/2.99  tff(c_9714, plain, (m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_6')), '#skF_6'))) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')) | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_8808, c_9693])).
% 8.38/2.99  tff(c_9731, plain, (m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_229, c_86, c_80, c_9356, c_172, c_6195, c_9714])).
% 8.38/2.99  tff(c_9733, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8098, c_9731])).
% 8.38/2.99  tff(c_9736, plain, (![B_1855]: (B_1855='#skF_6')), inference(splitRight, [status(thm)], [c_8797])).
% 8.38/2.99  tff(c_9819, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_9736, c_8098])).
% 8.38/2.99  tff(c_9937, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5989, c_9819])).
% 8.38/2.99  tff(c_9938, plain, (~v1_funct_2(k2_funct_1('#skF_6'), '#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_171])).
% 8.38/2.99  tff(c_9939, plain, (m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4')))), inference(splitRight, [status(thm)], [c_171])).
% 8.38/2.99  tff(c_10603, plain, (![A_3097, B_3098, C_3099]: (k1_relset_1(A_3097, B_3098, C_3099)=k1_relat_1(C_3099) | ~m1_subset_1(C_3099, k1_zfmisc_1(k2_zfmisc_1(A_3097, B_3098))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 8.38/2.99  tff(c_10631, plain, (k1_relset_1('#skF_5', '#skF_4', k2_funct_1('#skF_6'))=k1_relat_1(k2_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_9939, c_10603])).
% 8.38/2.99  tff(c_11030, plain, (![B_3140, C_3141, A_3142]: (k1_xboole_0=B_3140 | v1_funct_2(C_3141, A_3142, B_3140) | k1_relset_1(A_3142, B_3140, C_3141)!=A_3142 | ~m1_subset_1(C_3141, k1_zfmisc_1(k2_zfmisc_1(A_3142, B_3140))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 8.38/2.99  tff(c_11036, plain, (k1_xboole_0='#skF_4' | v1_funct_2(k2_funct_1('#skF_6'), '#skF_5', '#skF_4') | k1_relset_1('#skF_5', '#skF_4', k2_funct_1('#skF_6'))!='#skF_5'), inference(resolution, [status(thm)], [c_9939, c_11030])).
% 8.38/2.99  tff(c_11055, plain, (k1_xboole_0='#skF_4' | v1_funct_2(k2_funct_1('#skF_6'), '#skF_5', '#skF_4') | k1_relat_1(k2_funct_1('#skF_6'))!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_10631, c_11036])).
% 8.38/2.99  tff(c_11056, plain, (k1_xboole_0='#skF_4' | k1_relat_1(k2_funct_1('#skF_6'))!='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_9938, c_11055])).
% 8.38/3.00  tff(c_11064, plain, (k1_relat_1(k2_funct_1('#skF_6'))!='#skF_5'), inference(splitLeft, [status(thm)], [c_11056])).
% 8.38/3.00  tff(c_11067, plain, (k2_relat_1('#skF_6')!='#skF_5' | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_38, c_11064])).
% 8.38/3.00  tff(c_11070, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_229, c_86, c_80, c_10545, c_11067])).
% 8.38/3.00  tff(c_11071, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_11056])).
% 8.38/3.00  tff(c_11113, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11071, c_12])).
% 8.38/3.00  tff(c_11111, plain, (![B_13]: (k2_zfmisc_1('#skF_4', B_13)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11071, c_11071, c_24])).
% 8.38/3.00  tff(c_10016, plain, (![A_3039, B_3040]: (r2_hidden('#skF_2'(A_3039, B_3040), A_3039) | r1_tarski(A_3039, B_3040))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.38/3.00  tff(c_10026, plain, (![A_3039, B_3040]: (~v1_xboole_0(A_3039) | r1_tarski(A_3039, B_3040))), inference(resolution, [status(thm)], [c_10016, c_2])).
% 8.38/3.00  tff(c_10051, plain, (![B_3046, A_3047]: (B_3046=A_3047 | ~r1_tarski(B_3046, A_3047) | ~r1_tarski(A_3047, B_3046))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.38/3.00  tff(c_10083, plain, (![B_3051, A_3052]: (B_3051=A_3052 | ~r1_tarski(B_3051, A_3052) | ~v1_xboole_0(A_3052))), inference(resolution, [status(thm)], [c_10026, c_10051])).
% 8.38/3.00  tff(c_10114, plain, (k2_zfmisc_1('#skF_4', '#skF_5')='#skF_6' | ~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_177, c_10083])).
% 8.38/3.00  tff(c_10157, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_10114])).
% 8.38/3.00  tff(c_11165, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11111, c_10157])).
% 8.38/3.00  tff(c_11170, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11113, c_11165])).
% 8.38/3.00  tff(c_11171, plain, (k2_zfmisc_1('#skF_4', '#skF_5')='#skF_6'), inference(splitRight, [status(thm)], [c_10114])).
% 8.38/3.00  tff(c_10071, plain, (k2_zfmisc_1('#skF_4', '#skF_5')='#skF_6' | ~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), '#skF_6')), inference(resolution, [status(thm)], [c_177, c_10051])).
% 8.38/3.00  tff(c_11227, plain, (~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), '#skF_6')), inference(splitLeft, [status(thm)], [c_10071])).
% 8.38/3.00  tff(c_11275, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_11171, c_11227])).
% 8.38/3.00  tff(c_11276, plain, (k2_zfmisc_1('#skF_4', '#skF_5')='#skF_6'), inference(splitRight, [status(thm)], [c_10071])).
% 8.38/3.00  tff(c_11298, plain, (k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0!='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_11276, c_20])).
% 8.38/3.00  tff(c_11397, plain, (k1_xboole_0!='#skF_6'), inference(splitLeft, [status(thm)], [c_11298])).
% 8.38/3.00  tff(c_11172, plain, (v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_10114])).
% 8.38/3.00  tff(c_11309, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_11276, c_11172])).
% 8.38/3.00  tff(c_11390, plain, (![B_3155, A_3156]: (B_3155=A_3156 | ~v1_xboole_0(B_3155) | ~v1_xboole_0(A_3156))), inference(resolution, [status(thm)], [c_10026, c_10083])).
% 8.38/3.00  tff(c_11398, plain, (![A_3157]: (A_3157='#skF_6' | ~v1_xboole_0(A_3157))), inference(resolution, [status(thm)], [c_11309, c_11390])).
% 8.38/3.00  tff(c_11404, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_12, c_11398])).
% 8.38/3.00  tff(c_11410, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11397, c_11404])).
% 8.38/3.00  tff(c_11412, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_11298])).
% 8.38/3.00  tff(c_10098, plain, (![B_70]: ('#skF_3'(k1_xboole_0, B_70)=k1_xboole_0 | ~v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_210, c_10083])).
% 8.38/3.00  tff(c_11188, plain, (![B_3144]: ('#skF_3'(k1_xboole_0, B_3144)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_10098])).
% 8.38/3.00  tff(c_11202, plain, (![B_3144]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_3144))), inference(superposition, [status(thm), theory('equality')], [c_11188, c_58])).
% 8.38/3.00  tff(c_11414, plain, (![B_3144]: (v1_funct_2('#skF_6', '#skF_6', B_3144))), inference(demodulation, [status(thm), theory('equality')], [c_11412, c_11412, c_11202])).
% 8.38/3.00  tff(c_11425, plain, (![B_13]: (k2_zfmisc_1('#skF_6', B_13)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_11412, c_11412, c_24])).
% 8.38/3.00  tff(c_11411, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_11298])).
% 8.38/3.00  tff(c_11533, plain, ('#skF_6'='#skF_4' | '#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_11412, c_11412, c_11411])).
% 8.38/3.00  tff(c_11534, plain, ('#skF_5'='#skF_6'), inference(splitLeft, [status(thm)], [c_11533])).
% 8.38/3.00  tff(c_9948, plain, (r1_tarski(k2_funct_1('#skF_6'), k2_zfmisc_1('#skF_5', '#skF_4'))), inference(resolution, [status(thm)], [c_9939, c_26])).
% 8.38/3.00  tff(c_11537, plain, (r1_tarski(k2_funct_1('#skF_6'), k2_zfmisc_1('#skF_6', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_11534, c_9948])).
% 8.38/3.00  tff(c_11544, plain, (r1_tarski(k2_funct_1('#skF_6'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_11425, c_11537])).
% 8.38/3.00  tff(c_10066, plain, (![B_3040, A_3039]: (B_3040=A_3039 | ~r1_tarski(B_3040, A_3039) | ~v1_xboole_0(A_3039))), inference(resolution, [status(thm)], [c_10026, c_10051])).
% 8.38/3.00  tff(c_11595, plain, (k2_funct_1('#skF_6')='#skF_6' | ~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_11544, c_10066])).
% 8.38/3.00  tff(c_11602, plain, (k2_funct_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_11309, c_11595])).
% 8.38/3.00  tff(c_11539, plain, (~v1_funct_2(k2_funct_1('#skF_6'), '#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11534, c_9938])).
% 8.38/3.00  tff(c_11694, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11414, c_11602, c_11539])).
% 8.38/3.00  tff(c_11695, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_11533])).
% 8.38/3.00  tff(c_10095, plain, (![A_75]: ('#skF_3'(A_75, k1_xboole_0)=k1_xboole_0 | ~v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_235, c_10083])).
% 8.38/3.00  tff(c_10110, plain, (![A_75]: ('#skF_3'(A_75, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_10095])).
% 8.38/3.00  tff(c_11419, plain, (![A_75]: ('#skF_3'(A_75, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_11412, c_11412, c_10110])).
% 8.38/3.00  tff(c_11777, plain, (![A_3174]: ('#skF_3'(A_3174, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11695, c_11695, c_11419])).
% 8.38/3.00  tff(c_11788, plain, (![A_3174]: (v1_funct_2('#skF_4', A_3174, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_11777, c_58])).
% 8.38/3.00  tff(c_11706, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11695, c_11309])).
% 8.38/3.00  tff(c_11426, plain, (![A_12]: (k2_zfmisc_1(A_12, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_11412, c_11412, c_22])).
% 8.38/3.00  tff(c_11699, plain, (![A_12]: (k2_zfmisc_1(A_12, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11695, c_11695, c_11426])).
% 8.38/3.00  tff(c_11711, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_11695, c_9939])).
% 8.38/3.00  tff(c_11989, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_11699, c_11711])).
% 8.38/3.00  tff(c_11993, plain, (r1_tarski(k2_funct_1('#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_11989, c_26])).
% 8.38/3.00  tff(c_11999, plain, (k2_funct_1('#skF_4')='#skF_4' | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_11993, c_10066])).
% 8.38/3.00  tff(c_12006, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_11706, c_11999])).
% 8.38/3.00  tff(c_11712, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11695, c_9938])).
% 8.38/3.00  tff(c_12010, plain, (~v1_funct_2('#skF_4', '#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_12006, c_11712])).
% 8.38/3.00  tff(c_12017, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11788, c_12010])).
% 8.38/3.00  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.38/3.00  
% 8.38/3.00  Inference rules
% 8.38/3.00  ----------------------
% 8.38/3.00  #Ref     : 0
% 8.38/3.00  #Sup     : 2681
% 8.38/3.00  #Fact    : 0
% 8.38/3.00  #Define  : 0
% 8.38/3.00  #Split   : 38
% 8.38/3.00  #Chain   : 0
% 8.38/3.00  #Close   : 0
% 8.38/3.00  
% 8.38/3.00  Ordering : KBO
% 8.38/3.00  
% 8.38/3.00  Simplification rules
% 8.38/3.00  ----------------------
% 8.38/3.00  #Subsume      : 479
% 8.38/3.00  #Demod        : 2901
% 8.38/3.00  #Tautology    : 1466
% 8.38/3.00  #SimpNegUnit  : 54
% 8.38/3.00  #BackRed      : 384
% 8.38/3.00  
% 8.38/3.00  #Partial instantiations: 69
% 8.38/3.00  #Strategies tried      : 1
% 8.38/3.00  
% 8.38/3.00  Timing (in seconds)
% 8.38/3.00  ----------------------
% 8.38/3.00  Preprocessing        : 0.33
% 8.38/3.00  Parsing              : 0.17
% 8.38/3.00  CNF conversion       : 0.02
% 8.38/3.00  Main loop            : 1.83
% 8.38/3.00  Inferencing          : 0.63
% 8.38/3.00  Reduction            : 0.64
% 8.38/3.00  Demodulation         : 0.47
% 8.38/3.00  BG Simplification    : 0.06
% 8.38/3.00  Subsumption          : 0.35
% 8.38/3.00  Abstraction          : 0.08
% 8.38/3.00  MUC search           : 0.00
% 8.38/3.00  Cooper               : 0.00
% 8.38/3.00  Total                : 2.26
% 8.38/3.00  Index Insertion      : 0.00
% 8.38/3.00  Index Deletion       : 0.00
% 8.38/3.00  Index Matching       : 0.00
% 8.38/3.00  BG Taut test         : 0.00
%------------------------------------------------------------------------------
