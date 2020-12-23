%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:43 EST 2020

% Result     : Theorem 7.63s
% Output     : CNFRefutation 8.02s
% Verified   : 
% Statistics : Number of formulae       :  348 (5280 expanded)
%              Number of leaves         :   43 (1672 expanded)
%              Depth                    :   19
%              Number of atoms          :  589 (13722 expanded)
%              Number of equality atoms :  218 (4794 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   1 average)

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

tff(f_151,negated_conjecture,(
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

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_81,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_71,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_134,axiom,(
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

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_124,axiom,(
    ! [A,B] :
    ? [C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
      & v1_relat_1(C)
      & v4_relat_1(C,A)
      & v5_relat_1(C,B)
      & v1_funct_1(C)
      & v1_funct_2(C,A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_funct_2)).

tff(c_18,plain,(
    ! [B_11] : r1_tarski(B_11,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_84,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_7746,plain,(
    ! [C_738,A_739,B_740] :
      ( v1_relat_1(C_738)
      | ~ m1_subset_1(C_738,k1_zfmisc_1(k2_zfmisc_1(A_739,B_740))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_7768,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_84,c_7746])).

tff(c_88,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_82,plain,(
    v2_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_80,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_8252,plain,(
    ! [A_799,B_800,C_801] :
      ( k2_relset_1(A_799,B_800,C_801) = k2_relat_1(C_801)
      | ~ m1_subset_1(C_801,k1_zfmisc_1(k2_zfmisc_1(A_799,B_800))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_8268,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_84,c_8252])).

tff(c_8280,plain,(
    k2_relat_1('#skF_6') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_8268])).

tff(c_40,plain,(
    ! [A_18] :
      ( k1_relat_1(k2_funct_1(A_18)) = k2_relat_1(A_18)
      | ~ v2_funct_1(A_18)
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_148,plain,(
    ! [A_56] :
      ( v1_funct_1(k2_funct_1(A_56))
      | ~ v1_funct_1(A_56)
      | ~ v1_relat_1(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_78,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4')))
    | ~ v1_funct_2(k2_funct_1('#skF_6'),'#skF_5','#skF_4')
    | ~ v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_147,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_151,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_148,c_147])).

tff(c_154,plain,(
    ~ v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_151])).

tff(c_169,plain,(
    ! [C_59,A_60,B_61] :
      ( v1_relat_1(C_59)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_176,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_84,c_169])).

tff(c_185,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_154,c_176])).

tff(c_186,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_6'),'#skF_5','#skF_4')
    | ~ m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_188,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_186])).

tff(c_225,plain,(
    ! [C_71,A_72,B_73] :
      ( v1_relat_1(C_71)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_238,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_84,c_225])).

tff(c_741,plain,(
    ! [A_136,B_137,C_138] :
      ( k2_relset_1(A_136,B_137,C_138) = k2_relat_1(C_138)
      | ~ m1_subset_1(C_138,k1_zfmisc_1(k2_zfmisc_1(A_136,B_137))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_751,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_84,c_741])).

tff(c_761,plain,(
    k2_relat_1('#skF_6') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_751])).

tff(c_30,plain,(
    ! [A_16] :
      ( k2_relat_1(A_16) != k1_xboole_0
      | k1_xboole_0 = A_16
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_245,plain,
    ( k2_relat_1('#skF_6') != k1_xboole_0
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_238,c_30])).

tff(c_247,plain,(
    k2_relat_1('#skF_6') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_245])).

tff(c_762,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_761,c_247])).

tff(c_86,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_851,plain,(
    ! [A_146,B_147,C_148] :
      ( k1_relset_1(A_146,B_147,C_148) = k1_relat_1(C_148)
      | ~ m1_subset_1(C_148,k1_zfmisc_1(k2_zfmisc_1(A_146,B_147))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_870,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_84,c_851])).

tff(c_1194,plain,(
    ! [B_181,A_182,C_183] :
      ( k1_xboole_0 = B_181
      | k1_relset_1(A_182,B_181,C_183) = A_182
      | ~ v1_funct_2(C_183,A_182,B_181)
      | ~ m1_subset_1(C_183,k1_zfmisc_1(k2_zfmisc_1(A_182,B_181))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_1210,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_84,c_1194])).

tff(c_1228,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_870,c_1210])).

tff(c_1229,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_762,c_1228])).

tff(c_38,plain,(
    ! [A_18] :
      ( k2_relat_1(k2_funct_1(A_18)) = k1_relat_1(A_18)
      | ~ v2_funct_1(A_18)
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_36,plain,(
    ! [A_17] :
      ( v1_relat_1(k2_funct_1(A_17))
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_187,plain,(
    v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_621,plain,(
    ! [A_119] :
      ( k1_relat_1(k2_funct_1(A_119)) = k2_relat_1(A_119)
      | ~ v2_funct_1(A_119)
      | ~ v1_funct_1(A_119)
      | ~ v1_relat_1(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_74,plain,(
    ! [A_34] :
      ( v1_funct_2(A_34,k1_relat_1(A_34),k2_relat_1(A_34))
      | ~ v1_funct_1(A_34)
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_2569,plain,(
    ! [A_275] :
      ( v1_funct_2(k2_funct_1(A_275),k2_relat_1(A_275),k2_relat_1(k2_funct_1(A_275)))
      | ~ v1_funct_1(k2_funct_1(A_275))
      | ~ v1_relat_1(k2_funct_1(A_275))
      | ~ v2_funct_1(A_275)
      | ~ v1_funct_1(A_275)
      | ~ v1_relat_1(A_275) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_621,c_74])).

tff(c_2575,plain,
    ( v1_funct_2(k2_funct_1('#skF_6'),'#skF_5',k2_relat_1(k2_funct_1('#skF_6')))
    | ~ v1_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6'))
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_761,c_2569])).

tff(c_2585,plain,
    ( v1_funct_2(k2_funct_1('#skF_6'),'#skF_5',k2_relat_1(k2_funct_1('#skF_6')))
    | ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_238,c_88,c_82,c_187,c_2575])).

tff(c_2586,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_2585])).

tff(c_2589,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_36,c_2586])).

tff(c_2593,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_238,c_88,c_2589])).

tff(c_2595,plain,(
    v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_2585])).

tff(c_899,plain,(
    ! [A_153] :
      ( m1_subset_1(A_153,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_153),k2_relat_1(A_153))))
      | ~ v1_funct_1(A_153)
      | ~ v1_relat_1(A_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_3134,plain,(
    ! [A_312] :
      ( m1_subset_1(k2_funct_1(A_312),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_312),k2_relat_1(k2_funct_1(A_312)))))
      | ~ v1_funct_1(k2_funct_1(A_312))
      | ~ v1_relat_1(k2_funct_1(A_312))
      | ~ v2_funct_1(A_312)
      | ~ v1_funct_1(A_312)
      | ~ v1_relat_1(A_312) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_899])).

tff(c_3158,plain,
    ( m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_5',k2_relat_1(k2_funct_1('#skF_6')))))
    | ~ v1_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6'))
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_761,c_3134])).

tff(c_3174,plain,(
    m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_5',k2_relat_1(k2_funct_1('#skF_6'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_238,c_88,c_82,c_2595,c_187,c_3158])).

tff(c_3195,plain,
    ( m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_relat_1('#skF_6'))))
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_3174])).

tff(c_3209,plain,(
    m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_238,c_88,c_82,c_1229,c_3195])).

tff(c_3211,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_188,c_3209])).

tff(c_3212,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_245])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_3218,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3212,c_12])).

tff(c_22,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_3217,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3212,c_3212,c_22])).

tff(c_3213,plain,(
    k2_relat_1('#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_245])).

tff(c_3224,plain,(
    k2_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3212,c_3213])).

tff(c_3759,plain,(
    ! [A_372,B_373,C_374] :
      ( k2_relset_1(A_372,B_373,C_374) = k2_relat_1(C_374)
      | ~ m1_subset_1(C_374,k1_zfmisc_1(k2_zfmisc_1(A_372,B_373))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_3778,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_84,c_3759])).

tff(c_3783,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3224,c_80,c_3778])).

tff(c_208,plain,(
    ! [A_65,B_66] :
      ( r2_hidden('#skF_2'(A_65,B_66),A_65)
      | r1_tarski(A_65,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_212,plain,(
    ! [A_65,B_66] :
      ( ~ v1_xboole_0(A_65)
      | r1_tarski(A_65,B_66) ) ),
    inference(resolution,[status(thm)],[c_208,c_2])).

tff(c_138,plain,(
    ! [A_54,B_55] :
      ( r1_tarski(A_54,B_55)
      | ~ m1_subset_1(A_54,k1_zfmisc_1(B_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_146,plain,(
    r1_tarski('#skF_6',k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_84,c_138])).

tff(c_3274,plain,(
    ! [B_317,A_318] :
      ( B_317 = A_318
      | ~ r1_tarski(B_317,A_318)
      | ~ r1_tarski(A_318,B_317) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_3282,plain,
    ( k2_zfmisc_1('#skF_4','#skF_5') = '#skF_6'
    | ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_146,c_3274])).

tff(c_3294,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_3282])).

tff(c_3298,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_212,c_3294])).

tff(c_3785,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3783,c_3298])).

tff(c_3795,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3218,c_3217,c_3785])).

tff(c_3796,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_3282])).

tff(c_3799,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3796,c_84])).

tff(c_24,plain,(
    ! [B_13] : k2_zfmisc_1(k1_xboole_0,B_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_3216,plain,(
    ! [B_13] : k2_zfmisc_1('#skF_6',B_13) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3212,c_3212,c_24])).

tff(c_3818,plain,(
    ! [A_375,B_376] : m1_subset_1('#skF_3'(A_375,B_376),k1_zfmisc_1(k2_zfmisc_1(A_375,B_376))) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_3854,plain,(
    ! [B_377] : m1_subset_1('#skF_3'('#skF_6',B_377),k1_zfmisc_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3216,c_3818])).

tff(c_26,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(A_14,B_15)
      | ~ m1_subset_1(A_14,k1_zfmisc_1(B_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_3863,plain,(
    ! [B_377] : r1_tarski('#skF_3'('#skF_6',B_377),'#skF_6') ),
    inference(resolution,[status(thm)],[c_3854,c_26])).

tff(c_6062,plain,(
    ! [B_569,A_570] :
      ( B_569 = A_570
      | ~ r1_tarski(B_569,A_570)
      | ~ v1_xboole_0(A_570) ) ),
    inference(resolution,[status(thm)],[c_212,c_3274])).

tff(c_6071,plain,(
    ! [B_377] :
      ( '#skF_3'('#skF_6',B_377) = '#skF_6'
      | ~ v1_xboole_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_3863,c_6062])).

tff(c_6084,plain,(
    ! [B_377] : '#skF_3'('#skF_6',B_377) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3218,c_6071])).

tff(c_70,plain,(
    ! [A_31,B_32] : m1_subset_1('#skF_3'(A_31,B_32),k1_zfmisc_1(k2_zfmisc_1(A_31,B_32))) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_6330,plain,(
    ! [A_595,B_596,C_597] :
      ( k1_relset_1(A_595,B_596,C_597) = k1_relat_1(C_597)
      | ~ m1_subset_1(C_597,k1_zfmisc_1(k2_zfmisc_1(A_595,B_596))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_6394,plain,(
    ! [A_605,B_606] : k1_relset_1(A_605,B_606,'#skF_3'(A_605,B_606)) = k1_relat_1('#skF_3'(A_605,B_606)) ),
    inference(resolution,[status(thm)],[c_70,c_6330])).

tff(c_6403,plain,(
    ! [B_377] : k1_relat_1('#skF_3'('#skF_6',B_377)) = k1_relset_1('#skF_6',B_377,'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_6084,c_6394])).

tff(c_6409,plain,(
    ! [B_377] : k1_relset_1('#skF_6',B_377,'#skF_6') = k1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6084,c_6403])).

tff(c_60,plain,(
    ! [A_31,B_32] : v1_funct_2('#skF_3'(A_31,B_32),A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_56,plain,(
    ! [B_29,C_30] :
      ( k1_relset_1(k1_xboole_0,B_29,C_30) = k1_xboole_0
      | ~ v1_funct_2(C_30,k1_xboole_0,B_29)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_89,plain,(
    ! [B_29,C_30] :
      ( k1_relset_1(k1_xboole_0,B_29,C_30) = k1_xboole_0
      | ~ v1_funct_2(C_30,k1_xboole_0,B_29)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_56])).

tff(c_6553,plain,(
    ! [B_626,C_627] :
      ( k1_relset_1('#skF_6',B_626,C_627) = '#skF_6'
      | ~ v1_funct_2(C_627,'#skF_6',B_626)
      | ~ m1_subset_1(C_627,k1_zfmisc_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3212,c_3212,c_3212,c_3212,c_89])).

tff(c_6561,plain,(
    ! [B_32] :
      ( k1_relset_1('#skF_6',B_32,'#skF_3'('#skF_6',B_32)) = '#skF_6'
      | ~ m1_subset_1('#skF_3'('#skF_6',B_32),k1_zfmisc_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_60,c_6553])).

tff(c_6570,plain,(
    k1_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3799,c_6084,c_6409,c_6084,c_6561])).

tff(c_6200,plain,(
    ! [A_580] :
      ( k2_relat_1(k2_funct_1(A_580)) = k1_relat_1(A_580)
      | ~ v2_funct_1(A_580)
      | ~ v1_funct_1(A_580)
      | ~ v1_relat_1(A_580) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_7447,plain,(
    ! [A_710] :
      ( v1_funct_2(k2_funct_1(A_710),k1_relat_1(k2_funct_1(A_710)),k1_relat_1(A_710))
      | ~ v1_funct_1(k2_funct_1(A_710))
      | ~ v1_relat_1(k2_funct_1(A_710))
      | ~ v2_funct_1(A_710)
      | ~ v1_funct_1(A_710)
      | ~ v1_relat_1(A_710) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6200,c_74])).

tff(c_7453,plain,
    ( v1_funct_2(k2_funct_1('#skF_6'),k1_relat_1(k2_funct_1('#skF_6')),'#skF_6')
    | ~ v1_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6'))
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_6570,c_7447])).

tff(c_7463,plain,
    ( v1_funct_2(k2_funct_1('#skF_6'),k1_relat_1(k2_funct_1('#skF_6')),'#skF_6')
    | ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_238,c_88,c_82,c_187,c_7453])).

tff(c_7464,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_7463])).

tff(c_7467,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_36,c_7464])).

tff(c_7471,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_238,c_88,c_7467])).

tff(c_7473,plain,(
    v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_7463])).

tff(c_3214,plain,(
    ! [A_16] :
      ( k2_relat_1(A_16) != '#skF_6'
      | A_16 = '#skF_6'
      | ~ v1_relat_1(A_16) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3212,c_3212,c_30])).

tff(c_7481,plain,
    ( k2_relat_1(k2_funct_1('#skF_6')) != '#skF_6'
    | k2_funct_1('#skF_6') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_7473,c_3214])).

tff(c_7515,plain,(
    k2_relat_1(k2_funct_1('#skF_6')) != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_7481])).

tff(c_7518,plain,
    ( k1_relat_1('#skF_6') != '#skF_6'
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_7515])).

tff(c_7521,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_238,c_88,c_82,c_6570,c_7518])).

tff(c_7522,plain,(
    k2_funct_1('#skF_6') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_7481])).

tff(c_20,plain,(
    ! [B_13,A_12] :
      ( k1_xboole_0 = B_13
      | k1_xboole_0 = A_12
      | k2_zfmisc_1(A_12,B_13) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_3912,plain,(
    ! [B_379,A_380] :
      ( B_379 = '#skF_6'
      | A_380 = '#skF_6'
      | k2_zfmisc_1(A_380,B_379) != '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3212,c_3212,c_3212,c_20])).

tff(c_3922,plain,
    ( '#skF_5' = '#skF_6'
    | '#skF_6' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_3796,c_3912])).

tff(c_3927,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_3922])).

tff(c_3940,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3927,c_3218])).

tff(c_3937,plain,(
    ! [B_13] : k2_zfmisc_1('#skF_4',B_13) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3927,c_3927,c_3216])).

tff(c_4061,plain,(
    ! [B_377] : r1_tarski('#skF_3'('#skF_4',B_377),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3927,c_3927,c_3863])).

tff(c_4202,plain,(
    ! [B_403,A_404] :
      ( B_403 = A_404
      | ~ r1_tarski(B_403,A_404)
      | ~ v1_xboole_0(A_404) ) ),
    inference(resolution,[status(thm)],[c_212,c_3274])).

tff(c_4211,plain,(
    ! [B_377] :
      ( '#skF_3'('#skF_4',B_377) = '#skF_4'
      | ~ v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_4061,c_4202])).

tff(c_4224,plain,(
    ! [B_377] : '#skF_3'('#skF_4',B_377) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3940,c_4211])).

tff(c_3836,plain,(
    ! [A_375,B_376] : r1_tarski('#skF_3'(A_375,B_376),k2_zfmisc_1(A_375,B_376)) ),
    inference(resolution,[status(thm)],[c_3818,c_26])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_3968,plain,(
    ! [C_381,B_382,A_383] :
      ( r2_hidden(C_381,B_382)
      | ~ r2_hidden(C_381,A_383)
      | ~ r1_tarski(A_383,B_382) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_4873,plain,(
    ! [A_468,B_469,B_470] :
      ( r2_hidden('#skF_2'(A_468,B_469),B_470)
      | ~ r1_tarski(A_468,B_470)
      | r1_tarski(A_468,B_469) ) ),
    inference(resolution,[status(thm)],[c_10,c_3968])).

tff(c_4886,plain,(
    ! [B_471,A_472,B_473] :
      ( ~ v1_xboole_0(B_471)
      | ~ r1_tarski(A_472,B_471)
      | r1_tarski(A_472,B_473) ) ),
    inference(resolution,[status(thm)],[c_4873,c_2])).

tff(c_4896,plain,(
    ! [A_474,B_475,B_476] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_474,B_475))
      | r1_tarski('#skF_3'(A_474,B_475),B_476) ) ),
    inference(resolution,[status(thm)],[c_3836,c_4886])).

tff(c_4920,plain,(
    ! [B_377,B_476] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_4',B_377))
      | r1_tarski('#skF_4',B_476) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4224,c_4896])).

tff(c_4933,plain,(
    ! [B_476] : r1_tarski('#skF_4',B_476) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3940,c_3937,c_4920])).

tff(c_3942,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3927,c_238])).

tff(c_3950,plain,(
    v1_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3927,c_88])).

tff(c_3949,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3927,c_82])).

tff(c_3939,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3927,c_3927,c_3224])).

tff(c_3946,plain,(
    v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3927,c_187])).

tff(c_4133,plain,(
    ! [A_394] :
      ( k1_relat_1(k2_funct_1(A_394)) = k2_relat_1(A_394)
      | ~ v2_funct_1(A_394)
      | ~ v1_funct_1(A_394)
      | ~ v1_relat_1(A_394) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_5750,plain,(
    ! [A_549] :
      ( v1_funct_2(k2_funct_1(A_549),k2_relat_1(A_549),k2_relat_1(k2_funct_1(A_549)))
      | ~ v1_funct_1(k2_funct_1(A_549))
      | ~ v1_relat_1(k2_funct_1(A_549))
      | ~ v2_funct_1(A_549)
      | ~ v1_funct_1(A_549)
      | ~ v1_relat_1(A_549) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4133,c_74])).

tff(c_5759,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_4',k2_relat_1(k2_funct_1('#skF_4')))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3939,c_5750])).

tff(c_5761,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_4',k2_relat_1(k2_funct_1('#skF_4')))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3942,c_3950,c_3949,c_3946,c_5759])).

tff(c_5843,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_5761])).

tff(c_5846,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_5843])).

tff(c_5850,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3942,c_3950,c_5846])).

tff(c_5852,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_5761])).

tff(c_32,plain,(
    ! [A_16] :
      ( k1_relat_1(A_16) != k1_xboole_0
      | k1_xboole_0 = A_16
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_3215,plain,(
    ! [A_16] :
      ( k1_relat_1(A_16) != '#skF_6'
      | A_16 = '#skF_6'
      | ~ v1_relat_1(A_16) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3212,c_3212,c_32])).

tff(c_4415,plain,(
    ! [A_16] :
      ( k1_relat_1(A_16) != '#skF_4'
      | A_16 = '#skF_4'
      | ~ v1_relat_1(A_16) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3927,c_3927,c_3215])).

tff(c_5859,plain,
    ( k1_relat_1(k2_funct_1('#skF_4')) != '#skF_4'
    | k2_funct_1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_5852,c_4415])).

tff(c_5875,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_5859])).

tff(c_5878,plain,
    ( k2_relat_1('#skF_4') != '#skF_4'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_5875])).

tff(c_5881,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3942,c_3950,c_3949,c_3939,c_5878])).

tff(c_5882,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_5859])).

tff(c_28,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(A_14,k1_zfmisc_1(B_15))
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_3938,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3927,c_3927,c_3217])).

tff(c_3945,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3927,c_188])).

tff(c_4074,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3938,c_3945])).

tff(c_4078,plain,(
    ~ r1_tarski(k2_funct_1('#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_4074])).

tff(c_5904,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5882,c_4078])).

tff(c_5913,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4933,c_5904])).

tff(c_5914,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_3922])).

tff(c_5920,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5914,c_188])).

tff(c_5925,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3216,c_5920])).

tff(c_7527,plain,(
    ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7522,c_5925])).

tff(c_7536,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3799,c_7527])).

tff(c_7537,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_6'),'#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_186])).

tff(c_7538,plain,(
    m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_186])).

tff(c_8083,plain,(
    ! [A_786,B_787,C_788] :
      ( k1_relset_1(A_786,B_787,C_788) = k1_relat_1(C_788)
      | ~ m1_subset_1(C_788,k1_zfmisc_1(k2_zfmisc_1(A_786,B_787))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_8104,plain,(
    k1_relset_1('#skF_5','#skF_4',k2_funct_1('#skF_6')) = k1_relat_1(k2_funct_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_7538,c_8083])).

tff(c_8582,plain,(
    ! [B_833,C_834,A_835] :
      ( k1_xboole_0 = B_833
      | v1_funct_2(C_834,A_835,B_833)
      | k1_relset_1(A_835,B_833,C_834) != A_835
      | ~ m1_subset_1(C_834,k1_zfmisc_1(k2_zfmisc_1(A_835,B_833))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_8594,plain,
    ( k1_xboole_0 = '#skF_4'
    | v1_funct_2(k2_funct_1('#skF_6'),'#skF_5','#skF_4')
    | k1_relset_1('#skF_5','#skF_4',k2_funct_1('#skF_6')) != '#skF_5' ),
    inference(resolution,[status(thm)],[c_7538,c_8582])).

tff(c_8616,plain,
    ( k1_xboole_0 = '#skF_4'
    | v1_funct_2(k2_funct_1('#skF_6'),'#skF_5','#skF_4')
    | k1_relat_1(k2_funct_1('#skF_6')) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8104,c_8594])).

tff(c_8617,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1(k2_funct_1('#skF_6')) != '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_7537,c_8616])).

tff(c_8623,plain,(
    k1_relat_1(k2_funct_1('#skF_6')) != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_8617])).

tff(c_8626,plain,
    ( k2_relat_1('#skF_6') != '#skF_5'
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_8623])).

tff(c_8629,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7768,c_88,c_82,c_8280,c_8626])).

tff(c_8630,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_8617])).

tff(c_7776,plain,
    ( k1_relat_1('#skF_6') != k1_xboole_0
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_7768,c_32])).

tff(c_7787,plain,(
    k1_relat_1('#skF_6') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_7776])).

tff(c_8664,plain,(
    k1_relat_1('#skF_6') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8630,c_7787])).

tff(c_7775,plain,
    ( k2_relat_1('#skF_6') != k1_xboole_0
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_7768,c_30])).

tff(c_7786,plain,(
    k2_relat_1('#skF_6') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_7775])).

tff(c_8281,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8280,c_7786])).

tff(c_8649,plain,(
    '#skF_5' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8630,c_8281])).

tff(c_8106,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_84,c_8083])).

tff(c_58,plain,(
    ! [B_29,A_28,C_30] :
      ( k1_xboole_0 = B_29
      | k1_relset_1(A_28,B_29,C_30) = A_28
      | ~ v1_funct_2(C_30,A_28,B_29)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_8692,plain,(
    ! [B_836,A_837,C_838] :
      ( B_836 = '#skF_4'
      | k1_relset_1(A_837,B_836,C_838) = A_837
      | ~ v1_funct_2(C_838,A_837,B_836)
      | ~ m1_subset_1(C_838,k1_zfmisc_1(k2_zfmisc_1(A_837,B_836))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8630,c_58])).

tff(c_8711,plain,
    ( '#skF_5' = '#skF_4'
    | k1_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_84,c_8692])).

tff(c_8725,plain,
    ( '#skF_5' = '#skF_4'
    | k1_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_8106,c_8711])).

tff(c_8727,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8664,c_8649,c_8725])).

tff(c_8728,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_7776])).

tff(c_8730,plain,(
    k2_relat_1('#skF_6') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8728,c_7786])).

tff(c_8729,plain,(
    k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_7776])).

tff(c_8751,plain,(
    k1_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8728,c_8729])).

tff(c_9145,plain,(
    ! [A_881] :
      ( k2_relat_1(k2_funct_1(A_881)) = k1_relat_1(A_881)
      | ~ v2_funct_1(A_881)
      | ~ v1_funct_1(A_881)
      | ~ v1_relat_1(A_881) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_7766,plain,(
    v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_7538,c_7746])).

tff(c_7783,plain,
    ( k2_relat_1(k2_funct_1('#skF_6')) != k1_xboole_0
    | k2_funct_1('#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_7766,c_30])).

tff(c_8915,plain,
    ( k2_relat_1(k2_funct_1('#skF_6')) != '#skF_6'
    | k2_funct_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8728,c_8728,c_7783])).

tff(c_8916,plain,(
    k2_relat_1(k2_funct_1('#skF_6')) != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_8915])).

tff(c_9154,plain,
    ( k1_relat_1('#skF_6') != '#skF_6'
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_9145,c_8916])).

tff(c_9161,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7768,c_88,c_82,c_8751,c_9154])).

tff(c_9162,plain,(
    k2_funct_1('#skF_6') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_8915])).

tff(c_7784,plain,
    ( k1_relat_1(k2_funct_1('#skF_6')) != k1_xboole_0
    | k2_funct_1('#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_7766,c_32])).

tff(c_8872,plain,
    ( k1_relat_1(k2_funct_1('#skF_6')) != '#skF_6'
    | k2_funct_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8728,c_8728,c_7784])).

tff(c_8873,plain,(
    k1_relat_1(k2_funct_1('#skF_6')) != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_8872])).

tff(c_9164,plain,(
    k1_relat_1('#skF_6') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9162,c_8873])).

tff(c_9172,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8751,c_9164])).

tff(c_9173,plain,(
    k2_funct_1('#skF_6') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_8872])).

tff(c_9418,plain,(
    ! [A_909] :
      ( k2_relat_1(k2_funct_1(A_909)) = k1_relat_1(A_909)
      | ~ v2_funct_1(A_909)
      | ~ v1_funct_1(A_909)
      | ~ v1_relat_1(A_909) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_9430,plain,
    ( k2_relat_1('#skF_6') = k1_relat_1('#skF_6')
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_9173,c_9418])).

tff(c_9434,plain,(
    k2_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7768,c_88,c_82,c_8751,c_9430])).

tff(c_9436,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8730,c_9434])).

tff(c_9437,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_7775])).

tff(c_7598,plain,(
    ! [A_725,B_726] : m1_subset_1('#skF_3'(A_725,B_726),k1_zfmisc_1(k2_zfmisc_1(A_725,B_726))) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_7609,plain,(
    ! [B_727] : m1_subset_1('#skF_3'(k1_xboole_0,B_727),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_7598])).

tff(c_7614,plain,(
    ! [B_728] : r1_tarski('#skF_3'(k1_xboole_0,B_728),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_7609,c_26])).

tff(c_7571,plain,(
    ! [A_719,B_720] :
      ( r2_hidden('#skF_2'(A_719,B_720),A_719)
      | r1_tarski(A_719,B_720) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_7576,plain,(
    ! [A_721,B_722] :
      ( ~ v1_xboole_0(A_721)
      | r1_tarski(A_721,B_722) ) ),
    inference(resolution,[status(thm)],[c_7571,c_2])).

tff(c_14,plain,(
    ! [B_11,A_10] :
      ( B_11 = A_10
      | ~ r1_tarski(B_11,A_10)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_7579,plain,(
    ! [B_722,A_721] :
      ( B_722 = A_721
      | ~ r1_tarski(B_722,A_721)
      | ~ v1_xboole_0(A_721) ) ),
    inference(resolution,[status(thm)],[c_7576,c_14])).

tff(c_7617,plain,(
    ! [B_728] :
      ( '#skF_3'(k1_xboole_0,B_728) = k1_xboole_0
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_7614,c_7579])).

tff(c_7627,plain,(
    ! [B_729] : '#skF_3'(k1_xboole_0,B_729) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_7617])).

tff(c_7635,plain,(
    ! [B_729] : v1_funct_2(k1_xboole_0,k1_xboole_0,B_729) ),
    inference(superposition,[status(thm),theory(equality)],[c_7627,c_60])).

tff(c_9442,plain,(
    ! [B_729] : v1_funct_2('#skF_6','#skF_6',B_729) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9437,c_9437,c_7635])).

tff(c_9452,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9437,c_12])).

tff(c_9450,plain,(
    ! [B_13] : k2_zfmisc_1('#skF_6',B_13) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9437,c_9437,c_24])).

tff(c_9438,plain,(
    k2_relat_1('#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_7775])).

tff(c_9459,plain,(
    k2_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9437,c_9438])).

tff(c_10199,plain,(
    ! [A_989,B_990,C_991] :
      ( k2_relset_1(A_989,B_990,C_991) = k2_relat_1(C_991)
      | ~ m1_subset_1(C_991,k1_zfmisc_1(k2_zfmisc_1(A_989,B_990))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_10218,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_84,c_10199])).

tff(c_10224,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_9459,c_10218])).

tff(c_7575,plain,(
    ! [A_719,B_720] :
      ( ~ v1_xboole_0(A_719)
      | r1_tarski(A_719,B_720) ) ),
    inference(resolution,[status(thm)],[c_7571,c_2])).

tff(c_9823,plain,(
    ! [A_949] :
      ( k1_relat_1(k2_funct_1(A_949)) = k2_relat_1(A_949)
      | ~ v2_funct_1(A_949)
      | ~ v1_funct_1(A_949)
      | ~ v1_relat_1(A_949) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_9581,plain,
    ( k1_relat_1(k2_funct_1('#skF_6')) != '#skF_6'
    | k2_funct_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9437,c_9437,c_7784])).

tff(c_9582,plain,(
    k1_relat_1(k2_funct_1('#skF_6')) != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_9581])).

tff(c_9832,plain,
    ( k2_relat_1('#skF_6') != '#skF_6'
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_9823,c_9582])).

tff(c_9839,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7768,c_88,c_82,c_9459,c_9832])).

tff(c_9840,plain,(
    k2_funct_1('#skF_6') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_9581])).

tff(c_7542,plain,(
    r1_tarski(k2_funct_1('#skF_6'),k2_zfmisc_1('#skF_5','#skF_4')) ),
    inference(resolution,[status(thm)],[c_7538,c_26])).

tff(c_7558,plain,(
    ! [B_717,A_718] :
      ( B_717 = A_718
      | ~ r1_tarski(B_717,A_718)
      | ~ r1_tarski(A_718,B_717) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_7565,plain,
    ( k2_zfmisc_1('#skF_5','#skF_4') = k2_funct_1('#skF_6')
    | ~ r1_tarski(k2_zfmisc_1('#skF_5','#skF_4'),k2_funct_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_7542,c_7558])).

tff(c_10080,plain,
    ( k2_zfmisc_1('#skF_5','#skF_4') = '#skF_6'
    | ~ r1_tarski(k2_zfmisc_1('#skF_5','#skF_4'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9840,c_9840,c_7565])).

tff(c_10081,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_5','#skF_4'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_10080])).

tff(c_10085,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_4')) ),
    inference(resolution,[status(thm)],[c_7575,c_10081])).

tff(c_10225,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10224,c_10085])).

tff(c_10238,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9452,c_9450,c_10225])).

tff(c_10239,plain,(
    k2_zfmisc_1('#skF_5','#skF_4') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_10080])).

tff(c_9527,plain,(
    ! [B_13,A_12] :
      ( B_13 = '#skF_6'
      | A_12 = '#skF_6'
      | k2_zfmisc_1(A_12,B_13) != '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9437,c_9437,c_9437,c_20])).

tff(c_10264,plain,
    ( '#skF_6' = '#skF_4'
    | '#skF_5' = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_10239,c_9527])).

tff(c_10266,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_10264])).

tff(c_9845,plain,(
    ~ v1_funct_2('#skF_6','#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9840,c_7537])).

tff(c_10270,plain,(
    ~ v1_funct_2('#skF_6','#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10266,c_9845])).

tff(c_10280,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9442,c_10270])).

tff(c_10281,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_10264])).

tff(c_10305,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10281,c_9452])).

tff(c_10300,plain,(
    ! [B_13] : k2_zfmisc_1('#skF_4',B_13) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10281,c_10281,c_9450])).

tff(c_7580,plain,(
    ! [B_723,A_724] :
      ( B_723 = A_724
      | ~ r1_tarski(B_723,A_724)
      | ~ v1_xboole_0(A_724) ) ),
    inference(resolution,[status(thm)],[c_7576,c_14])).

tff(c_7595,plain,
    ( k2_zfmisc_1('#skF_4','#skF_5') = '#skF_6'
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_146,c_7580])).

tff(c_7651,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_7595])).

tff(c_10401,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10300,c_7651])).

tff(c_10404,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10305,c_10401])).

tff(c_10405,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_7595])).

tff(c_7566,plain,
    ( k2_zfmisc_1('#skF_4','#skF_5') = '#skF_6'
    | ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_146,c_7558])).

tff(c_10407,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_7566])).

tff(c_10455,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_10405,c_10407])).

tff(c_10456,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_7566])).

tff(c_10479,plain,(
    ! [B_1000,A_1001] :
      ( k1_xboole_0 = B_1000
      | k1_xboole_0 = A_1001
      | k2_zfmisc_1(A_1001,B_1000) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_10482,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 != '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_10456,c_10479])).

tff(c_10601,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_10482])).

tff(c_10406,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_7595])).

tff(c_10504,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10456,c_10406])).

tff(c_10703,plain,(
    ! [B_1019,A_1020] :
      ( B_1019 = A_1020
      | ~ v1_xboole_0(B_1019)
      | ~ v1_xboole_0(A_1020) ) ),
    inference(resolution,[status(thm)],[c_7575,c_7580])).

tff(c_10710,plain,(
    ! [A_1021] :
      ( A_1021 = '#skF_6'
      | ~ v1_xboole_0(A_1021) ) ),
    inference(resolution,[status(thm)],[c_10504,c_10703])).

tff(c_10716,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_12,c_10710])).

tff(c_10722,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10601,c_10716])).

tff(c_10724,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_10482])).

tff(c_10727,plain,(
    ! [B_729] : v1_funct_2('#skF_6','#skF_6',B_729) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10724,c_10724,c_7635])).

tff(c_10736,plain,(
    ! [B_13] : k2_zfmisc_1('#skF_6',B_13) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10724,c_10724,c_24])).

tff(c_10723,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_10482])).

tff(c_10799,plain,
    ( '#skF_6' = '#skF_4'
    | '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10724,c_10724,c_10723])).

tff(c_10800,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_10799])).

tff(c_10803,plain,(
    r1_tarski(k2_funct_1('#skF_6'),k2_zfmisc_1('#skF_6','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10800,c_7542])).

tff(c_10808,plain,(
    r1_tarski(k2_funct_1('#skF_6'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10736,c_10803])).

tff(c_10873,plain,
    ( k2_funct_1('#skF_6') = '#skF_6'
    | ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_10808,c_7579])).

tff(c_10878,plain,(
    k2_funct_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10504,c_10873])).

tff(c_10805,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_6'),'#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10800,c_7537])).

tff(c_10918,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10727,c_10878,c_10805])).

tff(c_10919,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_10799])).

tff(c_10927,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10919,c_10724])).

tff(c_10508,plain,(
    ! [A_1003] : m1_subset_1('#skF_3'(A_1003,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_7598])).

tff(c_10517,plain,(
    ! [A_1004] : r1_tarski('#skF_3'(A_1004,k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_10508,c_26])).

tff(c_10520,plain,(
    ! [A_1004] :
      ( '#skF_3'(A_1004,k1_xboole_0) = k1_xboole_0
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_10517,c_7579])).

tff(c_10564,plain,(
    ! [A_1008] : '#skF_3'(A_1008,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_10520])).

tff(c_10575,plain,(
    ! [A_1008] : v1_funct_2(k1_xboole_0,A_1008,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10564,c_60])).

tff(c_11185,plain,(
    ! [A_1008] : v1_funct_2('#skF_4',A_1008,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10927,c_10927,c_10575])).

tff(c_10929,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10919,c_10504])).

tff(c_10737,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10724,c_10724,c_22])).

tff(c_11100,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10919,c_10919,c_10737])).

tff(c_10933,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10919,c_7538])).

tff(c_11249,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11100,c_10933])).

tff(c_11258,plain,(
    r1_tarski(k2_funct_1('#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_11249,c_26])).

tff(c_11264,plain,
    ( k2_funct_1('#skF_4') = '#skF_4'
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_11258,c_7579])).

tff(c_11271,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10929,c_11264])).

tff(c_10934,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10919,c_7537])).

tff(c_11275,plain,(
    ~ v1_funct_2('#skF_4','#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11271,c_10934])).

tff(c_11282,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11185,c_11275])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:31:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.63/2.69  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.63/2.74  
% 7.63/2.74  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.63/2.74  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 7.63/2.74  
% 7.63/2.74  %Foreground sorts:
% 7.63/2.74  
% 7.63/2.74  
% 7.63/2.74  %Background operators:
% 7.63/2.74  
% 7.63/2.74  
% 7.63/2.74  %Foreground operators:
% 7.63/2.74  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 7.63/2.74  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.63/2.74  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 7.63/2.74  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 7.63/2.74  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.63/2.74  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.63/2.74  tff('#skF_1', type, '#skF_1': $i > $i).
% 7.63/2.74  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.63/2.74  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 7.63/2.74  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.63/2.74  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.63/2.74  tff('#skF_5', type, '#skF_5': $i).
% 7.63/2.74  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.63/2.74  tff('#skF_6', type, '#skF_6': $i).
% 7.63/2.74  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 7.63/2.74  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.63/2.74  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.63/2.74  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.63/2.74  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.63/2.74  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.63/2.74  tff('#skF_4', type, '#skF_4': $i).
% 7.63/2.74  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.63/2.74  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.63/2.74  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.63/2.74  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.63/2.74  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.63/2.74  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.63/2.74  
% 8.02/2.77  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.02/2.77  tff(f_151, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 8.02/2.77  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 8.02/2.77  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 8.02/2.77  tff(f_81, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 8.02/2.77  tff(f_71, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 8.02/2.77  tff(f_63, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 8.02/2.77  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 8.02/2.77  tff(f_111, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 8.02/2.77  tff(f_134, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 8.02/2.77  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 8.02/2.77  tff(f_51, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 8.02/2.77  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 8.02/2.77  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 8.02/2.77  tff(f_55, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 8.02/2.77  tff(f_124, axiom, (![A, B]: (?[C]: (((((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & v1_relat_1(C)) & v4_relat_1(C, A)) & v5_relat_1(C, B)) & v1_funct_1(C)) & v1_funct_2(C, A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_funct_2)).
% 8.02/2.77  tff(c_18, plain, (![B_11]: (r1_tarski(B_11, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.02/2.77  tff(c_84, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_151])).
% 8.02/2.77  tff(c_7746, plain, (![C_738, A_739, B_740]: (v1_relat_1(C_738) | ~m1_subset_1(C_738, k1_zfmisc_1(k2_zfmisc_1(A_739, B_740))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 8.02/2.77  tff(c_7768, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_84, c_7746])).
% 8.02/2.77  tff(c_88, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_151])).
% 8.02/2.77  tff(c_82, plain, (v2_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_151])).
% 8.02/2.77  tff(c_80, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_5'), inference(cnfTransformation, [status(thm)], [f_151])).
% 8.02/2.77  tff(c_8252, plain, (![A_799, B_800, C_801]: (k2_relset_1(A_799, B_800, C_801)=k2_relat_1(C_801) | ~m1_subset_1(C_801, k1_zfmisc_1(k2_zfmisc_1(A_799, B_800))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 8.02/2.77  tff(c_8268, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_84, c_8252])).
% 8.02/2.77  tff(c_8280, plain, (k2_relat_1('#skF_6')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_8268])).
% 8.02/2.77  tff(c_40, plain, (![A_18]: (k1_relat_1(k2_funct_1(A_18))=k2_relat_1(A_18) | ~v2_funct_1(A_18) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.02/2.77  tff(c_148, plain, (![A_56]: (v1_funct_1(k2_funct_1(A_56)) | ~v1_funct_1(A_56) | ~v1_relat_1(A_56))), inference(cnfTransformation, [status(thm)], [f_71])).
% 8.02/2.77  tff(c_78, plain, (~m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4'))) | ~v1_funct_2(k2_funct_1('#skF_6'), '#skF_5', '#skF_4') | ~v1_funct_1(k2_funct_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_151])).
% 8.02/2.77  tff(c_147, plain, (~v1_funct_1(k2_funct_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_78])).
% 8.02/2.77  tff(c_151, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_148, c_147])).
% 8.02/2.77  tff(c_154, plain, (~v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_151])).
% 8.02/2.77  tff(c_169, plain, (![C_59, A_60, B_61]: (v1_relat_1(C_59) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 8.02/2.77  tff(c_176, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_84, c_169])).
% 8.02/2.77  tff(c_185, plain, $false, inference(negUnitSimplification, [status(thm)], [c_154, c_176])).
% 8.02/2.77  tff(c_186, plain, (~v1_funct_2(k2_funct_1('#skF_6'), '#skF_5', '#skF_4') | ~m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4')))), inference(splitRight, [status(thm)], [c_78])).
% 8.02/2.77  tff(c_188, plain, (~m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4')))), inference(splitLeft, [status(thm)], [c_186])).
% 8.02/2.77  tff(c_225, plain, (![C_71, A_72, B_73]: (v1_relat_1(C_71) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 8.02/2.77  tff(c_238, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_84, c_225])).
% 8.02/2.77  tff(c_741, plain, (![A_136, B_137, C_138]: (k2_relset_1(A_136, B_137, C_138)=k2_relat_1(C_138) | ~m1_subset_1(C_138, k1_zfmisc_1(k2_zfmisc_1(A_136, B_137))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 8.02/2.77  tff(c_751, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_84, c_741])).
% 8.02/2.77  tff(c_761, plain, (k2_relat_1('#skF_6')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_751])).
% 8.02/2.77  tff(c_30, plain, (![A_16]: (k2_relat_1(A_16)!=k1_xboole_0 | k1_xboole_0=A_16 | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.02/2.77  tff(c_245, plain, (k2_relat_1('#skF_6')!=k1_xboole_0 | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_238, c_30])).
% 8.02/2.77  tff(c_247, plain, (k2_relat_1('#skF_6')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_245])).
% 8.02/2.77  tff(c_762, plain, (k1_xboole_0!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_761, c_247])).
% 8.02/2.77  tff(c_86, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_151])).
% 8.02/2.77  tff(c_851, plain, (![A_146, B_147, C_148]: (k1_relset_1(A_146, B_147, C_148)=k1_relat_1(C_148) | ~m1_subset_1(C_148, k1_zfmisc_1(k2_zfmisc_1(A_146, B_147))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 8.02/2.77  tff(c_870, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_84, c_851])).
% 8.02/2.77  tff(c_1194, plain, (![B_181, A_182, C_183]: (k1_xboole_0=B_181 | k1_relset_1(A_182, B_181, C_183)=A_182 | ~v1_funct_2(C_183, A_182, B_181) | ~m1_subset_1(C_183, k1_zfmisc_1(k2_zfmisc_1(A_182, B_181))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 8.02/2.77  tff(c_1210, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_84, c_1194])).
% 8.02/2.77  tff(c_1228, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_870, c_1210])).
% 8.02/2.77  tff(c_1229, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_762, c_1228])).
% 8.02/2.77  tff(c_38, plain, (![A_18]: (k2_relat_1(k2_funct_1(A_18))=k1_relat_1(A_18) | ~v2_funct_1(A_18) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.02/2.77  tff(c_36, plain, (![A_17]: (v1_relat_1(k2_funct_1(A_17)) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_71])).
% 8.02/2.77  tff(c_187, plain, (v1_funct_1(k2_funct_1('#skF_6'))), inference(splitRight, [status(thm)], [c_78])).
% 8.02/2.77  tff(c_621, plain, (![A_119]: (k1_relat_1(k2_funct_1(A_119))=k2_relat_1(A_119) | ~v2_funct_1(A_119) | ~v1_funct_1(A_119) | ~v1_relat_1(A_119))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.02/2.77  tff(c_74, plain, (![A_34]: (v1_funct_2(A_34, k1_relat_1(A_34), k2_relat_1(A_34)) | ~v1_funct_1(A_34) | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_134])).
% 8.02/2.77  tff(c_2569, plain, (![A_275]: (v1_funct_2(k2_funct_1(A_275), k2_relat_1(A_275), k2_relat_1(k2_funct_1(A_275))) | ~v1_funct_1(k2_funct_1(A_275)) | ~v1_relat_1(k2_funct_1(A_275)) | ~v2_funct_1(A_275) | ~v1_funct_1(A_275) | ~v1_relat_1(A_275))), inference(superposition, [status(thm), theory('equality')], [c_621, c_74])).
% 8.02/2.77  tff(c_2575, plain, (v1_funct_2(k2_funct_1('#skF_6'), '#skF_5', k2_relat_1(k2_funct_1('#skF_6'))) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')) | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_761, c_2569])).
% 8.02/2.77  tff(c_2585, plain, (v1_funct_2(k2_funct_1('#skF_6'), '#skF_5', k2_relat_1(k2_funct_1('#skF_6'))) | ~v1_relat_1(k2_funct_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_238, c_88, c_82, c_187, c_2575])).
% 8.02/2.77  tff(c_2586, plain, (~v1_relat_1(k2_funct_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_2585])).
% 8.02/2.77  tff(c_2589, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_36, c_2586])).
% 8.02/2.77  tff(c_2593, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_238, c_88, c_2589])).
% 8.02/2.77  tff(c_2595, plain, (v1_relat_1(k2_funct_1('#skF_6'))), inference(splitRight, [status(thm)], [c_2585])).
% 8.02/2.77  tff(c_899, plain, (![A_153]: (m1_subset_1(A_153, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_153), k2_relat_1(A_153)))) | ~v1_funct_1(A_153) | ~v1_relat_1(A_153))), inference(cnfTransformation, [status(thm)], [f_134])).
% 8.02/2.77  tff(c_3134, plain, (![A_312]: (m1_subset_1(k2_funct_1(A_312), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_312), k2_relat_1(k2_funct_1(A_312))))) | ~v1_funct_1(k2_funct_1(A_312)) | ~v1_relat_1(k2_funct_1(A_312)) | ~v2_funct_1(A_312) | ~v1_funct_1(A_312) | ~v1_relat_1(A_312))), inference(superposition, [status(thm), theory('equality')], [c_40, c_899])).
% 8.02/2.77  tff(c_3158, plain, (m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', k2_relat_1(k2_funct_1('#skF_6'))))) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')) | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_761, c_3134])).
% 8.02/2.77  tff(c_3174, plain, (m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', k2_relat_1(k2_funct_1('#skF_6')))))), inference(demodulation, [status(thm), theory('equality')], [c_238, c_88, c_82, c_2595, c_187, c_3158])).
% 8.02/2.77  tff(c_3195, plain, (m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_relat_1('#skF_6')))) | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_38, c_3174])).
% 8.02/2.77  tff(c_3209, plain, (m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_238, c_88, c_82, c_1229, c_3195])).
% 8.02/2.77  tff(c_3211, plain, $false, inference(negUnitSimplification, [status(thm)], [c_188, c_3209])).
% 8.02/2.77  tff(c_3212, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_245])).
% 8.02/2.77  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.02/2.77  tff(c_3218, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3212, c_12])).
% 8.02/2.77  tff(c_22, plain, (![A_12]: (k2_zfmisc_1(A_12, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.02/2.77  tff(c_3217, plain, (![A_12]: (k2_zfmisc_1(A_12, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3212, c_3212, c_22])).
% 8.02/2.77  tff(c_3213, plain, (k2_relat_1('#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_245])).
% 8.02/2.77  tff(c_3224, plain, (k2_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_3212, c_3213])).
% 8.02/2.77  tff(c_3759, plain, (![A_372, B_373, C_374]: (k2_relset_1(A_372, B_373, C_374)=k2_relat_1(C_374) | ~m1_subset_1(C_374, k1_zfmisc_1(k2_zfmisc_1(A_372, B_373))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 8.02/2.77  tff(c_3778, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_84, c_3759])).
% 8.02/2.77  tff(c_3783, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_3224, c_80, c_3778])).
% 8.02/2.77  tff(c_208, plain, (![A_65, B_66]: (r2_hidden('#skF_2'(A_65, B_66), A_65) | r1_tarski(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.02/2.77  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.02/2.77  tff(c_212, plain, (![A_65, B_66]: (~v1_xboole_0(A_65) | r1_tarski(A_65, B_66))), inference(resolution, [status(thm)], [c_208, c_2])).
% 8.02/2.77  tff(c_138, plain, (![A_54, B_55]: (r1_tarski(A_54, B_55) | ~m1_subset_1(A_54, k1_zfmisc_1(B_55)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.02/2.77  tff(c_146, plain, (r1_tarski('#skF_6', k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_84, c_138])).
% 8.02/2.77  tff(c_3274, plain, (![B_317, A_318]: (B_317=A_318 | ~r1_tarski(B_317, A_318) | ~r1_tarski(A_318, B_317))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.02/2.77  tff(c_3282, plain, (k2_zfmisc_1('#skF_4', '#skF_5')='#skF_6' | ~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), '#skF_6')), inference(resolution, [status(thm)], [c_146, c_3274])).
% 8.02/2.77  tff(c_3294, plain, (~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), '#skF_6')), inference(splitLeft, [status(thm)], [c_3282])).
% 8.02/2.77  tff(c_3298, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_212, c_3294])).
% 8.02/2.77  tff(c_3785, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_3783, c_3298])).
% 8.02/2.77  tff(c_3795, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3218, c_3217, c_3785])).
% 8.02/2.77  tff(c_3796, plain, (k2_zfmisc_1('#skF_4', '#skF_5')='#skF_6'), inference(splitRight, [status(thm)], [c_3282])).
% 8.02/2.77  tff(c_3799, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_3796, c_84])).
% 8.02/2.77  tff(c_24, plain, (![B_13]: (k2_zfmisc_1(k1_xboole_0, B_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.02/2.77  tff(c_3216, plain, (![B_13]: (k2_zfmisc_1('#skF_6', B_13)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3212, c_3212, c_24])).
% 8.02/2.77  tff(c_3818, plain, (![A_375, B_376]: (m1_subset_1('#skF_3'(A_375, B_376), k1_zfmisc_1(k2_zfmisc_1(A_375, B_376))))), inference(cnfTransformation, [status(thm)], [f_124])).
% 8.02/2.77  tff(c_3854, plain, (![B_377]: (m1_subset_1('#skF_3'('#skF_6', B_377), k1_zfmisc_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_3216, c_3818])).
% 8.02/2.77  tff(c_26, plain, (![A_14, B_15]: (r1_tarski(A_14, B_15) | ~m1_subset_1(A_14, k1_zfmisc_1(B_15)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.02/2.77  tff(c_3863, plain, (![B_377]: (r1_tarski('#skF_3'('#skF_6', B_377), '#skF_6'))), inference(resolution, [status(thm)], [c_3854, c_26])).
% 8.02/2.77  tff(c_6062, plain, (![B_569, A_570]: (B_569=A_570 | ~r1_tarski(B_569, A_570) | ~v1_xboole_0(A_570))), inference(resolution, [status(thm)], [c_212, c_3274])).
% 8.02/2.77  tff(c_6071, plain, (![B_377]: ('#skF_3'('#skF_6', B_377)='#skF_6' | ~v1_xboole_0('#skF_6'))), inference(resolution, [status(thm)], [c_3863, c_6062])).
% 8.02/2.77  tff(c_6084, plain, (![B_377]: ('#skF_3'('#skF_6', B_377)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3218, c_6071])).
% 8.02/2.77  tff(c_70, plain, (![A_31, B_32]: (m1_subset_1('#skF_3'(A_31, B_32), k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))))), inference(cnfTransformation, [status(thm)], [f_124])).
% 8.02/2.77  tff(c_6330, plain, (![A_595, B_596, C_597]: (k1_relset_1(A_595, B_596, C_597)=k1_relat_1(C_597) | ~m1_subset_1(C_597, k1_zfmisc_1(k2_zfmisc_1(A_595, B_596))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 8.02/2.77  tff(c_6394, plain, (![A_605, B_606]: (k1_relset_1(A_605, B_606, '#skF_3'(A_605, B_606))=k1_relat_1('#skF_3'(A_605, B_606)))), inference(resolution, [status(thm)], [c_70, c_6330])).
% 8.02/2.77  tff(c_6403, plain, (![B_377]: (k1_relat_1('#skF_3'('#skF_6', B_377))=k1_relset_1('#skF_6', B_377, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_6084, c_6394])).
% 8.02/2.77  tff(c_6409, plain, (![B_377]: (k1_relset_1('#skF_6', B_377, '#skF_6')=k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_6084, c_6403])).
% 8.02/2.77  tff(c_60, plain, (![A_31, B_32]: (v1_funct_2('#skF_3'(A_31, B_32), A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_124])).
% 8.02/2.77  tff(c_56, plain, (![B_29, C_30]: (k1_relset_1(k1_xboole_0, B_29, C_30)=k1_xboole_0 | ~v1_funct_2(C_30, k1_xboole_0, B_29) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_29))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 8.02/2.77  tff(c_89, plain, (![B_29, C_30]: (k1_relset_1(k1_xboole_0, B_29, C_30)=k1_xboole_0 | ~v1_funct_2(C_30, k1_xboole_0, B_29) | ~m1_subset_1(C_30, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_56])).
% 8.02/2.77  tff(c_6553, plain, (![B_626, C_627]: (k1_relset_1('#skF_6', B_626, C_627)='#skF_6' | ~v1_funct_2(C_627, '#skF_6', B_626) | ~m1_subset_1(C_627, k1_zfmisc_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_3212, c_3212, c_3212, c_3212, c_89])).
% 8.02/2.77  tff(c_6561, plain, (![B_32]: (k1_relset_1('#skF_6', B_32, '#skF_3'('#skF_6', B_32))='#skF_6' | ~m1_subset_1('#skF_3'('#skF_6', B_32), k1_zfmisc_1('#skF_6')))), inference(resolution, [status(thm)], [c_60, c_6553])).
% 8.02/2.77  tff(c_6570, plain, (k1_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_3799, c_6084, c_6409, c_6084, c_6561])).
% 8.02/2.77  tff(c_6200, plain, (![A_580]: (k2_relat_1(k2_funct_1(A_580))=k1_relat_1(A_580) | ~v2_funct_1(A_580) | ~v1_funct_1(A_580) | ~v1_relat_1(A_580))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.02/2.77  tff(c_7447, plain, (![A_710]: (v1_funct_2(k2_funct_1(A_710), k1_relat_1(k2_funct_1(A_710)), k1_relat_1(A_710)) | ~v1_funct_1(k2_funct_1(A_710)) | ~v1_relat_1(k2_funct_1(A_710)) | ~v2_funct_1(A_710) | ~v1_funct_1(A_710) | ~v1_relat_1(A_710))), inference(superposition, [status(thm), theory('equality')], [c_6200, c_74])).
% 8.02/2.77  tff(c_7453, plain, (v1_funct_2(k2_funct_1('#skF_6'), k1_relat_1(k2_funct_1('#skF_6')), '#skF_6') | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')) | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_6570, c_7447])).
% 8.02/2.77  tff(c_7463, plain, (v1_funct_2(k2_funct_1('#skF_6'), k1_relat_1(k2_funct_1('#skF_6')), '#skF_6') | ~v1_relat_1(k2_funct_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_238, c_88, c_82, c_187, c_7453])).
% 8.02/2.77  tff(c_7464, plain, (~v1_relat_1(k2_funct_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_7463])).
% 8.02/2.77  tff(c_7467, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_36, c_7464])).
% 8.02/2.77  tff(c_7471, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_238, c_88, c_7467])).
% 8.02/2.77  tff(c_7473, plain, (v1_relat_1(k2_funct_1('#skF_6'))), inference(splitRight, [status(thm)], [c_7463])).
% 8.02/2.77  tff(c_3214, plain, (![A_16]: (k2_relat_1(A_16)!='#skF_6' | A_16='#skF_6' | ~v1_relat_1(A_16))), inference(demodulation, [status(thm), theory('equality')], [c_3212, c_3212, c_30])).
% 8.02/2.77  tff(c_7481, plain, (k2_relat_1(k2_funct_1('#skF_6'))!='#skF_6' | k2_funct_1('#skF_6')='#skF_6'), inference(resolution, [status(thm)], [c_7473, c_3214])).
% 8.02/2.77  tff(c_7515, plain, (k2_relat_1(k2_funct_1('#skF_6'))!='#skF_6'), inference(splitLeft, [status(thm)], [c_7481])).
% 8.02/2.77  tff(c_7518, plain, (k1_relat_1('#skF_6')!='#skF_6' | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_38, c_7515])).
% 8.02/2.77  tff(c_7521, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_238, c_88, c_82, c_6570, c_7518])).
% 8.02/2.77  tff(c_7522, plain, (k2_funct_1('#skF_6')='#skF_6'), inference(splitRight, [status(thm)], [c_7481])).
% 8.02/2.77  tff(c_20, plain, (![B_13, A_12]: (k1_xboole_0=B_13 | k1_xboole_0=A_12 | k2_zfmisc_1(A_12, B_13)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.02/2.77  tff(c_3912, plain, (![B_379, A_380]: (B_379='#skF_6' | A_380='#skF_6' | k2_zfmisc_1(A_380, B_379)!='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3212, c_3212, c_3212, c_20])).
% 8.02/2.77  tff(c_3922, plain, ('#skF_5'='#skF_6' | '#skF_6'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_3796, c_3912])).
% 8.02/2.77  tff(c_3927, plain, ('#skF_6'='#skF_4'), inference(splitLeft, [status(thm)], [c_3922])).
% 8.02/2.77  tff(c_3940, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3927, c_3218])).
% 8.02/2.77  tff(c_3937, plain, (![B_13]: (k2_zfmisc_1('#skF_4', B_13)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3927, c_3927, c_3216])).
% 8.02/2.77  tff(c_4061, plain, (![B_377]: (r1_tarski('#skF_3'('#skF_4', B_377), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3927, c_3927, c_3863])).
% 8.02/2.77  tff(c_4202, plain, (![B_403, A_404]: (B_403=A_404 | ~r1_tarski(B_403, A_404) | ~v1_xboole_0(A_404))), inference(resolution, [status(thm)], [c_212, c_3274])).
% 8.02/2.77  tff(c_4211, plain, (![B_377]: ('#skF_3'('#skF_4', B_377)='#skF_4' | ~v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_4061, c_4202])).
% 8.02/2.77  tff(c_4224, plain, (![B_377]: ('#skF_3'('#skF_4', B_377)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3940, c_4211])).
% 8.02/2.77  tff(c_3836, plain, (![A_375, B_376]: (r1_tarski('#skF_3'(A_375, B_376), k2_zfmisc_1(A_375, B_376)))), inference(resolution, [status(thm)], [c_3818, c_26])).
% 8.02/2.77  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.02/2.77  tff(c_3968, plain, (![C_381, B_382, A_383]: (r2_hidden(C_381, B_382) | ~r2_hidden(C_381, A_383) | ~r1_tarski(A_383, B_382))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.02/2.77  tff(c_4873, plain, (![A_468, B_469, B_470]: (r2_hidden('#skF_2'(A_468, B_469), B_470) | ~r1_tarski(A_468, B_470) | r1_tarski(A_468, B_469))), inference(resolution, [status(thm)], [c_10, c_3968])).
% 8.02/2.77  tff(c_4886, plain, (![B_471, A_472, B_473]: (~v1_xboole_0(B_471) | ~r1_tarski(A_472, B_471) | r1_tarski(A_472, B_473))), inference(resolution, [status(thm)], [c_4873, c_2])).
% 8.02/2.77  tff(c_4896, plain, (![A_474, B_475, B_476]: (~v1_xboole_0(k2_zfmisc_1(A_474, B_475)) | r1_tarski('#skF_3'(A_474, B_475), B_476))), inference(resolution, [status(thm)], [c_3836, c_4886])).
% 8.02/2.77  tff(c_4920, plain, (![B_377, B_476]: (~v1_xboole_0(k2_zfmisc_1('#skF_4', B_377)) | r1_tarski('#skF_4', B_476))), inference(superposition, [status(thm), theory('equality')], [c_4224, c_4896])).
% 8.02/2.77  tff(c_4933, plain, (![B_476]: (r1_tarski('#skF_4', B_476))), inference(demodulation, [status(thm), theory('equality')], [c_3940, c_3937, c_4920])).
% 8.02/2.77  tff(c_3942, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3927, c_238])).
% 8.02/2.77  tff(c_3950, plain, (v1_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3927, c_88])).
% 8.02/2.77  tff(c_3949, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3927, c_82])).
% 8.02/2.77  tff(c_3939, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3927, c_3927, c_3224])).
% 8.02/2.77  tff(c_3946, plain, (v1_funct_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3927, c_187])).
% 8.02/2.77  tff(c_4133, plain, (![A_394]: (k1_relat_1(k2_funct_1(A_394))=k2_relat_1(A_394) | ~v2_funct_1(A_394) | ~v1_funct_1(A_394) | ~v1_relat_1(A_394))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.02/2.77  tff(c_5750, plain, (![A_549]: (v1_funct_2(k2_funct_1(A_549), k2_relat_1(A_549), k2_relat_1(k2_funct_1(A_549))) | ~v1_funct_1(k2_funct_1(A_549)) | ~v1_relat_1(k2_funct_1(A_549)) | ~v2_funct_1(A_549) | ~v1_funct_1(A_549) | ~v1_relat_1(A_549))), inference(superposition, [status(thm), theory('equality')], [c_4133, c_74])).
% 8.02/2.77  tff(c_5759, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_4', k2_relat_1(k2_funct_1('#skF_4'))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3939, c_5750])).
% 8.02/2.77  tff(c_5761, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_4', k2_relat_1(k2_funct_1('#skF_4'))) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3942, c_3950, c_3949, c_3946, c_5759])).
% 8.02/2.77  tff(c_5843, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_5761])).
% 8.02/2.77  tff(c_5846, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_5843])).
% 8.02/2.77  tff(c_5850, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3942, c_3950, c_5846])).
% 8.02/2.77  tff(c_5852, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_5761])).
% 8.02/2.77  tff(c_32, plain, (![A_16]: (k1_relat_1(A_16)!=k1_xboole_0 | k1_xboole_0=A_16 | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.02/2.77  tff(c_3215, plain, (![A_16]: (k1_relat_1(A_16)!='#skF_6' | A_16='#skF_6' | ~v1_relat_1(A_16))), inference(demodulation, [status(thm), theory('equality')], [c_3212, c_3212, c_32])).
% 8.02/2.77  tff(c_4415, plain, (![A_16]: (k1_relat_1(A_16)!='#skF_4' | A_16='#skF_4' | ~v1_relat_1(A_16))), inference(demodulation, [status(thm), theory('equality')], [c_3927, c_3927, c_3215])).
% 8.02/2.77  tff(c_5859, plain, (k1_relat_1(k2_funct_1('#skF_4'))!='#skF_4' | k2_funct_1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_5852, c_4415])).
% 8.02/2.77  tff(c_5875, plain, (k1_relat_1(k2_funct_1('#skF_4'))!='#skF_4'), inference(splitLeft, [status(thm)], [c_5859])).
% 8.02/2.77  tff(c_5878, plain, (k2_relat_1('#skF_4')!='#skF_4' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_40, c_5875])).
% 8.02/2.77  tff(c_5881, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3942, c_3950, c_3949, c_3939, c_5878])).
% 8.02/2.77  tff(c_5882, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_5859])).
% 8.02/2.77  tff(c_28, plain, (![A_14, B_15]: (m1_subset_1(A_14, k1_zfmisc_1(B_15)) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.02/2.77  tff(c_3938, plain, (![A_12]: (k2_zfmisc_1(A_12, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3927, c_3927, c_3217])).
% 8.02/2.77  tff(c_3945, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_3927, c_188])).
% 8.02/2.77  tff(c_4074, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3938, c_3945])).
% 8.02/2.77  tff(c_4078, plain, (~r1_tarski(k2_funct_1('#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_28, c_4074])).
% 8.02/2.77  tff(c_5904, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5882, c_4078])).
% 8.02/2.77  tff(c_5913, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4933, c_5904])).
% 8.02/2.77  tff(c_5914, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_3922])).
% 8.02/2.77  tff(c_5920, plain, (~m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_5914, c_188])).
% 8.02/2.77  tff(c_5925, plain, (~m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_3216, c_5920])).
% 8.02/2.77  tff(c_7527, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_7522, c_5925])).
% 8.02/2.77  tff(c_7536, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3799, c_7527])).
% 8.02/2.77  tff(c_7537, plain, (~v1_funct_2(k2_funct_1('#skF_6'), '#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_186])).
% 8.02/2.77  tff(c_7538, plain, (m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4')))), inference(splitRight, [status(thm)], [c_186])).
% 8.02/2.77  tff(c_8083, plain, (![A_786, B_787, C_788]: (k1_relset_1(A_786, B_787, C_788)=k1_relat_1(C_788) | ~m1_subset_1(C_788, k1_zfmisc_1(k2_zfmisc_1(A_786, B_787))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 8.02/2.77  tff(c_8104, plain, (k1_relset_1('#skF_5', '#skF_4', k2_funct_1('#skF_6'))=k1_relat_1(k2_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_7538, c_8083])).
% 8.02/2.77  tff(c_8582, plain, (![B_833, C_834, A_835]: (k1_xboole_0=B_833 | v1_funct_2(C_834, A_835, B_833) | k1_relset_1(A_835, B_833, C_834)!=A_835 | ~m1_subset_1(C_834, k1_zfmisc_1(k2_zfmisc_1(A_835, B_833))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 8.02/2.77  tff(c_8594, plain, (k1_xboole_0='#skF_4' | v1_funct_2(k2_funct_1('#skF_6'), '#skF_5', '#skF_4') | k1_relset_1('#skF_5', '#skF_4', k2_funct_1('#skF_6'))!='#skF_5'), inference(resolution, [status(thm)], [c_7538, c_8582])).
% 8.02/2.77  tff(c_8616, plain, (k1_xboole_0='#skF_4' | v1_funct_2(k2_funct_1('#skF_6'), '#skF_5', '#skF_4') | k1_relat_1(k2_funct_1('#skF_6'))!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_8104, c_8594])).
% 8.02/2.77  tff(c_8617, plain, (k1_xboole_0='#skF_4' | k1_relat_1(k2_funct_1('#skF_6'))!='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_7537, c_8616])).
% 8.02/2.77  tff(c_8623, plain, (k1_relat_1(k2_funct_1('#skF_6'))!='#skF_5'), inference(splitLeft, [status(thm)], [c_8617])).
% 8.02/2.77  tff(c_8626, plain, (k2_relat_1('#skF_6')!='#skF_5' | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_40, c_8623])).
% 8.02/2.77  tff(c_8629, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7768, c_88, c_82, c_8280, c_8626])).
% 8.02/2.77  tff(c_8630, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_8617])).
% 8.02/2.77  tff(c_7776, plain, (k1_relat_1('#skF_6')!=k1_xboole_0 | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_7768, c_32])).
% 8.02/2.77  tff(c_7787, plain, (k1_relat_1('#skF_6')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_7776])).
% 8.02/2.77  tff(c_8664, plain, (k1_relat_1('#skF_6')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_8630, c_7787])).
% 8.02/2.77  tff(c_7775, plain, (k2_relat_1('#skF_6')!=k1_xboole_0 | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_7768, c_30])).
% 8.02/2.77  tff(c_7786, plain, (k2_relat_1('#skF_6')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_7775])).
% 8.02/2.77  tff(c_8281, plain, (k1_xboole_0!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_8280, c_7786])).
% 8.02/2.77  tff(c_8649, plain, ('#skF_5'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_8630, c_8281])).
% 8.02/2.77  tff(c_8106, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_84, c_8083])).
% 8.02/2.77  tff(c_58, plain, (![B_29, A_28, C_30]: (k1_xboole_0=B_29 | k1_relset_1(A_28, B_29, C_30)=A_28 | ~v1_funct_2(C_30, A_28, B_29) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 8.02/2.77  tff(c_8692, plain, (![B_836, A_837, C_838]: (B_836='#skF_4' | k1_relset_1(A_837, B_836, C_838)=A_837 | ~v1_funct_2(C_838, A_837, B_836) | ~m1_subset_1(C_838, k1_zfmisc_1(k2_zfmisc_1(A_837, B_836))))), inference(demodulation, [status(thm), theory('equality')], [c_8630, c_58])).
% 8.02/2.77  tff(c_8711, plain, ('#skF_5'='#skF_4' | k1_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_84, c_8692])).
% 8.02/2.77  tff(c_8725, plain, ('#skF_5'='#skF_4' | k1_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_8106, c_8711])).
% 8.02/2.77  tff(c_8727, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8664, c_8649, c_8725])).
% 8.02/2.77  tff(c_8728, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_7776])).
% 8.02/2.77  tff(c_8730, plain, (k2_relat_1('#skF_6')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_8728, c_7786])).
% 8.02/2.77  tff(c_8729, plain, (k1_relat_1('#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_7776])).
% 8.02/2.77  tff(c_8751, plain, (k1_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_8728, c_8729])).
% 8.02/2.77  tff(c_9145, plain, (![A_881]: (k2_relat_1(k2_funct_1(A_881))=k1_relat_1(A_881) | ~v2_funct_1(A_881) | ~v1_funct_1(A_881) | ~v1_relat_1(A_881))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.02/2.77  tff(c_7766, plain, (v1_relat_1(k2_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_7538, c_7746])).
% 8.02/2.77  tff(c_7783, plain, (k2_relat_1(k2_funct_1('#skF_6'))!=k1_xboole_0 | k2_funct_1('#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_7766, c_30])).
% 8.02/2.77  tff(c_8915, plain, (k2_relat_1(k2_funct_1('#skF_6'))!='#skF_6' | k2_funct_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_8728, c_8728, c_7783])).
% 8.02/2.77  tff(c_8916, plain, (k2_relat_1(k2_funct_1('#skF_6'))!='#skF_6'), inference(splitLeft, [status(thm)], [c_8915])).
% 8.02/2.77  tff(c_9154, plain, (k1_relat_1('#skF_6')!='#skF_6' | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_9145, c_8916])).
% 8.02/2.77  tff(c_9161, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7768, c_88, c_82, c_8751, c_9154])).
% 8.02/2.77  tff(c_9162, plain, (k2_funct_1('#skF_6')='#skF_6'), inference(splitRight, [status(thm)], [c_8915])).
% 8.02/2.77  tff(c_7784, plain, (k1_relat_1(k2_funct_1('#skF_6'))!=k1_xboole_0 | k2_funct_1('#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_7766, c_32])).
% 8.02/2.77  tff(c_8872, plain, (k1_relat_1(k2_funct_1('#skF_6'))!='#skF_6' | k2_funct_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_8728, c_8728, c_7784])).
% 8.02/2.77  tff(c_8873, plain, (k1_relat_1(k2_funct_1('#skF_6'))!='#skF_6'), inference(splitLeft, [status(thm)], [c_8872])).
% 8.02/2.77  tff(c_9164, plain, (k1_relat_1('#skF_6')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_9162, c_8873])).
% 8.02/2.77  tff(c_9172, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8751, c_9164])).
% 8.02/2.77  tff(c_9173, plain, (k2_funct_1('#skF_6')='#skF_6'), inference(splitRight, [status(thm)], [c_8872])).
% 8.02/2.77  tff(c_9418, plain, (![A_909]: (k2_relat_1(k2_funct_1(A_909))=k1_relat_1(A_909) | ~v2_funct_1(A_909) | ~v1_funct_1(A_909) | ~v1_relat_1(A_909))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.02/2.77  tff(c_9430, plain, (k2_relat_1('#skF_6')=k1_relat_1('#skF_6') | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_9173, c_9418])).
% 8.02/2.77  tff(c_9434, plain, (k2_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_7768, c_88, c_82, c_8751, c_9430])).
% 8.02/2.77  tff(c_9436, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8730, c_9434])).
% 8.02/2.77  tff(c_9437, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_7775])).
% 8.02/2.77  tff(c_7598, plain, (![A_725, B_726]: (m1_subset_1('#skF_3'(A_725, B_726), k1_zfmisc_1(k2_zfmisc_1(A_725, B_726))))), inference(cnfTransformation, [status(thm)], [f_124])).
% 8.02/2.77  tff(c_7609, plain, (![B_727]: (m1_subset_1('#skF_3'(k1_xboole_0, B_727), k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_7598])).
% 8.02/2.77  tff(c_7614, plain, (![B_728]: (r1_tarski('#skF_3'(k1_xboole_0, B_728), k1_xboole_0))), inference(resolution, [status(thm)], [c_7609, c_26])).
% 8.02/2.77  tff(c_7571, plain, (![A_719, B_720]: (r2_hidden('#skF_2'(A_719, B_720), A_719) | r1_tarski(A_719, B_720))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.02/2.77  tff(c_7576, plain, (![A_721, B_722]: (~v1_xboole_0(A_721) | r1_tarski(A_721, B_722))), inference(resolution, [status(thm)], [c_7571, c_2])).
% 8.02/2.77  tff(c_14, plain, (![B_11, A_10]: (B_11=A_10 | ~r1_tarski(B_11, A_10) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.02/2.77  tff(c_7579, plain, (![B_722, A_721]: (B_722=A_721 | ~r1_tarski(B_722, A_721) | ~v1_xboole_0(A_721))), inference(resolution, [status(thm)], [c_7576, c_14])).
% 8.02/2.77  tff(c_7617, plain, (![B_728]: ('#skF_3'(k1_xboole_0, B_728)=k1_xboole_0 | ~v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_7614, c_7579])).
% 8.02/2.77  tff(c_7627, plain, (![B_729]: ('#skF_3'(k1_xboole_0, B_729)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_7617])).
% 8.02/2.77  tff(c_7635, plain, (![B_729]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_729))), inference(superposition, [status(thm), theory('equality')], [c_7627, c_60])).
% 8.02/2.77  tff(c_9442, plain, (![B_729]: (v1_funct_2('#skF_6', '#skF_6', B_729))), inference(demodulation, [status(thm), theory('equality')], [c_9437, c_9437, c_7635])).
% 8.02/2.77  tff(c_9452, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_9437, c_12])).
% 8.02/2.77  tff(c_9450, plain, (![B_13]: (k2_zfmisc_1('#skF_6', B_13)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_9437, c_9437, c_24])).
% 8.02/2.77  tff(c_9438, plain, (k2_relat_1('#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_7775])).
% 8.02/2.77  tff(c_9459, plain, (k2_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_9437, c_9438])).
% 8.02/2.77  tff(c_10199, plain, (![A_989, B_990, C_991]: (k2_relset_1(A_989, B_990, C_991)=k2_relat_1(C_991) | ~m1_subset_1(C_991, k1_zfmisc_1(k2_zfmisc_1(A_989, B_990))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 8.02/2.77  tff(c_10218, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_84, c_10199])).
% 8.02/2.77  tff(c_10224, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_9459, c_10218])).
% 8.02/2.77  tff(c_7575, plain, (![A_719, B_720]: (~v1_xboole_0(A_719) | r1_tarski(A_719, B_720))), inference(resolution, [status(thm)], [c_7571, c_2])).
% 8.02/2.77  tff(c_9823, plain, (![A_949]: (k1_relat_1(k2_funct_1(A_949))=k2_relat_1(A_949) | ~v2_funct_1(A_949) | ~v1_funct_1(A_949) | ~v1_relat_1(A_949))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.02/2.77  tff(c_9581, plain, (k1_relat_1(k2_funct_1('#skF_6'))!='#skF_6' | k2_funct_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_9437, c_9437, c_7784])).
% 8.02/2.77  tff(c_9582, plain, (k1_relat_1(k2_funct_1('#skF_6'))!='#skF_6'), inference(splitLeft, [status(thm)], [c_9581])).
% 8.02/2.77  tff(c_9832, plain, (k2_relat_1('#skF_6')!='#skF_6' | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_9823, c_9582])).
% 8.02/2.77  tff(c_9839, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7768, c_88, c_82, c_9459, c_9832])).
% 8.02/2.77  tff(c_9840, plain, (k2_funct_1('#skF_6')='#skF_6'), inference(splitRight, [status(thm)], [c_9581])).
% 8.02/2.77  tff(c_7542, plain, (r1_tarski(k2_funct_1('#skF_6'), k2_zfmisc_1('#skF_5', '#skF_4'))), inference(resolution, [status(thm)], [c_7538, c_26])).
% 8.02/2.77  tff(c_7558, plain, (![B_717, A_718]: (B_717=A_718 | ~r1_tarski(B_717, A_718) | ~r1_tarski(A_718, B_717))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.02/2.77  tff(c_7565, plain, (k2_zfmisc_1('#skF_5', '#skF_4')=k2_funct_1('#skF_6') | ~r1_tarski(k2_zfmisc_1('#skF_5', '#skF_4'), k2_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_7542, c_7558])).
% 8.02/2.77  tff(c_10080, plain, (k2_zfmisc_1('#skF_5', '#skF_4')='#skF_6' | ~r1_tarski(k2_zfmisc_1('#skF_5', '#skF_4'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_9840, c_9840, c_7565])).
% 8.02/2.77  tff(c_10081, plain, (~r1_tarski(k2_zfmisc_1('#skF_5', '#skF_4'), '#skF_6')), inference(splitLeft, [status(thm)], [c_10080])).
% 8.02/2.77  tff(c_10085, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_5', '#skF_4'))), inference(resolution, [status(thm)], [c_7575, c_10081])).
% 8.02/2.77  tff(c_10225, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_6', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_10224, c_10085])).
% 8.02/2.77  tff(c_10238, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9452, c_9450, c_10225])).
% 8.02/2.77  tff(c_10239, plain, (k2_zfmisc_1('#skF_5', '#skF_4')='#skF_6'), inference(splitRight, [status(thm)], [c_10080])).
% 8.02/2.77  tff(c_9527, plain, (![B_13, A_12]: (B_13='#skF_6' | A_12='#skF_6' | k2_zfmisc_1(A_12, B_13)!='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_9437, c_9437, c_9437, c_20])).
% 8.02/2.77  tff(c_10264, plain, ('#skF_6'='#skF_4' | '#skF_5'='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_10239, c_9527])).
% 8.02/2.77  tff(c_10266, plain, ('#skF_5'='#skF_6'), inference(splitLeft, [status(thm)], [c_10264])).
% 8.02/2.77  tff(c_9845, plain, (~v1_funct_2('#skF_6', '#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9840, c_7537])).
% 8.02/2.77  tff(c_10270, plain, (~v1_funct_2('#skF_6', '#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10266, c_9845])).
% 8.02/2.77  tff(c_10280, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9442, c_10270])).
% 8.02/2.77  tff(c_10281, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_10264])).
% 8.02/2.77  tff(c_10305, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10281, c_9452])).
% 8.02/2.77  tff(c_10300, plain, (![B_13]: (k2_zfmisc_1('#skF_4', B_13)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10281, c_10281, c_9450])).
% 8.02/2.77  tff(c_7580, plain, (![B_723, A_724]: (B_723=A_724 | ~r1_tarski(B_723, A_724) | ~v1_xboole_0(A_724))), inference(resolution, [status(thm)], [c_7576, c_14])).
% 8.02/2.77  tff(c_7595, plain, (k2_zfmisc_1('#skF_4', '#skF_5')='#skF_6' | ~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_146, c_7580])).
% 8.02/2.77  tff(c_7651, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_7595])).
% 8.02/2.77  tff(c_10401, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10300, c_7651])).
% 8.02/2.77  tff(c_10404, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10305, c_10401])).
% 8.02/2.77  tff(c_10405, plain, (k2_zfmisc_1('#skF_4', '#skF_5')='#skF_6'), inference(splitRight, [status(thm)], [c_7595])).
% 8.02/2.77  tff(c_7566, plain, (k2_zfmisc_1('#skF_4', '#skF_5')='#skF_6' | ~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), '#skF_6')), inference(resolution, [status(thm)], [c_146, c_7558])).
% 8.02/2.77  tff(c_10407, plain, (~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), '#skF_6')), inference(splitLeft, [status(thm)], [c_7566])).
% 8.02/2.77  tff(c_10455, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_10405, c_10407])).
% 8.02/2.77  tff(c_10456, plain, (k2_zfmisc_1('#skF_4', '#skF_5')='#skF_6'), inference(splitRight, [status(thm)], [c_7566])).
% 8.02/2.77  tff(c_10479, plain, (![B_1000, A_1001]: (k1_xboole_0=B_1000 | k1_xboole_0=A_1001 | k2_zfmisc_1(A_1001, B_1000)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.02/2.77  tff(c_10482, plain, (k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0!='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_10456, c_10479])).
% 8.02/2.77  tff(c_10601, plain, (k1_xboole_0!='#skF_6'), inference(splitLeft, [status(thm)], [c_10482])).
% 8.02/2.77  tff(c_10406, plain, (v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_7595])).
% 8.02/2.77  tff(c_10504, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_10456, c_10406])).
% 8.02/2.77  tff(c_10703, plain, (![B_1019, A_1020]: (B_1019=A_1020 | ~v1_xboole_0(B_1019) | ~v1_xboole_0(A_1020))), inference(resolution, [status(thm)], [c_7575, c_7580])).
% 8.02/2.77  tff(c_10710, plain, (![A_1021]: (A_1021='#skF_6' | ~v1_xboole_0(A_1021))), inference(resolution, [status(thm)], [c_10504, c_10703])).
% 8.02/2.77  tff(c_10716, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_12, c_10710])).
% 8.02/2.77  tff(c_10722, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10601, c_10716])).
% 8.02/2.77  tff(c_10724, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_10482])).
% 8.02/2.77  tff(c_10727, plain, (![B_729]: (v1_funct_2('#skF_6', '#skF_6', B_729))), inference(demodulation, [status(thm), theory('equality')], [c_10724, c_10724, c_7635])).
% 8.02/2.77  tff(c_10736, plain, (![B_13]: (k2_zfmisc_1('#skF_6', B_13)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_10724, c_10724, c_24])).
% 8.02/2.77  tff(c_10723, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_10482])).
% 8.02/2.77  tff(c_10799, plain, ('#skF_6'='#skF_4' | '#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_10724, c_10724, c_10723])).
% 8.02/2.77  tff(c_10800, plain, ('#skF_5'='#skF_6'), inference(splitLeft, [status(thm)], [c_10799])).
% 8.02/2.77  tff(c_10803, plain, (r1_tarski(k2_funct_1('#skF_6'), k2_zfmisc_1('#skF_6', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_10800, c_7542])).
% 8.02/2.77  tff(c_10808, plain, (r1_tarski(k2_funct_1('#skF_6'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_10736, c_10803])).
% 8.02/2.77  tff(c_10873, plain, (k2_funct_1('#skF_6')='#skF_6' | ~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_10808, c_7579])).
% 8.02/2.77  tff(c_10878, plain, (k2_funct_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_10504, c_10873])).
% 8.02/2.77  tff(c_10805, plain, (~v1_funct_2(k2_funct_1('#skF_6'), '#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10800, c_7537])).
% 8.02/2.77  tff(c_10918, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10727, c_10878, c_10805])).
% 8.02/2.77  tff(c_10919, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_10799])).
% 8.02/2.77  tff(c_10927, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_10919, c_10724])).
% 8.02/2.77  tff(c_10508, plain, (![A_1003]: (m1_subset_1('#skF_3'(A_1003, k1_xboole_0), k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_7598])).
% 8.02/2.77  tff(c_10517, plain, (![A_1004]: (r1_tarski('#skF_3'(A_1004, k1_xboole_0), k1_xboole_0))), inference(resolution, [status(thm)], [c_10508, c_26])).
% 8.02/2.77  tff(c_10520, plain, (![A_1004]: ('#skF_3'(A_1004, k1_xboole_0)=k1_xboole_0 | ~v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_10517, c_7579])).
% 8.02/2.77  tff(c_10564, plain, (![A_1008]: ('#skF_3'(A_1008, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_10520])).
% 8.02/2.77  tff(c_10575, plain, (![A_1008]: (v1_funct_2(k1_xboole_0, A_1008, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10564, c_60])).
% 8.02/2.77  tff(c_11185, plain, (![A_1008]: (v1_funct_2('#skF_4', A_1008, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_10927, c_10927, c_10575])).
% 8.02/2.77  tff(c_10929, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10919, c_10504])).
% 8.02/2.77  tff(c_10737, plain, (![A_12]: (k2_zfmisc_1(A_12, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_10724, c_10724, c_22])).
% 8.02/2.77  tff(c_11100, plain, (![A_12]: (k2_zfmisc_1(A_12, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10919, c_10919, c_10737])).
% 8.02/2.77  tff(c_10933, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_10919, c_7538])).
% 8.02/2.77  tff(c_11249, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_11100, c_10933])).
% 8.02/2.77  tff(c_11258, plain, (r1_tarski(k2_funct_1('#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_11249, c_26])).
% 8.02/2.77  tff(c_11264, plain, (k2_funct_1('#skF_4')='#skF_4' | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_11258, c_7579])).
% 8.02/2.77  tff(c_11271, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_10929, c_11264])).
% 8.02/2.77  tff(c_10934, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10919, c_7537])).
% 8.02/2.77  tff(c_11275, plain, (~v1_funct_2('#skF_4', '#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11271, c_10934])).
% 8.02/2.77  tff(c_11282, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11185, c_11275])).
% 8.02/2.77  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.02/2.77  
% 8.02/2.77  Inference rules
% 8.02/2.77  ----------------------
% 8.02/2.77  #Ref     : 0
% 8.02/2.77  #Sup     : 2434
% 8.02/2.77  #Fact    : 0
% 8.02/2.77  #Define  : 0
% 8.02/2.77  #Split   : 47
% 8.02/2.77  #Chain   : 0
% 8.02/2.77  #Close   : 0
% 8.02/2.77  
% 8.02/2.77  Ordering : KBO
% 8.02/2.77  
% 8.02/2.77  Simplification rules
% 8.02/2.77  ----------------------
% 8.02/2.77  #Subsume      : 321
% 8.02/2.77  #Demod        : 2508
% 8.02/2.78  #Tautology    : 1470
% 8.02/2.78  #SimpNegUnit  : 36
% 8.02/2.78  #BackRed      : 314
% 8.02/2.78  
% 8.02/2.78  #Partial instantiations: 0
% 8.02/2.78  #Strategies tried      : 1
% 8.02/2.78  
% 8.02/2.78  Timing (in seconds)
% 8.02/2.78  ----------------------
% 8.02/2.78  Preprocessing        : 0.35
% 8.02/2.78  Parsing              : 0.19
% 8.02/2.78  CNF conversion       : 0.02
% 8.02/2.78  Main loop            : 1.55
% 8.02/2.78  Inferencing          : 0.54
% 8.02/2.78  Reduction            : 0.54
% 8.02/2.78  Demodulation         : 0.38
% 8.02/2.78  BG Simplification    : 0.06
% 8.02/2.78  Subsumption          : 0.28
% 8.02/2.78  Abstraction          : 0.07
% 8.02/2.78  MUC search           : 0.00
% 8.02/2.78  Cooper               : 0.00
% 8.02/2.78  Total                : 2.00
% 8.02/2.78  Index Insertion      : 0.00
% 8.02/2.78  Index Deletion       : 0.00
% 8.02/2.78  Index Matching       : 0.00
% 8.02/2.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
