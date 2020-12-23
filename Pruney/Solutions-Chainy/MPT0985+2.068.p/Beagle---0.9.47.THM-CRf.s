%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:36 EST 2020

% Result     : Theorem 11.90s
% Output     : CNFRefutation 11.90s
% Verified   : 
% Statistics : Number of formulae       :  274 (1968 expanded)
%              Number of leaves         :   47 ( 651 expanded)
%              Depth                    :   13
%              Number of atoms          :  451 (5316 expanded)
%              Number of equality atoms :  150 (1194 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v5_ordinal1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_4

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v5_ordinal1,type,(
    v5_ordinal1: $i > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_165,negated_conjecture,(
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

tff(f_98,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_106,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_86,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_76,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_102,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_126,axiom,(
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

tff(f_136,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_38,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_148,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_108,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(c_94,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_257,plain,(
    ! [C_75,A_76,B_77] :
      ( v1_relat_1(C_75)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_269,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_94,c_257])).

tff(c_98,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_14,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_92,plain,(
    v2_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_90,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') = '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_14415,plain,(
    ! [A_297,B_298,C_299] :
      ( k2_relset_1(A_297,B_298,C_299) = k2_relat_1(C_299)
      | ~ m1_subset_1(C_299,k1_zfmisc_1(k2_zfmisc_1(A_297,B_298))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_14424,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_94,c_14415])).

tff(c_14434,plain,(
    k2_relat_1('#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_14424])).

tff(c_46,plain,(
    ! [A_33] :
      ( k1_relat_1(k2_funct_1(A_33)) = k2_relat_1(A_33)
      | ~ v2_funct_1(A_33)
      | ~ v1_funct_1(A_33)
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_163,plain,(
    ! [A_61] :
      ( v1_funct_1(k2_funct_1(A_61))
      | ~ v1_funct_1(A_61)
      | ~ v1_relat_1(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_88,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_8'),k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_6')))
    | ~ v1_funct_2(k2_funct_1('#skF_8'),'#skF_7','#skF_6')
    | ~ v1_funct_1(k2_funct_1('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_160,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_88])).

tff(c_166,plain,
    ( ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_163,c_160])).

tff(c_169,plain,(
    ~ v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_166])).

tff(c_203,plain,(
    ! [C_66,A_67,B_68] :
      ( v1_relat_1(C_66)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_209,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_94,c_203])).

tff(c_218,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_169,c_209])).

tff(c_219,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_8'),'#skF_7','#skF_6')
    | ~ m1_subset_1(k2_funct_1('#skF_8'),k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_395,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_8'),k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_219])).

tff(c_490,plain,(
    ! [A_98,B_99,C_100] :
      ( k2_relset_1(A_98,B_99,C_100) = k2_relat_1(C_100)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(A_98,B_99))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_499,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_94,c_490])).

tff(c_509,plain,(
    k2_relat_1('#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_499])).

tff(c_42,plain,(
    ! [A_32] :
      ( v1_relat_1(k2_funct_1(A_32))
      | ~ v1_funct_1(A_32)
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_220,plain,(
    v1_funct_1(k2_funct_1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_36,plain,(
    ! [A_31] :
      ( k1_relat_1(A_31) = k1_xboole_0
      | k2_relat_1(A_31) != k1_xboole_0
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_276,plain,
    ( k1_relat_1('#skF_8') = k1_xboole_0
    | k2_relat_1('#skF_8') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_269,c_36])).

tff(c_293,plain,(
    k2_relat_1('#skF_8') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_276])).

tff(c_510,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_509,c_293])).

tff(c_96,plain,(
    v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_467,plain,(
    ! [A_95,B_96,C_97] :
      ( k1_relset_1(A_95,B_96,C_97) = k1_relat_1(C_97)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_485,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_94,c_467])).

tff(c_1765,plain,(
    ! [B_155,A_156,C_157] :
      ( k1_xboole_0 = B_155
      | k1_relset_1(A_156,B_155,C_157) = A_156
      | ~ v1_funct_2(C_157,A_156,B_155)
      | ~ m1_subset_1(C_157,k1_zfmisc_1(k2_zfmisc_1(A_156,B_155))) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_1780,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_8') = '#skF_6'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_94,c_1765])).

tff(c_1797,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_485,c_1780])).

tff(c_1798,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_510,c_1797])).

tff(c_412,plain,(
    ! [A_91] :
      ( k2_relat_1(k2_funct_1(A_91)) = k1_relat_1(A_91)
      | ~ v2_funct_1(A_91)
      | ~ v1_funct_1(A_91)
      | ~ v1_relat_1(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_78,plain,(
    ! [A_48] :
      ( v1_funct_2(A_48,k1_relat_1(A_48),k2_relat_1(A_48))
      | ~ v1_funct_1(A_48)
      | ~ v1_relat_1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_11321,plain,(
    ! [A_279] :
      ( v1_funct_2(k2_funct_1(A_279),k1_relat_1(k2_funct_1(A_279)),k1_relat_1(A_279))
      | ~ v1_funct_1(k2_funct_1(A_279))
      | ~ v1_relat_1(k2_funct_1(A_279))
      | ~ v2_funct_1(A_279)
      | ~ v1_funct_1(A_279)
      | ~ v1_relat_1(A_279) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_412,c_78])).

tff(c_11324,plain,
    ( v1_funct_2(k2_funct_1('#skF_8'),k1_relat_1(k2_funct_1('#skF_8')),'#skF_6')
    | ~ v1_funct_1(k2_funct_1('#skF_8'))
    | ~ v1_relat_1(k2_funct_1('#skF_8'))
    | ~ v2_funct_1('#skF_8')
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_1798,c_11321])).

tff(c_11335,plain,
    ( v1_funct_2(k2_funct_1('#skF_8'),k1_relat_1(k2_funct_1('#skF_8')),'#skF_6')
    | ~ v1_relat_1(k2_funct_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_269,c_98,c_92,c_220,c_11324])).

tff(c_11338,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_11335])).

tff(c_11341,plain,
    ( ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_42,c_11338])).

tff(c_11345,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_269,c_98,c_11341])).

tff(c_11347,plain,(
    v1_relat_1(k2_funct_1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_11335])).

tff(c_44,plain,(
    ! [A_33] :
      ( k2_relat_1(k2_funct_1(A_33)) = k1_relat_1(A_33)
      | ~ v2_funct_1(A_33)
      | ~ v1_funct_1(A_33)
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_437,plain,(
    ! [A_94] :
      ( m1_subset_1(A_94,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_94),k2_relat_1(A_94))))
      | ~ v1_funct_1(A_94)
      | ~ v1_relat_1(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_14278,plain,(
    ! [A_293] :
      ( m1_subset_1(k2_funct_1(A_293),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_293)),k1_relat_1(A_293))))
      | ~ v1_funct_1(k2_funct_1(A_293))
      | ~ v1_relat_1(k2_funct_1(A_293))
      | ~ v2_funct_1(A_293)
      | ~ v1_funct_1(A_293)
      | ~ v1_relat_1(A_293) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_437])).

tff(c_14299,plain,
    ( m1_subset_1(k2_funct_1('#skF_8'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_8')),'#skF_6')))
    | ~ v1_funct_1(k2_funct_1('#skF_8'))
    | ~ v1_relat_1(k2_funct_1('#skF_8'))
    | ~ v2_funct_1('#skF_8')
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_1798,c_14278])).

tff(c_14316,plain,(
    m1_subset_1(k2_funct_1('#skF_8'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_8')),'#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_269,c_98,c_92,c_11347,c_220,c_14299])).

tff(c_14339,plain,
    ( m1_subset_1(k2_funct_1('#skF_8'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_8'),'#skF_6')))
    | ~ v2_funct_1('#skF_8')
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_14316])).

tff(c_14353,plain,(
    m1_subset_1(k2_funct_1('#skF_8'),k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_269,c_98,c_92,c_509,c_14339])).

tff(c_14355,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_395,c_14353])).

tff(c_14356,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_8'),'#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_219])).

tff(c_14435,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14434,c_293])).

tff(c_14555,plain,(
    ! [A_309,B_310,C_311] :
      ( k1_relset_1(A_309,B_310,C_311) = k1_relat_1(C_311)
      | ~ m1_subset_1(C_311,k1_zfmisc_1(k2_zfmisc_1(A_309,B_310))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_14581,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_94,c_14555])).

tff(c_17504,plain,(
    ! [B_380,A_381,C_382] :
      ( k1_xboole_0 = B_380
      | k1_relset_1(A_381,B_380,C_382) = A_381
      | ~ v1_funct_2(C_382,A_381,B_380)
      | ~ m1_subset_1(C_382,k1_zfmisc_1(k2_zfmisc_1(A_381,B_380))) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_17522,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_8') = '#skF_6'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_94,c_17504])).

tff(c_17541,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_14581,c_17522])).

tff(c_17542,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_14435,c_17541])).

tff(c_38,plain,(
    ! [A_31] :
      ( k2_relat_1(A_31) = k1_xboole_0
      | k1_relat_1(A_31) != k1_xboole_0
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_277,plain,
    ( k2_relat_1('#skF_8') = k1_xboole_0
    | k1_relat_1('#skF_8') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_269,c_38])).

tff(c_340,plain,(
    k1_relat_1('#skF_8') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_293,c_277])).

tff(c_17550,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17542,c_340])).

tff(c_14357,plain,(
    m1_subset_1(k2_funct_1('#skF_8'),k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_219])).

tff(c_14579,plain,(
    k1_relset_1('#skF_7','#skF_6',k2_funct_1('#skF_8')) = k1_relat_1(k2_funct_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_14357,c_14555])).

tff(c_17644,plain,(
    ! [B_387,C_388,A_389] :
      ( k1_xboole_0 = B_387
      | v1_funct_2(C_388,A_389,B_387)
      | k1_relset_1(A_389,B_387,C_388) != A_389
      | ~ m1_subset_1(C_388,k1_zfmisc_1(k2_zfmisc_1(A_389,B_387))) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_17656,plain,
    ( k1_xboole_0 = '#skF_6'
    | v1_funct_2(k2_funct_1('#skF_8'),'#skF_7','#skF_6')
    | k1_relset_1('#skF_7','#skF_6',k2_funct_1('#skF_8')) != '#skF_7' ),
    inference(resolution,[status(thm)],[c_14357,c_17644])).

tff(c_17673,plain,
    ( k1_xboole_0 = '#skF_6'
    | v1_funct_2(k2_funct_1('#skF_8'),'#skF_7','#skF_6')
    | k1_relat_1(k2_funct_1('#skF_8')) != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14579,c_17656])).

tff(c_17674,plain,(
    k1_relat_1(k2_funct_1('#skF_8')) != '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_14356,c_17550,c_17673])).

tff(c_17684,plain,
    ( k2_relat_1('#skF_8') != '#skF_7'
    | ~ v2_funct_1('#skF_8')
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_17674])).

tff(c_17687,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_269,c_98,c_92,c_14434,c_17684])).

tff(c_17688,plain,(
    k1_relat_1('#skF_8') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_276])).

tff(c_17689,plain,(
    k2_relat_1('#skF_8') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_276])).

tff(c_31803,plain,(
    ! [A_783] :
      ( m1_subset_1(A_783,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_783),k2_relat_1(A_783))))
      | ~ v1_funct_1(A_783)
      | ~ v1_relat_1(A_783) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_31830,plain,
    ( m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_8'),k1_xboole_0)))
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_17689,c_31803])).

tff(c_31850,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_269,c_98,c_14,c_17688,c_31830])).

tff(c_18,plain,(
    ! [B_11,A_9] :
      ( v1_xboole_0(B_11)
      | ~ m1_subset_1(B_11,k1_zfmisc_1(A_9))
      | ~ v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_31859,plain,
    ( v1_xboole_0('#skF_8')
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_31850,c_18])).

tff(c_31865,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_31859])).

tff(c_8,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_31871,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_31865,c_8])).

tff(c_16,plain,(
    ! [B_8] : k2_zfmisc_1(k1_xboole_0,B_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_31893,plain,(
    ! [B_8] : k2_zfmisc_1('#skF_8',B_8) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31871,c_31871,c_16])).

tff(c_31885,plain,(
    k2_relat_1('#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31871,c_17689])).

tff(c_31970,plain,(
    ! [A_788,B_789,C_790] :
      ( k2_relset_1(A_788,B_789,C_790) = k2_relat_1(C_790)
      | ~ m1_subset_1(C_790,k1_zfmisc_1(k2_zfmisc_1(A_788,B_789))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_31982,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_94,c_31970])).

tff(c_31987,plain,(
    '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31885,c_90,c_31982])).

tff(c_17912,plain,(
    ! [A_413,B_414,C_415] :
      ( k2_relset_1(A_413,B_414,C_415) = k2_relat_1(C_415)
      | ~ m1_subset_1(C_415,k1_zfmisc_1(k2_zfmisc_1(A_413,B_414))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_17918,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_94,c_17912])).

tff(c_17927,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17689,c_90,c_17918])).

tff(c_17954,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17927,c_6])).

tff(c_17947,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,'#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17927,c_17927,c_14])).

tff(c_17701,plain,(
    ! [B_390,A_391] :
      ( v1_xboole_0(B_390)
      | ~ m1_subset_1(B_390,k1_zfmisc_1(A_391))
      | ~ v1_xboole_0(A_391) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_17715,plain,
    ( v1_xboole_0('#skF_8')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_94,c_17701])).

tff(c_17747,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_17715])).

tff(c_18060,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17947,c_17747])).

tff(c_18064,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_17954,c_18060])).

tff(c_18065,plain,(
    v1_xboole_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_17715])).

tff(c_18073,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_18065,c_8])).

tff(c_18085,plain,(
    ! [B_8] : k2_zfmisc_1('#skF_8',B_8) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18073,c_18073,c_16])).

tff(c_18084,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,'#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18073,c_18073,c_14])).

tff(c_18066,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_17715])).

tff(c_18148,plain,(
    ! [A_424] :
      ( A_424 = '#skF_8'
      | ~ v1_xboole_0(A_424) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18073,c_8])).

tff(c_18155,plain,(
    k2_zfmisc_1('#skF_6','#skF_7') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_18066,c_18148])).

tff(c_12,plain,(
    ! [B_8,A_7] :
      ( k1_xboole_0 = B_8
      | k1_xboole_0 = A_7
      | k2_zfmisc_1(A_7,B_8) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_18336,plain,(
    ! [B_439,A_440] :
      ( B_439 = '#skF_8'
      | A_440 = '#skF_8'
      | k2_zfmisc_1(A_440,B_439) != '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18073,c_18073,c_18073,c_12])).

tff(c_18346,plain,
    ( '#skF_7' = '#skF_8'
    | '#skF_6' = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_18155,c_18336])).

tff(c_18351,plain,(
    '#skF_6' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_18346])).

tff(c_17698,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_8'),k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_219])).

tff(c_18367,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_8'),k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18351,c_17698])).

tff(c_18371,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_8'),k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18084,c_18367])).

tff(c_18077,plain,(
    k2_relat_1('#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18073,c_17689])).

tff(c_18232,plain,(
    ! [A_430] :
      ( k1_relat_1(k2_funct_1(A_430)) = k2_relat_1(A_430)
      | ~ v2_funct_1(A_430)
      | ~ v1_funct_1(A_430)
      | ~ v1_relat_1(A_430) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_23970,plain,(
    ! [A_596] :
      ( v1_funct_2(k2_funct_1(A_596),k2_relat_1(A_596),k2_relat_1(k2_funct_1(A_596)))
      | ~ v1_funct_1(k2_funct_1(A_596))
      | ~ v1_relat_1(k2_funct_1(A_596))
      | ~ v2_funct_1(A_596)
      | ~ v1_funct_1(A_596)
      | ~ v1_relat_1(A_596) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18232,c_78])).

tff(c_24021,plain,
    ( v1_funct_2(k2_funct_1('#skF_8'),'#skF_8',k2_relat_1(k2_funct_1('#skF_8')))
    | ~ v1_funct_1(k2_funct_1('#skF_8'))
    | ~ v1_relat_1(k2_funct_1('#skF_8'))
    | ~ v2_funct_1('#skF_8')
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_18077,c_23970])).

tff(c_24025,plain,
    ( v1_funct_2(k2_funct_1('#skF_8'),'#skF_8',k2_relat_1(k2_funct_1('#skF_8')))
    | ~ v1_relat_1(k2_funct_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_269,c_98,c_92,c_220,c_24021])).

tff(c_24026,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_24025])).

tff(c_24029,plain,
    ( ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_42,c_24026])).

tff(c_24033,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_269,c_98,c_24029])).

tff(c_24035,plain,(
    v1_relat_1(k2_funct_1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_24025])).

tff(c_18078,plain,(
    k1_relat_1('#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18073,c_17688])).

tff(c_18080,plain,(
    ! [A_31] :
      ( k1_relat_1(A_31) = '#skF_8'
      | k2_relat_1(A_31) != '#skF_8'
      | ~ v1_relat_1(A_31) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18073,c_18073,c_36])).

tff(c_24043,plain,
    ( k1_relat_1(k2_funct_1('#skF_8')) = '#skF_8'
    | k2_relat_1(k2_funct_1('#skF_8')) != '#skF_8' ),
    inference(resolution,[status(thm)],[c_24035,c_18080])).

tff(c_24063,plain,(
    k2_relat_1(k2_funct_1('#skF_8')) != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_24043])).

tff(c_24069,plain,
    ( k1_relat_1('#skF_8') != '#skF_8'
    | ~ v2_funct_1('#skF_8')
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_24063])).

tff(c_24075,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_269,c_98,c_92,c_18078,c_24069])).

tff(c_24076,plain,(
    k1_relat_1(k2_funct_1('#skF_8')) = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_24043])).

tff(c_76,plain,(
    ! [A_48] :
      ( m1_subset_1(A_48,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_48),k2_relat_1(A_48))))
      | ~ v1_funct_1(A_48)
      | ~ v1_relat_1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_24099,plain,
    ( m1_subset_1(k2_funct_1('#skF_8'),k1_zfmisc_1(k2_zfmisc_1('#skF_8',k2_relat_1(k2_funct_1('#skF_8')))))
    | ~ v1_funct_1(k2_funct_1('#skF_8'))
    | ~ v1_relat_1(k2_funct_1('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_24076,c_76])).

tff(c_24125,plain,(
    m1_subset_1(k2_funct_1('#skF_8'),k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24035,c_220,c_18085,c_24099])).

tff(c_24127,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18371,c_24125])).

tff(c_24128,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_18346])).

tff(c_24131,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_8'),k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24128,c_17698])).

tff(c_24135,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_8'),k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18085,c_24131])).

tff(c_31331,plain,(
    ! [A_762] :
      ( v1_funct_2(k2_funct_1(A_762),k2_relat_1(A_762),k2_relat_1(k2_funct_1(A_762)))
      | ~ v1_funct_1(k2_funct_1(A_762))
      | ~ v1_relat_1(k2_funct_1(A_762))
      | ~ v2_funct_1(A_762)
      | ~ v1_funct_1(A_762)
      | ~ v1_relat_1(A_762) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18232,c_78])).

tff(c_31388,plain,
    ( v1_funct_2(k2_funct_1('#skF_8'),'#skF_8',k2_relat_1(k2_funct_1('#skF_8')))
    | ~ v1_funct_1(k2_funct_1('#skF_8'))
    | ~ v1_relat_1(k2_funct_1('#skF_8'))
    | ~ v2_funct_1('#skF_8')
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_18077,c_31331])).

tff(c_31394,plain,
    ( v1_funct_2(k2_funct_1('#skF_8'),'#skF_8',k2_relat_1(k2_funct_1('#skF_8')))
    | ~ v1_relat_1(k2_funct_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_269,c_98,c_92,c_220,c_31388])).

tff(c_31395,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_31394])).

tff(c_31398,plain,
    ( ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_42,c_31395])).

tff(c_31402,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_269,c_98,c_31398])).

tff(c_31404,plain,(
    v1_relat_1(k2_funct_1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_31394])).

tff(c_31412,plain,
    ( k1_relat_1(k2_funct_1('#skF_8')) = '#skF_8'
    | k2_relat_1(k2_funct_1('#skF_8')) != '#skF_8' ),
    inference(resolution,[status(thm)],[c_31404,c_18080])).

tff(c_31432,plain,(
    k2_relat_1(k2_funct_1('#skF_8')) != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_31412])).

tff(c_31438,plain,
    ( k1_relat_1('#skF_8') != '#skF_8'
    | ~ v2_funct_1('#skF_8')
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_31432])).

tff(c_31444,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_269,c_98,c_92,c_18078,c_31438])).

tff(c_31445,plain,(
    k1_relat_1(k2_funct_1('#skF_8')) = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_31412])).

tff(c_31468,plain,
    ( m1_subset_1(k2_funct_1('#skF_8'),k1_zfmisc_1(k2_zfmisc_1('#skF_8',k2_relat_1(k2_funct_1('#skF_8')))))
    | ~ v1_funct_1(k2_funct_1('#skF_8'))
    | ~ v1_relat_1(k2_funct_1('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_31445,c_76])).

tff(c_31494,plain,(
    m1_subset_1(k2_funct_1('#skF_8'),k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31404,c_220,c_18085,c_31468])).

tff(c_31496,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24135,c_31494])).

tff(c_31498,plain,(
    m1_subset_1(k2_funct_1('#skF_8'),k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_219])).

tff(c_31513,plain,(
    ! [B_763,A_764] :
      ( v1_xboole_0(B_763)
      | ~ m1_subset_1(B_763,k1_zfmisc_1(A_764))
      | ~ v1_xboole_0(A_764) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_31526,plain,
    ( v1_xboole_0(k2_funct_1('#skF_8'))
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_7','#skF_6')) ),
    inference(resolution,[status(thm)],[c_31498,c_31513])).

tff(c_31564,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_7','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_31526])).

tff(c_31989,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_8','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31987,c_31564])).

tff(c_32144,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_31865,c_31893,c_31989])).

tff(c_32146,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_7','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_31526])).

tff(c_32154,plain,(
    k2_zfmisc_1('#skF_7','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32146,c_8])).

tff(c_32187,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_32154,c_12])).

tff(c_32189,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_32187])).

tff(c_32209,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32189,c_6])).

tff(c_32202,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,'#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32189,c_32189,c_14])).

tff(c_31531,plain,
    ( v1_xboole_0('#skF_8')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_94,c_31513])).

tff(c_31532,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_31531])).

tff(c_32291,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32202,c_31532])).

tff(c_32295,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32209,c_32291])).

tff(c_32296,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_32187])).

tff(c_32317,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32296,c_6])).

tff(c_32311,plain,(
    ! [B_8] : k2_zfmisc_1('#skF_6',B_8) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32296,c_32296,c_16])).

tff(c_32401,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32311,c_31532])).

tff(c_32405,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32317,c_32401])).

tff(c_32406,plain,(
    v1_xboole_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_31531])).

tff(c_32411,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_32406,c_8])).

tff(c_10,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_32423,plain,(
    ! [A_6] : r1_tarski('#skF_8',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32411,c_10])).

tff(c_32412,plain,(
    k2_relat_1('#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32411,c_17689])).

tff(c_32413,plain,(
    k1_relat_1('#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32411,c_17688])).

tff(c_33873,plain,(
    ! [B_865,A_866] :
      ( v1_funct_2(B_865,k1_relat_1(B_865),A_866)
      | ~ r1_tarski(k2_relat_1(B_865),A_866)
      | ~ v1_funct_1(B_865)
      | ~ v1_relat_1(B_865) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_33882,plain,(
    ! [A_866] :
      ( v1_funct_2('#skF_8','#skF_8',A_866)
      | ~ r1_tarski(k2_relat_1('#skF_8'),A_866)
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32413,c_33873])).

tff(c_33885,plain,(
    ! [A_866] : v1_funct_2('#skF_8','#skF_8',A_866) ),
    inference(demodulation,[status(thm),theory(equality)],[c_269,c_98,c_32423,c_32412,c_33882])).

tff(c_32421,plain,(
    ! [B_8] : k2_zfmisc_1('#skF_8',B_8) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32411,c_32411,c_16])).

tff(c_32420,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,'#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32411,c_32411,c_14])).

tff(c_32407,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_31531])).

tff(c_32475,plain,(
    ! [A_809] :
      ( A_809 = '#skF_8'
      | ~ v1_xboole_0(A_809) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32411,c_8])).

tff(c_32485,plain,(
    k2_zfmisc_1('#skF_6','#skF_7') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_32407,c_32475])).

tff(c_32626,plain,(
    ! [B_818,A_819] :
      ( B_818 = '#skF_8'
      | A_819 = '#skF_8'
      | k2_zfmisc_1(A_819,B_818) != '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32411,c_32411,c_32411,c_12])).

tff(c_32636,plain,
    ( '#skF_7' = '#skF_8'
    | '#skF_6' = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_32485,c_32626])).

tff(c_32641,plain,(
    '#skF_6' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_32636])).

tff(c_32553,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_7','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_31526])).

tff(c_32642,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_7','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32641,c_32553])).

tff(c_32650,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32406,c_32420,c_32642])).

tff(c_32651,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_32636])).

tff(c_32653,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_8','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32651,c_32553])).

tff(c_32661,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32406,c_32421,c_32653])).

tff(c_32663,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_7','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_31526])).

tff(c_32419,plain,(
    ! [A_5] :
      ( A_5 = '#skF_8'
      | ~ v1_xboole_0(A_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32411,c_8])).

tff(c_32710,plain,(
    k2_zfmisc_1('#skF_7','#skF_6') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_32663,c_32419])).

tff(c_32774,plain,(
    ! [B_825,A_826] :
      ( B_825 = '#skF_8'
      | A_826 = '#skF_8'
      | k2_zfmisc_1(A_826,B_825) != '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32411,c_32411,c_32411,c_12])).

tff(c_32787,plain,
    ( '#skF_6' = '#skF_8'
    | '#skF_7' = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_32710,c_32774])).

tff(c_32793,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_32787])).

tff(c_32662,plain,(
    v1_xboole_0(k2_funct_1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_31526])).

tff(c_32679,plain,(
    k2_funct_1('#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_32662,c_32419])).

tff(c_31497,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_8'),'#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_219])).

tff(c_32683,plain,(
    ~ v1_funct_2('#skF_8','#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32679,c_31497])).

tff(c_32795,plain,(
    ~ v1_funct_2('#skF_8','#skF_8','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32793,c_32683])).

tff(c_33890,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_33885,c_32795])).

tff(c_33892,plain,(
    '#skF_7' != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_32787])).

tff(c_151,plain,(
    ! [A_59] : m1_subset_1(k6_relat_1(A_59),k1_zfmisc_1(k2_zfmisc_1(A_59,A_59))) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_155,plain,(
    m1_subset_1(k6_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_151])).

tff(c_31519,plain,
    ( v1_xboole_0(k6_relat_1(k1_xboole_0))
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_155,c_31513])).

tff(c_31529,plain,(
    v1_xboole_0(k6_relat_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_31519])).

tff(c_32438,plain,(
    v1_xboole_0(k6_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32411,c_31529])).

tff(c_32486,plain,(
    k6_relat_1('#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_32438,c_32475])).

tff(c_32502,plain,(
    ! [A_810] : k2_zfmisc_1(A_810,'#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32411,c_32411,c_14])).

tff(c_62,plain,(
    ! [A_44] : m1_subset_1(k6_relat_1(A_44),k1_zfmisc_1(k2_zfmisc_1(A_44,A_44))) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_32513,plain,(
    m1_subset_1(k6_relat_1('#skF_8'),k1_zfmisc_1('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_32502,c_62])).

tff(c_32521,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32486,c_32513])).

tff(c_64,plain,(
    ! [A_45] :
      ( v1_funct_2(k1_xboole_0,A_45,k1_xboole_0)
      | k1_xboole_0 = A_45
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_45,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_101,plain,(
    ! [A_45] :
      ( v1_funct_2(k1_xboole_0,A_45,k1_xboole_0)
      | k1_xboole_0 = A_45
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_64])).

tff(c_32543,plain,(
    ! [A_45] :
      ( v1_funct_2('#skF_8',A_45,'#skF_8')
      | A_45 = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32521,c_32411,c_32411,c_32411,c_32411,c_32411,c_101])).

tff(c_33891,plain,(
    '#skF_6' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_32787])).

tff(c_33894,plain,(
    ~ v1_funct_2('#skF_8','#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_33891,c_32683])).

tff(c_33908,plain,(
    '#skF_7' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_32543,c_33894])).

tff(c_33912,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_33892,c_33908])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n016.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 14:26:34 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.17/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.90/5.02  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.90/5.05  
% 11.90/5.05  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.90/5.05  %$ v1_funct_2 > v5_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v5_ordinal1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_4
% 11.90/5.05  
% 11.90/5.05  %Foreground sorts:
% 11.90/5.05  
% 11.90/5.05  
% 11.90/5.05  %Background operators:
% 11.90/5.05  
% 11.90/5.05  
% 11.90/5.05  %Foreground operators:
% 11.90/5.05  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 11.90/5.05  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 11.90/5.05  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 11.90/5.05  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 11.90/5.05  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.90/5.05  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.90/5.05  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 11.90/5.05  tff('#skF_1', type, '#skF_1': $i > $i).
% 11.90/5.05  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.90/5.05  tff('#skF_7', type, '#skF_7': $i).
% 11.90/5.05  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 11.90/5.05  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.90/5.05  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 11.90/5.05  tff(v5_ordinal1, type, v5_ordinal1: $i > $o).
% 11.90/5.05  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 11.90/5.05  tff('#skF_6', type, '#skF_6': $i).
% 11.90/5.05  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 11.90/5.05  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 11.90/5.05  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 11.90/5.05  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.90/5.05  tff('#skF_8', type, '#skF_8': $i).
% 11.90/5.05  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.90/5.05  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 11.90/5.05  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 11.90/5.05  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 11.90/5.05  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.90/5.05  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 11.90/5.05  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 11.90/5.05  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 11.90/5.05  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 11.90/5.05  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.90/5.05  
% 11.90/5.08  tff(f_165, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 11.90/5.08  tff(f_98, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 11.90/5.08  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 11.90/5.08  tff(f_44, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 11.90/5.08  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 11.90/5.08  tff(f_86, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 11.90/5.08  tff(f_76, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 11.90/5.08  tff(f_68, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 11.90/5.08  tff(f_102, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 11.90/5.08  tff(f_126, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 11.90/5.08  tff(f_136, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 11.90/5.08  tff(f_51, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 11.90/5.08  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 11.90/5.08  tff(f_38, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 11.90/5.08  tff(f_148, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 11.90/5.08  tff(f_108, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 11.90/5.08  tff(c_94, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_165])).
% 11.90/5.08  tff(c_257, plain, (![C_75, A_76, B_77]: (v1_relat_1(C_75) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 11.90/5.08  tff(c_269, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_94, c_257])).
% 11.90/5.08  tff(c_98, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_165])).
% 11.90/5.08  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.90/5.08  tff(c_14, plain, (![A_7]: (k2_zfmisc_1(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 11.90/5.08  tff(c_92, plain, (v2_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_165])).
% 11.90/5.08  tff(c_90, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')='#skF_7'), inference(cnfTransformation, [status(thm)], [f_165])).
% 11.90/5.08  tff(c_14415, plain, (![A_297, B_298, C_299]: (k2_relset_1(A_297, B_298, C_299)=k2_relat_1(C_299) | ~m1_subset_1(C_299, k1_zfmisc_1(k2_zfmisc_1(A_297, B_298))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 11.90/5.08  tff(c_14424, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_94, c_14415])).
% 11.90/5.08  tff(c_14434, plain, (k2_relat_1('#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_90, c_14424])).
% 11.90/5.08  tff(c_46, plain, (![A_33]: (k1_relat_1(k2_funct_1(A_33))=k2_relat_1(A_33) | ~v2_funct_1(A_33) | ~v1_funct_1(A_33) | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_86])).
% 11.90/5.08  tff(c_163, plain, (![A_61]: (v1_funct_1(k2_funct_1(A_61)) | ~v1_funct_1(A_61) | ~v1_relat_1(A_61))), inference(cnfTransformation, [status(thm)], [f_76])).
% 11.90/5.08  tff(c_88, plain, (~m1_subset_1(k2_funct_1('#skF_8'), k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_6'))) | ~v1_funct_2(k2_funct_1('#skF_8'), '#skF_7', '#skF_6') | ~v1_funct_1(k2_funct_1('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_165])).
% 11.90/5.08  tff(c_160, plain, (~v1_funct_1(k2_funct_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_88])).
% 11.90/5.08  tff(c_166, plain, (~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_163, c_160])).
% 11.90/5.08  tff(c_169, plain, (~v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_166])).
% 11.90/5.08  tff(c_203, plain, (![C_66, A_67, B_68]: (v1_relat_1(C_66) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 11.90/5.08  tff(c_209, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_94, c_203])).
% 11.90/5.08  tff(c_218, plain, $false, inference(negUnitSimplification, [status(thm)], [c_169, c_209])).
% 11.90/5.08  tff(c_219, plain, (~v1_funct_2(k2_funct_1('#skF_8'), '#skF_7', '#skF_6') | ~m1_subset_1(k2_funct_1('#skF_8'), k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_6')))), inference(splitRight, [status(thm)], [c_88])).
% 11.90/5.08  tff(c_395, plain, (~m1_subset_1(k2_funct_1('#skF_8'), k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_6')))), inference(splitLeft, [status(thm)], [c_219])).
% 11.90/5.08  tff(c_490, plain, (![A_98, B_99, C_100]: (k2_relset_1(A_98, B_99, C_100)=k2_relat_1(C_100) | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(A_98, B_99))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 11.90/5.08  tff(c_499, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_94, c_490])).
% 11.90/5.08  tff(c_509, plain, (k2_relat_1('#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_90, c_499])).
% 11.90/5.08  tff(c_42, plain, (![A_32]: (v1_relat_1(k2_funct_1(A_32)) | ~v1_funct_1(A_32) | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_76])).
% 11.90/5.08  tff(c_220, plain, (v1_funct_1(k2_funct_1('#skF_8'))), inference(splitRight, [status(thm)], [c_88])).
% 11.90/5.08  tff(c_36, plain, (![A_31]: (k1_relat_1(A_31)=k1_xboole_0 | k2_relat_1(A_31)!=k1_xboole_0 | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_68])).
% 11.90/5.08  tff(c_276, plain, (k1_relat_1('#skF_8')=k1_xboole_0 | k2_relat_1('#skF_8')!=k1_xboole_0), inference(resolution, [status(thm)], [c_269, c_36])).
% 11.90/5.08  tff(c_293, plain, (k2_relat_1('#skF_8')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_276])).
% 11.90/5.08  tff(c_510, plain, (k1_xboole_0!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_509, c_293])).
% 11.90/5.08  tff(c_96, plain, (v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_165])).
% 11.90/5.08  tff(c_467, plain, (![A_95, B_96, C_97]: (k1_relset_1(A_95, B_96, C_97)=k1_relat_1(C_97) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 11.90/5.08  tff(c_485, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_94, c_467])).
% 11.90/5.08  tff(c_1765, plain, (![B_155, A_156, C_157]: (k1_xboole_0=B_155 | k1_relset_1(A_156, B_155, C_157)=A_156 | ~v1_funct_2(C_157, A_156, B_155) | ~m1_subset_1(C_157, k1_zfmisc_1(k2_zfmisc_1(A_156, B_155))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 11.90/5.08  tff(c_1780, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_8')='#skF_6' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_94, c_1765])).
% 11.90/5.08  tff(c_1797, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_96, c_485, c_1780])).
% 11.90/5.08  tff(c_1798, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_510, c_1797])).
% 11.90/5.08  tff(c_412, plain, (![A_91]: (k2_relat_1(k2_funct_1(A_91))=k1_relat_1(A_91) | ~v2_funct_1(A_91) | ~v1_funct_1(A_91) | ~v1_relat_1(A_91))), inference(cnfTransformation, [status(thm)], [f_86])).
% 11.90/5.08  tff(c_78, plain, (![A_48]: (v1_funct_2(A_48, k1_relat_1(A_48), k2_relat_1(A_48)) | ~v1_funct_1(A_48) | ~v1_relat_1(A_48))), inference(cnfTransformation, [status(thm)], [f_136])).
% 11.90/5.08  tff(c_11321, plain, (![A_279]: (v1_funct_2(k2_funct_1(A_279), k1_relat_1(k2_funct_1(A_279)), k1_relat_1(A_279)) | ~v1_funct_1(k2_funct_1(A_279)) | ~v1_relat_1(k2_funct_1(A_279)) | ~v2_funct_1(A_279) | ~v1_funct_1(A_279) | ~v1_relat_1(A_279))), inference(superposition, [status(thm), theory('equality')], [c_412, c_78])).
% 11.90/5.08  tff(c_11324, plain, (v1_funct_2(k2_funct_1('#skF_8'), k1_relat_1(k2_funct_1('#skF_8')), '#skF_6') | ~v1_funct_1(k2_funct_1('#skF_8')) | ~v1_relat_1(k2_funct_1('#skF_8')) | ~v2_funct_1('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_1798, c_11321])).
% 11.90/5.08  tff(c_11335, plain, (v1_funct_2(k2_funct_1('#skF_8'), k1_relat_1(k2_funct_1('#skF_8')), '#skF_6') | ~v1_relat_1(k2_funct_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_269, c_98, c_92, c_220, c_11324])).
% 11.90/5.08  tff(c_11338, plain, (~v1_relat_1(k2_funct_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_11335])).
% 11.90/5.08  tff(c_11341, plain, (~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_42, c_11338])).
% 11.90/5.08  tff(c_11345, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_269, c_98, c_11341])).
% 11.90/5.08  tff(c_11347, plain, (v1_relat_1(k2_funct_1('#skF_8'))), inference(splitRight, [status(thm)], [c_11335])).
% 11.90/5.08  tff(c_44, plain, (![A_33]: (k2_relat_1(k2_funct_1(A_33))=k1_relat_1(A_33) | ~v2_funct_1(A_33) | ~v1_funct_1(A_33) | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_86])).
% 11.90/5.08  tff(c_437, plain, (![A_94]: (m1_subset_1(A_94, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_94), k2_relat_1(A_94)))) | ~v1_funct_1(A_94) | ~v1_relat_1(A_94))), inference(cnfTransformation, [status(thm)], [f_136])).
% 11.90/5.08  tff(c_14278, plain, (![A_293]: (m1_subset_1(k2_funct_1(A_293), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_293)), k1_relat_1(A_293)))) | ~v1_funct_1(k2_funct_1(A_293)) | ~v1_relat_1(k2_funct_1(A_293)) | ~v2_funct_1(A_293) | ~v1_funct_1(A_293) | ~v1_relat_1(A_293))), inference(superposition, [status(thm), theory('equality')], [c_44, c_437])).
% 11.90/5.08  tff(c_14299, plain, (m1_subset_1(k2_funct_1('#skF_8'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_8')), '#skF_6'))) | ~v1_funct_1(k2_funct_1('#skF_8')) | ~v1_relat_1(k2_funct_1('#skF_8')) | ~v2_funct_1('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_1798, c_14278])).
% 11.90/5.08  tff(c_14316, plain, (m1_subset_1(k2_funct_1('#skF_8'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_8')), '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_269, c_98, c_92, c_11347, c_220, c_14299])).
% 11.90/5.08  tff(c_14339, plain, (m1_subset_1(k2_funct_1('#skF_8'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_8'), '#skF_6'))) | ~v2_funct_1('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_46, c_14316])).
% 11.90/5.08  tff(c_14353, plain, (m1_subset_1(k2_funct_1('#skF_8'), k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_269, c_98, c_92, c_509, c_14339])).
% 11.90/5.08  tff(c_14355, plain, $false, inference(negUnitSimplification, [status(thm)], [c_395, c_14353])).
% 11.90/5.08  tff(c_14356, plain, (~v1_funct_2(k2_funct_1('#skF_8'), '#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_219])).
% 11.90/5.08  tff(c_14435, plain, (k1_xboole_0!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_14434, c_293])).
% 11.90/5.08  tff(c_14555, plain, (![A_309, B_310, C_311]: (k1_relset_1(A_309, B_310, C_311)=k1_relat_1(C_311) | ~m1_subset_1(C_311, k1_zfmisc_1(k2_zfmisc_1(A_309, B_310))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 11.90/5.08  tff(c_14581, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_94, c_14555])).
% 11.90/5.08  tff(c_17504, plain, (![B_380, A_381, C_382]: (k1_xboole_0=B_380 | k1_relset_1(A_381, B_380, C_382)=A_381 | ~v1_funct_2(C_382, A_381, B_380) | ~m1_subset_1(C_382, k1_zfmisc_1(k2_zfmisc_1(A_381, B_380))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 11.90/5.08  tff(c_17522, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_8')='#skF_6' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_94, c_17504])).
% 11.90/5.08  tff(c_17541, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_96, c_14581, c_17522])).
% 11.90/5.08  tff(c_17542, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_14435, c_17541])).
% 11.90/5.08  tff(c_38, plain, (![A_31]: (k2_relat_1(A_31)=k1_xboole_0 | k1_relat_1(A_31)!=k1_xboole_0 | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_68])).
% 11.90/5.08  tff(c_277, plain, (k2_relat_1('#skF_8')=k1_xboole_0 | k1_relat_1('#skF_8')!=k1_xboole_0), inference(resolution, [status(thm)], [c_269, c_38])).
% 11.90/5.08  tff(c_340, plain, (k1_relat_1('#skF_8')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_293, c_277])).
% 11.90/5.08  tff(c_17550, plain, (k1_xboole_0!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_17542, c_340])).
% 11.90/5.08  tff(c_14357, plain, (m1_subset_1(k2_funct_1('#skF_8'), k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_6')))), inference(splitRight, [status(thm)], [c_219])).
% 11.90/5.08  tff(c_14579, plain, (k1_relset_1('#skF_7', '#skF_6', k2_funct_1('#skF_8'))=k1_relat_1(k2_funct_1('#skF_8'))), inference(resolution, [status(thm)], [c_14357, c_14555])).
% 11.90/5.08  tff(c_17644, plain, (![B_387, C_388, A_389]: (k1_xboole_0=B_387 | v1_funct_2(C_388, A_389, B_387) | k1_relset_1(A_389, B_387, C_388)!=A_389 | ~m1_subset_1(C_388, k1_zfmisc_1(k2_zfmisc_1(A_389, B_387))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 11.90/5.08  tff(c_17656, plain, (k1_xboole_0='#skF_6' | v1_funct_2(k2_funct_1('#skF_8'), '#skF_7', '#skF_6') | k1_relset_1('#skF_7', '#skF_6', k2_funct_1('#skF_8'))!='#skF_7'), inference(resolution, [status(thm)], [c_14357, c_17644])).
% 11.90/5.08  tff(c_17673, plain, (k1_xboole_0='#skF_6' | v1_funct_2(k2_funct_1('#skF_8'), '#skF_7', '#skF_6') | k1_relat_1(k2_funct_1('#skF_8'))!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_14579, c_17656])).
% 11.90/5.08  tff(c_17674, plain, (k1_relat_1(k2_funct_1('#skF_8'))!='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_14356, c_17550, c_17673])).
% 11.90/5.08  tff(c_17684, plain, (k2_relat_1('#skF_8')!='#skF_7' | ~v2_funct_1('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_46, c_17674])).
% 11.90/5.08  tff(c_17687, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_269, c_98, c_92, c_14434, c_17684])).
% 11.90/5.08  tff(c_17688, plain, (k1_relat_1('#skF_8')=k1_xboole_0), inference(splitRight, [status(thm)], [c_276])).
% 11.90/5.08  tff(c_17689, plain, (k2_relat_1('#skF_8')=k1_xboole_0), inference(splitRight, [status(thm)], [c_276])).
% 11.90/5.08  tff(c_31803, plain, (![A_783]: (m1_subset_1(A_783, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_783), k2_relat_1(A_783)))) | ~v1_funct_1(A_783) | ~v1_relat_1(A_783))), inference(cnfTransformation, [status(thm)], [f_136])).
% 11.90/5.08  tff(c_31830, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_8'), k1_xboole_0))) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_17689, c_31803])).
% 11.90/5.08  tff(c_31850, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_269, c_98, c_14, c_17688, c_31830])).
% 11.90/5.08  tff(c_18, plain, (![B_11, A_9]: (v1_xboole_0(B_11) | ~m1_subset_1(B_11, k1_zfmisc_1(A_9)) | ~v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_51])).
% 11.90/5.08  tff(c_31859, plain, (v1_xboole_0('#skF_8') | ~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_31850, c_18])).
% 11.90/5.08  tff(c_31865, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_31859])).
% 11.90/5.08  tff(c_8, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_36])).
% 11.90/5.08  tff(c_31871, plain, (k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_31865, c_8])).
% 11.90/5.08  tff(c_16, plain, (![B_8]: (k2_zfmisc_1(k1_xboole_0, B_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 11.90/5.08  tff(c_31893, plain, (![B_8]: (k2_zfmisc_1('#skF_8', B_8)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_31871, c_31871, c_16])).
% 11.90/5.08  tff(c_31885, plain, (k2_relat_1('#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_31871, c_17689])).
% 11.90/5.08  tff(c_31970, plain, (![A_788, B_789, C_790]: (k2_relset_1(A_788, B_789, C_790)=k2_relat_1(C_790) | ~m1_subset_1(C_790, k1_zfmisc_1(k2_zfmisc_1(A_788, B_789))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 11.90/5.08  tff(c_31982, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_94, c_31970])).
% 11.90/5.08  tff(c_31987, plain, ('#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_31885, c_90, c_31982])).
% 11.90/5.08  tff(c_17912, plain, (![A_413, B_414, C_415]: (k2_relset_1(A_413, B_414, C_415)=k2_relat_1(C_415) | ~m1_subset_1(C_415, k1_zfmisc_1(k2_zfmisc_1(A_413, B_414))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 11.90/5.08  tff(c_17918, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_94, c_17912])).
% 11.90/5.08  tff(c_17927, plain, (k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_17689, c_90, c_17918])).
% 11.90/5.08  tff(c_17954, plain, (v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_17927, c_6])).
% 11.90/5.08  tff(c_17947, plain, (![A_7]: (k2_zfmisc_1(A_7, '#skF_7')='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_17927, c_17927, c_14])).
% 11.90/5.08  tff(c_17701, plain, (![B_390, A_391]: (v1_xboole_0(B_390) | ~m1_subset_1(B_390, k1_zfmisc_1(A_391)) | ~v1_xboole_0(A_391))), inference(cnfTransformation, [status(thm)], [f_51])).
% 11.90/5.08  tff(c_17715, plain, (v1_xboole_0('#skF_8') | ~v1_xboole_0(k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_94, c_17701])).
% 11.90/5.08  tff(c_17747, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_6', '#skF_7'))), inference(splitLeft, [status(thm)], [c_17715])).
% 11.90/5.08  tff(c_18060, plain, (~v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_17947, c_17747])).
% 11.90/5.08  tff(c_18064, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_17954, c_18060])).
% 11.90/5.08  tff(c_18065, plain, (v1_xboole_0('#skF_8')), inference(splitRight, [status(thm)], [c_17715])).
% 11.90/5.08  tff(c_18073, plain, (k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_18065, c_8])).
% 11.90/5.08  tff(c_18085, plain, (![B_8]: (k2_zfmisc_1('#skF_8', B_8)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_18073, c_18073, c_16])).
% 11.90/5.08  tff(c_18084, plain, (![A_7]: (k2_zfmisc_1(A_7, '#skF_8')='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_18073, c_18073, c_14])).
% 11.90/5.08  tff(c_18066, plain, (v1_xboole_0(k2_zfmisc_1('#skF_6', '#skF_7'))), inference(splitRight, [status(thm)], [c_17715])).
% 11.90/5.08  tff(c_18148, plain, (![A_424]: (A_424='#skF_8' | ~v1_xboole_0(A_424))), inference(demodulation, [status(thm), theory('equality')], [c_18073, c_8])).
% 11.90/5.08  tff(c_18155, plain, (k2_zfmisc_1('#skF_6', '#skF_7')='#skF_8'), inference(resolution, [status(thm)], [c_18066, c_18148])).
% 11.90/5.08  tff(c_12, plain, (![B_8, A_7]: (k1_xboole_0=B_8 | k1_xboole_0=A_7 | k2_zfmisc_1(A_7, B_8)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 11.90/5.08  tff(c_18336, plain, (![B_439, A_440]: (B_439='#skF_8' | A_440='#skF_8' | k2_zfmisc_1(A_440, B_439)!='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_18073, c_18073, c_18073, c_12])).
% 11.90/5.08  tff(c_18346, plain, ('#skF_7'='#skF_8' | '#skF_6'='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_18155, c_18336])).
% 11.90/5.08  tff(c_18351, plain, ('#skF_6'='#skF_8'), inference(splitLeft, [status(thm)], [c_18346])).
% 11.90/5.08  tff(c_17698, plain, (~m1_subset_1(k2_funct_1('#skF_8'), k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_6')))), inference(splitLeft, [status(thm)], [c_219])).
% 11.90/5.08  tff(c_18367, plain, (~m1_subset_1(k2_funct_1('#skF_8'), k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_18351, c_17698])).
% 11.90/5.08  tff(c_18371, plain, (~m1_subset_1(k2_funct_1('#skF_8'), k1_zfmisc_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_18084, c_18367])).
% 11.90/5.08  tff(c_18077, plain, (k2_relat_1('#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_18073, c_17689])).
% 11.90/5.08  tff(c_18232, plain, (![A_430]: (k1_relat_1(k2_funct_1(A_430))=k2_relat_1(A_430) | ~v2_funct_1(A_430) | ~v1_funct_1(A_430) | ~v1_relat_1(A_430))), inference(cnfTransformation, [status(thm)], [f_86])).
% 11.90/5.08  tff(c_23970, plain, (![A_596]: (v1_funct_2(k2_funct_1(A_596), k2_relat_1(A_596), k2_relat_1(k2_funct_1(A_596))) | ~v1_funct_1(k2_funct_1(A_596)) | ~v1_relat_1(k2_funct_1(A_596)) | ~v2_funct_1(A_596) | ~v1_funct_1(A_596) | ~v1_relat_1(A_596))), inference(superposition, [status(thm), theory('equality')], [c_18232, c_78])).
% 11.90/5.08  tff(c_24021, plain, (v1_funct_2(k2_funct_1('#skF_8'), '#skF_8', k2_relat_1(k2_funct_1('#skF_8'))) | ~v1_funct_1(k2_funct_1('#skF_8')) | ~v1_relat_1(k2_funct_1('#skF_8')) | ~v2_funct_1('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_18077, c_23970])).
% 11.90/5.08  tff(c_24025, plain, (v1_funct_2(k2_funct_1('#skF_8'), '#skF_8', k2_relat_1(k2_funct_1('#skF_8'))) | ~v1_relat_1(k2_funct_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_269, c_98, c_92, c_220, c_24021])).
% 11.90/5.08  tff(c_24026, plain, (~v1_relat_1(k2_funct_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_24025])).
% 11.90/5.08  tff(c_24029, plain, (~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_42, c_24026])).
% 11.90/5.08  tff(c_24033, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_269, c_98, c_24029])).
% 11.90/5.08  tff(c_24035, plain, (v1_relat_1(k2_funct_1('#skF_8'))), inference(splitRight, [status(thm)], [c_24025])).
% 11.90/5.08  tff(c_18078, plain, (k1_relat_1('#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_18073, c_17688])).
% 11.90/5.08  tff(c_18080, plain, (![A_31]: (k1_relat_1(A_31)='#skF_8' | k2_relat_1(A_31)!='#skF_8' | ~v1_relat_1(A_31))), inference(demodulation, [status(thm), theory('equality')], [c_18073, c_18073, c_36])).
% 11.90/5.08  tff(c_24043, plain, (k1_relat_1(k2_funct_1('#skF_8'))='#skF_8' | k2_relat_1(k2_funct_1('#skF_8'))!='#skF_8'), inference(resolution, [status(thm)], [c_24035, c_18080])).
% 11.90/5.08  tff(c_24063, plain, (k2_relat_1(k2_funct_1('#skF_8'))!='#skF_8'), inference(splitLeft, [status(thm)], [c_24043])).
% 11.90/5.08  tff(c_24069, plain, (k1_relat_1('#skF_8')!='#skF_8' | ~v2_funct_1('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_44, c_24063])).
% 11.90/5.08  tff(c_24075, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_269, c_98, c_92, c_18078, c_24069])).
% 11.90/5.08  tff(c_24076, plain, (k1_relat_1(k2_funct_1('#skF_8'))='#skF_8'), inference(splitRight, [status(thm)], [c_24043])).
% 11.90/5.08  tff(c_76, plain, (![A_48]: (m1_subset_1(A_48, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_48), k2_relat_1(A_48)))) | ~v1_funct_1(A_48) | ~v1_relat_1(A_48))), inference(cnfTransformation, [status(thm)], [f_136])).
% 11.90/5.08  tff(c_24099, plain, (m1_subset_1(k2_funct_1('#skF_8'), k1_zfmisc_1(k2_zfmisc_1('#skF_8', k2_relat_1(k2_funct_1('#skF_8'))))) | ~v1_funct_1(k2_funct_1('#skF_8')) | ~v1_relat_1(k2_funct_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_24076, c_76])).
% 11.90/5.08  tff(c_24125, plain, (m1_subset_1(k2_funct_1('#skF_8'), k1_zfmisc_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_24035, c_220, c_18085, c_24099])).
% 11.90/5.08  tff(c_24127, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18371, c_24125])).
% 11.90/5.08  tff(c_24128, plain, ('#skF_7'='#skF_8'), inference(splitRight, [status(thm)], [c_18346])).
% 11.90/5.08  tff(c_24131, plain, (~m1_subset_1(k2_funct_1('#skF_8'), k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_24128, c_17698])).
% 11.90/5.08  tff(c_24135, plain, (~m1_subset_1(k2_funct_1('#skF_8'), k1_zfmisc_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_18085, c_24131])).
% 11.90/5.08  tff(c_31331, plain, (![A_762]: (v1_funct_2(k2_funct_1(A_762), k2_relat_1(A_762), k2_relat_1(k2_funct_1(A_762))) | ~v1_funct_1(k2_funct_1(A_762)) | ~v1_relat_1(k2_funct_1(A_762)) | ~v2_funct_1(A_762) | ~v1_funct_1(A_762) | ~v1_relat_1(A_762))), inference(superposition, [status(thm), theory('equality')], [c_18232, c_78])).
% 11.90/5.08  tff(c_31388, plain, (v1_funct_2(k2_funct_1('#skF_8'), '#skF_8', k2_relat_1(k2_funct_1('#skF_8'))) | ~v1_funct_1(k2_funct_1('#skF_8')) | ~v1_relat_1(k2_funct_1('#skF_8')) | ~v2_funct_1('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_18077, c_31331])).
% 11.90/5.08  tff(c_31394, plain, (v1_funct_2(k2_funct_1('#skF_8'), '#skF_8', k2_relat_1(k2_funct_1('#skF_8'))) | ~v1_relat_1(k2_funct_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_269, c_98, c_92, c_220, c_31388])).
% 11.90/5.08  tff(c_31395, plain, (~v1_relat_1(k2_funct_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_31394])).
% 11.90/5.08  tff(c_31398, plain, (~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_42, c_31395])).
% 11.90/5.08  tff(c_31402, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_269, c_98, c_31398])).
% 11.90/5.08  tff(c_31404, plain, (v1_relat_1(k2_funct_1('#skF_8'))), inference(splitRight, [status(thm)], [c_31394])).
% 11.90/5.08  tff(c_31412, plain, (k1_relat_1(k2_funct_1('#skF_8'))='#skF_8' | k2_relat_1(k2_funct_1('#skF_8'))!='#skF_8'), inference(resolution, [status(thm)], [c_31404, c_18080])).
% 11.90/5.08  tff(c_31432, plain, (k2_relat_1(k2_funct_1('#skF_8'))!='#skF_8'), inference(splitLeft, [status(thm)], [c_31412])).
% 11.90/5.08  tff(c_31438, plain, (k1_relat_1('#skF_8')!='#skF_8' | ~v2_funct_1('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_44, c_31432])).
% 11.90/5.08  tff(c_31444, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_269, c_98, c_92, c_18078, c_31438])).
% 11.90/5.08  tff(c_31445, plain, (k1_relat_1(k2_funct_1('#skF_8'))='#skF_8'), inference(splitRight, [status(thm)], [c_31412])).
% 11.90/5.08  tff(c_31468, plain, (m1_subset_1(k2_funct_1('#skF_8'), k1_zfmisc_1(k2_zfmisc_1('#skF_8', k2_relat_1(k2_funct_1('#skF_8'))))) | ~v1_funct_1(k2_funct_1('#skF_8')) | ~v1_relat_1(k2_funct_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_31445, c_76])).
% 11.90/5.08  tff(c_31494, plain, (m1_subset_1(k2_funct_1('#skF_8'), k1_zfmisc_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_31404, c_220, c_18085, c_31468])).
% 11.90/5.08  tff(c_31496, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24135, c_31494])).
% 11.90/5.08  tff(c_31498, plain, (m1_subset_1(k2_funct_1('#skF_8'), k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_6')))), inference(splitRight, [status(thm)], [c_219])).
% 11.90/5.08  tff(c_31513, plain, (![B_763, A_764]: (v1_xboole_0(B_763) | ~m1_subset_1(B_763, k1_zfmisc_1(A_764)) | ~v1_xboole_0(A_764))), inference(cnfTransformation, [status(thm)], [f_51])).
% 11.90/5.08  tff(c_31526, plain, (v1_xboole_0(k2_funct_1('#skF_8')) | ~v1_xboole_0(k2_zfmisc_1('#skF_7', '#skF_6'))), inference(resolution, [status(thm)], [c_31498, c_31513])).
% 11.90/5.08  tff(c_31564, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_7', '#skF_6'))), inference(splitLeft, [status(thm)], [c_31526])).
% 11.90/5.08  tff(c_31989, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_8', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_31987, c_31564])).
% 11.90/5.08  tff(c_32144, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_31865, c_31893, c_31989])).
% 11.90/5.08  tff(c_32146, plain, (v1_xboole_0(k2_zfmisc_1('#skF_7', '#skF_6'))), inference(splitRight, [status(thm)], [c_31526])).
% 11.90/5.08  tff(c_32154, plain, (k2_zfmisc_1('#skF_7', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_32146, c_8])).
% 11.90/5.08  tff(c_32187, plain, (k1_xboole_0='#skF_6' | k1_xboole_0='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_32154, c_12])).
% 11.90/5.08  tff(c_32189, plain, (k1_xboole_0='#skF_7'), inference(splitLeft, [status(thm)], [c_32187])).
% 11.90/5.08  tff(c_32209, plain, (v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_32189, c_6])).
% 11.90/5.08  tff(c_32202, plain, (![A_7]: (k2_zfmisc_1(A_7, '#skF_7')='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_32189, c_32189, c_14])).
% 11.90/5.08  tff(c_31531, plain, (v1_xboole_0('#skF_8') | ~v1_xboole_0(k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_94, c_31513])).
% 11.90/5.08  tff(c_31532, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_6', '#skF_7'))), inference(splitLeft, [status(thm)], [c_31531])).
% 11.90/5.08  tff(c_32291, plain, (~v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_32202, c_31532])).
% 11.90/5.08  tff(c_32295, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32209, c_32291])).
% 11.90/5.08  tff(c_32296, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_32187])).
% 11.90/5.08  tff(c_32317, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_32296, c_6])).
% 11.90/5.08  tff(c_32311, plain, (![B_8]: (k2_zfmisc_1('#skF_6', B_8)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_32296, c_32296, c_16])).
% 11.90/5.08  tff(c_32401, plain, (~v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_32311, c_31532])).
% 11.90/5.08  tff(c_32405, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32317, c_32401])).
% 11.90/5.08  tff(c_32406, plain, (v1_xboole_0('#skF_8')), inference(splitRight, [status(thm)], [c_31531])).
% 11.90/5.08  tff(c_32411, plain, (k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_32406, c_8])).
% 11.90/5.08  tff(c_10, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 11.90/5.08  tff(c_32423, plain, (![A_6]: (r1_tarski('#skF_8', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_32411, c_10])).
% 11.90/5.08  tff(c_32412, plain, (k2_relat_1('#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_32411, c_17689])).
% 11.90/5.08  tff(c_32413, plain, (k1_relat_1('#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_32411, c_17688])).
% 11.90/5.08  tff(c_33873, plain, (![B_865, A_866]: (v1_funct_2(B_865, k1_relat_1(B_865), A_866) | ~r1_tarski(k2_relat_1(B_865), A_866) | ~v1_funct_1(B_865) | ~v1_relat_1(B_865))), inference(cnfTransformation, [status(thm)], [f_148])).
% 11.90/5.08  tff(c_33882, plain, (![A_866]: (v1_funct_2('#skF_8', '#skF_8', A_866) | ~r1_tarski(k2_relat_1('#skF_8'), A_866) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_32413, c_33873])).
% 11.90/5.08  tff(c_33885, plain, (![A_866]: (v1_funct_2('#skF_8', '#skF_8', A_866))), inference(demodulation, [status(thm), theory('equality')], [c_269, c_98, c_32423, c_32412, c_33882])).
% 11.90/5.08  tff(c_32421, plain, (![B_8]: (k2_zfmisc_1('#skF_8', B_8)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_32411, c_32411, c_16])).
% 11.90/5.08  tff(c_32420, plain, (![A_7]: (k2_zfmisc_1(A_7, '#skF_8')='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_32411, c_32411, c_14])).
% 11.90/5.08  tff(c_32407, plain, (v1_xboole_0(k2_zfmisc_1('#skF_6', '#skF_7'))), inference(splitRight, [status(thm)], [c_31531])).
% 11.90/5.08  tff(c_32475, plain, (![A_809]: (A_809='#skF_8' | ~v1_xboole_0(A_809))), inference(demodulation, [status(thm), theory('equality')], [c_32411, c_8])).
% 11.90/5.08  tff(c_32485, plain, (k2_zfmisc_1('#skF_6', '#skF_7')='#skF_8'), inference(resolution, [status(thm)], [c_32407, c_32475])).
% 11.90/5.08  tff(c_32626, plain, (![B_818, A_819]: (B_818='#skF_8' | A_819='#skF_8' | k2_zfmisc_1(A_819, B_818)!='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_32411, c_32411, c_32411, c_12])).
% 11.90/5.08  tff(c_32636, plain, ('#skF_7'='#skF_8' | '#skF_6'='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_32485, c_32626])).
% 11.90/5.08  tff(c_32641, plain, ('#skF_6'='#skF_8'), inference(splitLeft, [status(thm)], [c_32636])).
% 11.90/5.08  tff(c_32553, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_7', '#skF_6'))), inference(splitLeft, [status(thm)], [c_31526])).
% 11.90/5.08  tff(c_32642, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_7', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_32641, c_32553])).
% 11.90/5.08  tff(c_32650, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32406, c_32420, c_32642])).
% 11.90/5.08  tff(c_32651, plain, ('#skF_7'='#skF_8'), inference(splitRight, [status(thm)], [c_32636])).
% 11.90/5.08  tff(c_32653, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_8', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_32651, c_32553])).
% 11.90/5.08  tff(c_32661, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32406, c_32421, c_32653])).
% 11.90/5.08  tff(c_32663, plain, (v1_xboole_0(k2_zfmisc_1('#skF_7', '#skF_6'))), inference(splitRight, [status(thm)], [c_31526])).
% 11.90/5.08  tff(c_32419, plain, (![A_5]: (A_5='#skF_8' | ~v1_xboole_0(A_5))), inference(demodulation, [status(thm), theory('equality')], [c_32411, c_8])).
% 11.90/5.08  tff(c_32710, plain, (k2_zfmisc_1('#skF_7', '#skF_6')='#skF_8'), inference(resolution, [status(thm)], [c_32663, c_32419])).
% 11.90/5.08  tff(c_32774, plain, (![B_825, A_826]: (B_825='#skF_8' | A_826='#skF_8' | k2_zfmisc_1(A_826, B_825)!='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_32411, c_32411, c_32411, c_12])).
% 11.90/5.08  tff(c_32787, plain, ('#skF_6'='#skF_8' | '#skF_7'='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_32710, c_32774])).
% 11.90/5.08  tff(c_32793, plain, ('#skF_7'='#skF_8'), inference(splitLeft, [status(thm)], [c_32787])).
% 11.90/5.08  tff(c_32662, plain, (v1_xboole_0(k2_funct_1('#skF_8'))), inference(splitRight, [status(thm)], [c_31526])).
% 11.90/5.08  tff(c_32679, plain, (k2_funct_1('#skF_8')='#skF_8'), inference(resolution, [status(thm)], [c_32662, c_32419])).
% 11.90/5.08  tff(c_31497, plain, (~v1_funct_2(k2_funct_1('#skF_8'), '#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_219])).
% 11.90/5.08  tff(c_32683, plain, (~v1_funct_2('#skF_8', '#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_32679, c_31497])).
% 11.90/5.08  tff(c_32795, plain, (~v1_funct_2('#skF_8', '#skF_8', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_32793, c_32683])).
% 11.90/5.08  tff(c_33890, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_33885, c_32795])).
% 11.90/5.08  tff(c_33892, plain, ('#skF_7'!='#skF_8'), inference(splitRight, [status(thm)], [c_32787])).
% 11.90/5.08  tff(c_151, plain, (![A_59]: (m1_subset_1(k6_relat_1(A_59), k1_zfmisc_1(k2_zfmisc_1(A_59, A_59))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 11.90/5.08  tff(c_155, plain, (m1_subset_1(k6_relat_1(k1_xboole_0), k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_151])).
% 11.90/5.08  tff(c_31519, plain, (v1_xboole_0(k6_relat_1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_155, c_31513])).
% 11.90/5.08  tff(c_31529, plain, (v1_xboole_0(k6_relat_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_31519])).
% 11.90/5.08  tff(c_32438, plain, (v1_xboole_0(k6_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_32411, c_31529])).
% 11.90/5.08  tff(c_32486, plain, (k6_relat_1('#skF_8')='#skF_8'), inference(resolution, [status(thm)], [c_32438, c_32475])).
% 11.90/5.08  tff(c_32502, plain, (![A_810]: (k2_zfmisc_1(A_810, '#skF_8')='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_32411, c_32411, c_14])).
% 11.90/5.08  tff(c_62, plain, (![A_44]: (m1_subset_1(k6_relat_1(A_44), k1_zfmisc_1(k2_zfmisc_1(A_44, A_44))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 11.90/5.08  tff(c_32513, plain, (m1_subset_1(k6_relat_1('#skF_8'), k1_zfmisc_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_32502, c_62])).
% 11.90/5.08  tff(c_32521, plain, (m1_subset_1('#skF_8', k1_zfmisc_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_32486, c_32513])).
% 11.90/5.08  tff(c_64, plain, (![A_45]: (v1_funct_2(k1_xboole_0, A_45, k1_xboole_0) | k1_xboole_0=A_45 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_45, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 11.90/5.08  tff(c_101, plain, (![A_45]: (v1_funct_2(k1_xboole_0, A_45, k1_xboole_0) | k1_xboole_0=A_45 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_64])).
% 11.90/5.08  tff(c_32543, plain, (![A_45]: (v1_funct_2('#skF_8', A_45, '#skF_8') | A_45='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_32521, c_32411, c_32411, c_32411, c_32411, c_32411, c_101])).
% 11.90/5.08  tff(c_33891, plain, ('#skF_6'='#skF_8'), inference(splitRight, [status(thm)], [c_32787])).
% 11.90/5.08  tff(c_33894, plain, (~v1_funct_2('#skF_8', '#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_33891, c_32683])).
% 11.90/5.08  tff(c_33908, plain, ('#skF_7'='#skF_8'), inference(resolution, [status(thm)], [c_32543, c_33894])).
% 11.90/5.08  tff(c_33912, plain, $false, inference(negUnitSimplification, [status(thm)], [c_33892, c_33908])).
% 11.90/5.08  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.90/5.08  
% 11.90/5.08  Inference rules
% 11.90/5.08  ----------------------
% 11.90/5.08  #Ref     : 0
% 11.90/5.08  #Sup     : 9265
% 11.90/5.08  #Fact    : 0
% 11.90/5.08  #Define  : 0
% 11.90/5.08  #Split   : 34
% 11.90/5.08  #Chain   : 0
% 11.90/5.08  #Close   : 0
% 11.90/5.08  
% 11.90/5.08  Ordering : KBO
% 11.90/5.08  
% 11.90/5.08  Simplification rules
% 11.90/5.08  ----------------------
% 11.90/5.08  #Subsume      : 3767
% 11.90/5.08  #Demod        : 8439
% 11.90/5.08  #Tautology    : 2479
% 11.90/5.08  #SimpNegUnit  : 99
% 11.90/5.08  #BackRed      : 227
% 11.90/5.08  
% 11.90/5.08  #Partial instantiations: 0
% 11.90/5.08  #Strategies tried      : 1
% 11.90/5.08  
% 11.90/5.08  Timing (in seconds)
% 11.90/5.08  ----------------------
% 11.90/5.09  Preprocessing        : 0.36
% 11.90/5.09  Parsing              : 0.19
% 11.90/5.09  CNF conversion       : 0.03
% 11.90/5.09  Main loop            : 3.87
% 11.90/5.09  Inferencing          : 0.79
% 11.90/5.09  Reduction            : 1.13
% 11.90/5.09  Demodulation         : 0.84
% 11.90/5.09  BG Simplification    : 0.10
% 11.90/5.09  Subsumption          : 1.65
% 11.90/5.09  Abstraction          : 0.14
% 11.90/5.09  MUC search           : 0.00
% 11.90/5.09  Cooper               : 0.00
% 11.90/5.09  Total                : 4.30
% 11.90/5.09  Index Insertion      : 0.00
% 11.90/5.09  Index Deletion       : 0.00
% 11.90/5.09  Index Matching       : 0.00
% 11.90/5.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
