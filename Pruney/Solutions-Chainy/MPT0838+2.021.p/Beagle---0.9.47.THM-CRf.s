%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:12 EST 2020

% Result     : Theorem 3.14s
% Output     : CNFRefutation 3.26s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 208 expanded)
%              Number of leaves         :   33 (  82 expanded)
%              Depth                    :   10
%              Number of atoms          :  143 ( 426 expanded)
%              Number of equality atoms :   34 (  90 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k8_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_31,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_relat_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_114,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
               => ~ ( k1_relset_1(A,B,C) != k1_xboole_0
                    & ! [D] :
                        ( m1_subset_1(D,B)
                       => ~ r2_hidden(D,k2_relset_1(A,B,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_relset_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_xboole_0(B) )
     => ( v1_xboole_0(k8_relat_1(B,A))
        & v1_relat_1(k8_relat_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc18_relat_1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_55,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_77,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k8_relat_1(k2_relat_1(A),A) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_relat_1)).

tff(c_4,plain,(
    v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_62,plain,(
    ! [A_42] :
      ( v1_xboole_0(k1_relat_1(A_42))
      | ~ v1_xboole_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_45,plain,(
    ! [A_39] :
      ( k1_xboole_0 = A_39
      | ~ v1_xboole_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_49,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_4,c_45])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_50,plain,(
    ! [A_1] :
      ( A_1 = '#skF_1'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_2])).

tff(c_68,plain,(
    ! [A_43] :
      ( k1_relat_1(A_43) = '#skF_1'
      | ~ v1_xboole_0(A_43) ) ),
    inference(resolution,[status(thm)],[c_62,c_50])).

tff(c_76,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_4,c_68])).

tff(c_40,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_362,plain,(
    ! [C_66,A_67,B_68] :
      ( v1_relat_1(C_66)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_375,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_362])).

tff(c_278,plain,(
    ! [B_58,A_59] :
      ( v1_xboole_0(k8_relat_1(B_58,A_59))
      | ~ v1_xboole_0(B_58)
      | ~ v1_relat_1(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_945,plain,(
    ! [B_128,A_129] :
      ( k8_relat_1(B_128,A_129) = '#skF_1'
      | ~ v1_xboole_0(B_128)
      | ~ v1_relat_1(A_129) ) ),
    inference(resolution,[status(thm)],[c_278,c_50])).

tff(c_958,plain,(
    ! [A_130] :
      ( k8_relat_1('#skF_1',A_130) = '#skF_1'
      | ~ v1_relat_1(A_130) ) ),
    inference(resolution,[status(thm)],[c_4,c_945])).

tff(c_970,plain,(
    k8_relat_1('#skF_1','#skF_5') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_375,c_958])).

tff(c_550,plain,(
    ! [A_95,B_96,C_97] :
      ( k1_relset_1(A_95,B_96,C_97) = k1_relat_1(C_97)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_563,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_550])).

tff(c_38,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_67,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_38])).

tff(c_566,plain,(
    k1_relat_1('#skF_5') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_563,c_67])).

tff(c_665,plain,(
    ! [A_107,B_108,C_109] :
      ( k2_relset_1(A_107,B_108,C_109) = k2_relat_1(C_109)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_107,B_108))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_678,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_665])).

tff(c_16,plain,(
    ! [A_6] : m1_subset_1('#skF_2'(A_6),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_379,plain,(
    ! [B_73,A_74] :
      ( r2_hidden(B_73,A_74)
      | ~ m1_subset_1(B_73,A_74)
      | v1_xboole_0(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_36,plain,(
    ! [D_38] :
      ( ~ r2_hidden(D_38,k2_relset_1('#skF_3','#skF_4','#skF_5'))
      | ~ m1_subset_1(D_38,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_388,plain,(
    ! [B_73] :
      ( ~ m1_subset_1(B_73,'#skF_4')
      | ~ m1_subset_1(B_73,k2_relset_1('#skF_3','#skF_4','#skF_5'))
      | v1_xboole_0(k2_relset_1('#skF_3','#skF_4','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_379,c_36])).

tff(c_503,plain,(
    ! [B_90] :
      ( ~ m1_subset_1(B_90,'#skF_4')
      | ~ m1_subset_1(B_90,k2_relset_1('#skF_3','#skF_4','#skF_5')) ) ),
    inference(splitLeft,[status(thm)],[c_388])).

tff(c_513,plain,(
    ~ m1_subset_1('#skF_2'(k2_relset_1('#skF_3','#skF_4','#skF_5')),'#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_503])).

tff(c_680,plain,(
    ~ m1_subset_1('#skF_2'(k2_relat_1('#skF_5')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_678,c_513])).

tff(c_12,plain,(
    ! [B_5,A_4] :
      ( m1_subset_1(B_5,A_4)
      | ~ v1_xboole_0(B_5)
      | ~ v1_xboole_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_407,plain,(
    ! [B_73] :
      ( ~ m1_subset_1(B_73,'#skF_4')
      | ~ m1_subset_1(B_73,k2_relset_1('#skF_3','#skF_4','#skF_5')) ) ),
    inference(splitLeft,[status(thm)],[c_388])).

tff(c_698,plain,(
    ! [B_111] :
      ( ~ m1_subset_1(B_111,'#skF_4')
      | ~ m1_subset_1(B_111,k2_relat_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_678,c_407])).

tff(c_707,plain,(
    ! [B_5] :
      ( ~ m1_subset_1(B_5,'#skF_4')
      | ~ v1_xboole_0(B_5)
      | ~ v1_xboole_0(k2_relat_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_12,c_698])).

tff(c_709,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_707])).

tff(c_10,plain,(
    ! [B_5,A_4] :
      ( r2_hidden(B_5,A_4)
      | ~ m1_subset_1(B_5,A_4)
      | v1_xboole_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_724,plain,(
    ! [A_114,B_115,C_116] :
      ( m1_subset_1(k2_relset_1(A_114,B_115,C_116),k1_zfmisc_1(B_115))
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1(A_114,B_115))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_744,plain,
    ( m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1('#skF_4'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_678,c_724])).

tff(c_751,plain,(
    m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_744])).

tff(c_18,plain,(
    ! [A_8,C_10,B_9] :
      ( m1_subset_1(A_8,C_10)
      | ~ m1_subset_1(B_9,k1_zfmisc_1(C_10))
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_761,plain,(
    ! [A_117] :
      ( m1_subset_1(A_117,'#skF_4')
      | ~ r2_hidden(A_117,k2_relat_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_751,c_18])).

tff(c_765,plain,(
    ! [B_5] :
      ( m1_subset_1(B_5,'#skF_4')
      | ~ m1_subset_1(B_5,k2_relat_1('#skF_5'))
      | v1_xboole_0(k2_relat_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_10,c_761])).

tff(c_770,plain,(
    ! [B_118] :
      ( m1_subset_1(B_118,'#skF_4')
      | ~ m1_subset_1(B_118,k2_relat_1('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_709,c_765])).

tff(c_778,plain,(
    m1_subset_1('#skF_2'(k2_relat_1('#skF_5')),'#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_770])).

tff(c_783,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_680,c_778])).

tff(c_785,plain,(
    v1_xboole_0(k2_relat_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_707])).

tff(c_26,plain,(
    ! [A_14] :
      ( k8_relat_1(k2_relat_1(A_14),A_14) = A_14
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_292,plain,(
    ! [A_14] :
      ( v1_xboole_0(A_14)
      | ~ v1_xboole_0(k2_relat_1(A_14))
      | ~ v1_relat_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_278])).

tff(c_790,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_785,c_292])).

tff(c_817,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_375,c_790])).

tff(c_66,plain,(
    ! [A_42] :
      ( k1_relat_1(A_42) = '#skF_1'
      | ~ v1_xboole_0(A_42) ) ),
    inference(resolution,[status(thm)],[c_62,c_50])).

tff(c_849,plain,(
    k1_relat_1('#skF_5') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_817,c_66])).

tff(c_865,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_566,c_849])).

tff(c_866,plain,(
    v1_xboole_0(k2_relset_1('#skF_3','#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_388])).

tff(c_890,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_866,c_50])).

tff(c_1039,plain,(
    ! [A_136,B_137,C_138] :
      ( k2_relset_1(A_136,B_137,C_138) = k2_relat_1(C_138)
      | ~ m1_subset_1(C_138,k1_zfmisc_1(k2_zfmisc_1(A_136,B_137))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1046,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_1039])).

tff(c_1053,plain,(
    k2_relat_1('#skF_5') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_890,c_1046])).

tff(c_1058,plain,
    ( k8_relat_1('#skF_1','#skF_5') = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1053,c_26])).

tff(c_1062,plain,(
    '#skF_5' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_375,c_970,c_1058])).

tff(c_971,plain,(
    ! [A_131,B_132,C_133] :
      ( k1_relset_1(A_131,B_132,C_133) = k1_relat_1(C_133)
      | ~ m1_subset_1(C_133,k1_zfmisc_1(k2_zfmisc_1(A_131,B_132))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_984,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_971])).

tff(c_1018,plain,(
    k1_relat_1('#skF_5') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_984,c_67])).

tff(c_1065,plain,(
    k1_relat_1('#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1062,c_1018])).

tff(c_1074,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_1065])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:14:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.14/1.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.14/1.48  
% 3.14/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.14/1.49  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k8_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_1 > #skF_4
% 3.14/1.49  
% 3.14/1.49  %Foreground sorts:
% 3.14/1.49  
% 3.14/1.49  
% 3.14/1.49  %Background operators:
% 3.14/1.49  
% 3.14/1.49  
% 3.14/1.49  %Foreground operators:
% 3.14/1.49  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.14/1.49  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 3.14/1.49  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.14/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.14/1.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.14/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.14/1.49  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.14/1.49  tff('#skF_5', type, '#skF_5': $i).
% 3.14/1.49  tff('#skF_3', type, '#skF_3': $i).
% 3.14/1.49  tff('#skF_1', type, '#skF_1': $i).
% 3.14/1.49  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.14/1.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.14/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.14/1.49  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.14/1.49  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.14/1.49  tff('#skF_4', type, '#skF_4': $i).
% 3.14/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.14/1.49  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.14/1.49  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.14/1.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.14/1.49  
% 3.26/1.50  tff(f_31, axiom, (?[A]: v1_xboole_0(A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_xboole_0)).
% 3.26/1.50  tff(f_65, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_relat_1)).
% 3.26/1.50  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.26/1.50  tff(f_114, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~(~(k1_relset_1(A, B, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k2_relset_1(A, B, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_relset_1)).
% 3.26/1.50  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.26/1.50  tff(f_73, axiom, (![A, B]: ((v1_relat_1(A) & v1_xboole_0(B)) => (v1_xboole_0(k8_relat_1(B, A)) & v1_relat_1(k8_relat_1(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc18_relat_1)).
% 3.26/1.50  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.26/1.50  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.26/1.50  tff(f_55, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 3.26/1.50  tff(f_52, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 3.26/1.50  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 3.26/1.50  tff(f_61, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 3.26/1.50  tff(f_77, axiom, (![A]: (v1_relat_1(A) => (k8_relat_1(k2_relat_1(A), A) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t126_relat_1)).
% 3.26/1.50  tff(c_4, plain, (v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.26/1.50  tff(c_62, plain, (![A_42]: (v1_xboole_0(k1_relat_1(A_42)) | ~v1_xboole_0(A_42))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.26/1.50  tff(c_45, plain, (![A_39]: (k1_xboole_0=A_39 | ~v1_xboole_0(A_39))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.26/1.50  tff(c_49, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_4, c_45])).
% 3.26/1.50  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.26/1.50  tff(c_50, plain, (![A_1]: (A_1='#skF_1' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_49, c_2])).
% 3.26/1.50  tff(c_68, plain, (![A_43]: (k1_relat_1(A_43)='#skF_1' | ~v1_xboole_0(A_43))), inference(resolution, [status(thm)], [c_62, c_50])).
% 3.26/1.50  tff(c_76, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_4, c_68])).
% 3.26/1.50  tff(c_40, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.26/1.50  tff(c_362, plain, (![C_66, A_67, B_68]: (v1_relat_1(C_66) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.26/1.50  tff(c_375, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_40, c_362])).
% 3.26/1.50  tff(c_278, plain, (![B_58, A_59]: (v1_xboole_0(k8_relat_1(B_58, A_59)) | ~v1_xboole_0(B_58) | ~v1_relat_1(A_59))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.26/1.50  tff(c_945, plain, (![B_128, A_129]: (k8_relat_1(B_128, A_129)='#skF_1' | ~v1_xboole_0(B_128) | ~v1_relat_1(A_129))), inference(resolution, [status(thm)], [c_278, c_50])).
% 3.26/1.50  tff(c_958, plain, (![A_130]: (k8_relat_1('#skF_1', A_130)='#skF_1' | ~v1_relat_1(A_130))), inference(resolution, [status(thm)], [c_4, c_945])).
% 3.26/1.50  tff(c_970, plain, (k8_relat_1('#skF_1', '#skF_5')='#skF_1'), inference(resolution, [status(thm)], [c_375, c_958])).
% 3.26/1.50  tff(c_550, plain, (![A_95, B_96, C_97]: (k1_relset_1(A_95, B_96, C_97)=k1_relat_1(C_97) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.26/1.50  tff(c_563, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_40, c_550])).
% 3.26/1.50  tff(c_38, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.26/1.50  tff(c_67, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_49, c_38])).
% 3.26/1.50  tff(c_566, plain, (k1_relat_1('#skF_5')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_563, c_67])).
% 3.26/1.50  tff(c_665, plain, (![A_107, B_108, C_109]: (k2_relset_1(A_107, B_108, C_109)=k2_relat_1(C_109) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_107, B_108))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.26/1.50  tff(c_678, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_40, c_665])).
% 3.26/1.50  tff(c_16, plain, (![A_6]: (m1_subset_1('#skF_2'(A_6), A_6))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.26/1.50  tff(c_379, plain, (![B_73, A_74]: (r2_hidden(B_73, A_74) | ~m1_subset_1(B_73, A_74) | v1_xboole_0(A_74))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.26/1.50  tff(c_36, plain, (![D_38]: (~r2_hidden(D_38, k2_relset_1('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1(D_38, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.26/1.50  tff(c_388, plain, (![B_73]: (~m1_subset_1(B_73, '#skF_4') | ~m1_subset_1(B_73, k2_relset_1('#skF_3', '#skF_4', '#skF_5')) | v1_xboole_0(k2_relset_1('#skF_3', '#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_379, c_36])).
% 3.26/1.50  tff(c_503, plain, (![B_90]: (~m1_subset_1(B_90, '#skF_4') | ~m1_subset_1(B_90, k2_relset_1('#skF_3', '#skF_4', '#skF_5')))), inference(splitLeft, [status(thm)], [c_388])).
% 3.26/1.50  tff(c_513, plain, (~m1_subset_1('#skF_2'(k2_relset_1('#skF_3', '#skF_4', '#skF_5')), '#skF_4')), inference(resolution, [status(thm)], [c_16, c_503])).
% 3.26/1.50  tff(c_680, plain, (~m1_subset_1('#skF_2'(k2_relat_1('#skF_5')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_678, c_513])).
% 3.26/1.50  tff(c_12, plain, (![B_5, A_4]: (m1_subset_1(B_5, A_4) | ~v1_xboole_0(B_5) | ~v1_xboole_0(A_4))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.26/1.50  tff(c_407, plain, (![B_73]: (~m1_subset_1(B_73, '#skF_4') | ~m1_subset_1(B_73, k2_relset_1('#skF_3', '#skF_4', '#skF_5')))), inference(splitLeft, [status(thm)], [c_388])).
% 3.26/1.50  tff(c_698, plain, (![B_111]: (~m1_subset_1(B_111, '#skF_4') | ~m1_subset_1(B_111, k2_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_678, c_407])).
% 3.26/1.50  tff(c_707, plain, (![B_5]: (~m1_subset_1(B_5, '#skF_4') | ~v1_xboole_0(B_5) | ~v1_xboole_0(k2_relat_1('#skF_5')))), inference(resolution, [status(thm)], [c_12, c_698])).
% 3.26/1.50  tff(c_709, plain, (~v1_xboole_0(k2_relat_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_707])).
% 3.26/1.50  tff(c_10, plain, (![B_5, A_4]: (r2_hidden(B_5, A_4) | ~m1_subset_1(B_5, A_4) | v1_xboole_0(A_4))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.26/1.50  tff(c_724, plain, (![A_114, B_115, C_116]: (m1_subset_1(k2_relset_1(A_114, B_115, C_116), k1_zfmisc_1(B_115)) | ~m1_subset_1(C_116, k1_zfmisc_1(k2_zfmisc_1(A_114, B_115))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.26/1.50  tff(c_744, plain, (m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1('#skF_4')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_678, c_724])).
% 3.26/1.50  tff(c_751, plain, (m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_744])).
% 3.26/1.50  tff(c_18, plain, (![A_8, C_10, B_9]: (m1_subset_1(A_8, C_10) | ~m1_subset_1(B_9, k1_zfmisc_1(C_10)) | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.26/1.50  tff(c_761, plain, (![A_117]: (m1_subset_1(A_117, '#skF_4') | ~r2_hidden(A_117, k2_relat_1('#skF_5')))), inference(resolution, [status(thm)], [c_751, c_18])).
% 3.26/1.50  tff(c_765, plain, (![B_5]: (m1_subset_1(B_5, '#skF_4') | ~m1_subset_1(B_5, k2_relat_1('#skF_5')) | v1_xboole_0(k2_relat_1('#skF_5')))), inference(resolution, [status(thm)], [c_10, c_761])).
% 3.26/1.50  tff(c_770, plain, (![B_118]: (m1_subset_1(B_118, '#skF_4') | ~m1_subset_1(B_118, k2_relat_1('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_709, c_765])).
% 3.26/1.50  tff(c_778, plain, (m1_subset_1('#skF_2'(k2_relat_1('#skF_5')), '#skF_4')), inference(resolution, [status(thm)], [c_16, c_770])).
% 3.26/1.50  tff(c_783, plain, $false, inference(negUnitSimplification, [status(thm)], [c_680, c_778])).
% 3.26/1.50  tff(c_785, plain, (v1_xboole_0(k2_relat_1('#skF_5'))), inference(splitRight, [status(thm)], [c_707])).
% 3.26/1.50  tff(c_26, plain, (![A_14]: (k8_relat_1(k2_relat_1(A_14), A_14)=A_14 | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.26/1.50  tff(c_292, plain, (![A_14]: (v1_xboole_0(A_14) | ~v1_xboole_0(k2_relat_1(A_14)) | ~v1_relat_1(A_14) | ~v1_relat_1(A_14))), inference(superposition, [status(thm), theory('equality')], [c_26, c_278])).
% 3.26/1.50  tff(c_790, plain, (v1_xboole_0('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_785, c_292])).
% 3.26/1.50  tff(c_817, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_375, c_790])).
% 3.26/1.50  tff(c_66, plain, (![A_42]: (k1_relat_1(A_42)='#skF_1' | ~v1_xboole_0(A_42))), inference(resolution, [status(thm)], [c_62, c_50])).
% 3.26/1.50  tff(c_849, plain, (k1_relat_1('#skF_5')='#skF_1'), inference(resolution, [status(thm)], [c_817, c_66])).
% 3.26/1.50  tff(c_865, plain, $false, inference(negUnitSimplification, [status(thm)], [c_566, c_849])).
% 3.26/1.50  tff(c_866, plain, (v1_xboole_0(k2_relset_1('#skF_3', '#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_388])).
% 3.26/1.50  tff(c_890, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_1'), inference(resolution, [status(thm)], [c_866, c_50])).
% 3.26/1.50  tff(c_1039, plain, (![A_136, B_137, C_138]: (k2_relset_1(A_136, B_137, C_138)=k2_relat_1(C_138) | ~m1_subset_1(C_138, k1_zfmisc_1(k2_zfmisc_1(A_136, B_137))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.26/1.50  tff(c_1046, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_40, c_1039])).
% 3.26/1.50  tff(c_1053, plain, (k2_relat_1('#skF_5')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_890, c_1046])).
% 3.26/1.50  tff(c_1058, plain, (k8_relat_1('#skF_1', '#skF_5')='#skF_5' | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1053, c_26])).
% 3.26/1.50  tff(c_1062, plain, ('#skF_5'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_375, c_970, c_1058])).
% 3.26/1.50  tff(c_971, plain, (![A_131, B_132, C_133]: (k1_relset_1(A_131, B_132, C_133)=k1_relat_1(C_133) | ~m1_subset_1(C_133, k1_zfmisc_1(k2_zfmisc_1(A_131, B_132))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.26/1.50  tff(c_984, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_40, c_971])).
% 3.26/1.50  tff(c_1018, plain, (k1_relat_1('#skF_5')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_984, c_67])).
% 3.26/1.50  tff(c_1065, plain, (k1_relat_1('#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1062, c_1018])).
% 3.26/1.50  tff(c_1074, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_1065])).
% 3.26/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.26/1.50  
% 3.26/1.50  Inference rules
% 3.26/1.50  ----------------------
% 3.26/1.50  #Ref     : 0
% 3.26/1.50  #Sup     : 248
% 3.26/1.50  #Fact    : 0
% 3.26/1.50  #Define  : 0
% 3.26/1.50  #Split   : 6
% 3.26/1.50  #Chain   : 0
% 3.26/1.50  #Close   : 0
% 3.26/1.50  
% 3.26/1.50  Ordering : KBO
% 3.26/1.50  
% 3.26/1.50  Simplification rules
% 3.26/1.50  ----------------------
% 3.26/1.50  #Subsume      : 26
% 3.26/1.50  #Demod        : 124
% 3.26/1.50  #Tautology    : 95
% 3.26/1.50  #SimpNegUnit  : 4
% 3.26/1.50  #BackRed      : 16
% 3.26/1.50  
% 3.26/1.50  #Partial instantiations: 0
% 3.26/1.50  #Strategies tried      : 1
% 3.26/1.50  
% 3.26/1.50  Timing (in seconds)
% 3.26/1.50  ----------------------
% 3.26/1.51  Preprocessing        : 0.32
% 3.26/1.51  Parsing              : 0.18
% 3.26/1.51  CNF conversion       : 0.02
% 3.26/1.51  Main loop            : 0.40
% 3.26/1.51  Inferencing          : 0.14
% 3.26/1.51  Reduction            : 0.11
% 3.26/1.51  Demodulation         : 0.07
% 3.26/1.51  BG Simplification    : 0.02
% 3.26/1.51  Subsumption          : 0.09
% 3.26/1.51  Abstraction          : 0.02
% 3.26/1.51  MUC search           : 0.00
% 3.26/1.51  Cooper               : 0.00
% 3.26/1.51  Total                : 0.76
% 3.26/1.51  Index Insertion      : 0.00
% 3.26/1.51  Index Deletion       : 0.00
% 3.26/1.51  Index Matching       : 0.00
% 3.26/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
