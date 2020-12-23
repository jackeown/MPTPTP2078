%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:59 EST 2020

% Result     : Theorem 2.57s
% Output     : CNFRefutation 2.73s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 305 expanded)
%              Number of leaves         :   30 ( 109 expanded)
%              Depth                    :    9
%              Number of atoms          :  132 ( 726 expanded)
%              Number of equality atoms :   72 ( 455 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_40,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_93,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => k8_relset_1(A,B,C,k7_relset_1(A,B,C,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_funct_2)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_56,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_80,axiom,(
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

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_10,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_40,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_78,plain,(
    ! [B_29,A_30] :
      ( v1_relat_1(B_29)
      | ~ m1_subset_1(B_29,k1_zfmisc_1(A_30))
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_81,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_40,c_78])).

tff(c_84,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_81])).

tff(c_12,plain,(
    ! [A_8] :
      ( k10_relat_1(A_8,k2_relat_1(A_8)) = k1_relat_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_124,plain,(
    ! [A_43,B_44,C_45] :
      ( k2_relset_1(A_43,B_44,C_45) = k2_relat_1(C_45)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_134,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_124])).

tff(c_176,plain,(
    ! [A_68,B_69,C_70] :
      ( k7_relset_1(A_68,B_69,C_70,A_68) = k2_relset_1(A_68,B_69,C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_178,plain,(
    k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') = k2_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_176])).

tff(c_184,plain,(
    k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_178])).

tff(c_143,plain,(
    ! [A_54,B_55,C_56,D_57] :
      ( k8_relset_1(A_54,B_55,C_56,D_57) = k10_relat_1(C_56,D_57)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_150,plain,(
    ! [D_57] : k8_relset_1('#skF_1','#skF_2','#skF_3',D_57) = k10_relat_1('#skF_3',D_57) ),
    inference(resolution,[status(thm)],[c_40,c_143])).

tff(c_36,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_3',k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1')) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_151,plain,(
    k10_relat_1('#skF_3',k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_36])).

tff(c_185,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_151])).

tff(c_192,plain,
    ( k1_relat_1('#skF_3') != '#skF_1'
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_185])).

tff(c_194,plain,(
    k1_relat_1('#skF_3') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_192])).

tff(c_38,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_49,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_42,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_107,plain,(
    ! [A_36,B_37,C_38] :
      ( k1_relset_1(A_36,B_37,C_38) = k1_relat_1(C_38)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1(A_36,B_37))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_117,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_107])).

tff(c_213,plain,(
    ! [B_82,A_83,C_84] :
      ( k1_xboole_0 = B_82
      | k1_relset_1(A_83,B_82,C_84) = A_83
      | ~ v1_funct_2(C_84,A_83,B_82)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_83,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_216,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_213])).

tff(c_225,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_117,c_216])).

tff(c_227,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_194,c_49,c_225])).

tff(c_228,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_4,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_242,plain,(
    ! [A_87] : k2_zfmisc_1(A_87,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_228,c_4])).

tff(c_246,plain,(
    v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_242,c_10])).

tff(c_241,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_228,c_4])).

tff(c_229,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_234,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_229])).

tff(c_251,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_241,c_234,c_40])).

tff(c_283,plain,(
    ! [B_91,A_92] :
      ( v1_relat_1(B_91)
      | ~ m1_subset_1(B_91,k1_zfmisc_1(A_92))
      | ~ v1_relat_1(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_286,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_251,c_283])).

tff(c_289,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_246,c_286])).

tff(c_6,plain,(
    ! [B_2] : k2_zfmisc_1(k1_xboole_0,B_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_252,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_1',B_2) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_228,c_6])).

tff(c_339,plain,(
    ! [A_103,B_104,C_105] :
      ( k1_relset_1(A_103,B_104,C_105) = k1_relat_1(C_105)
      | ~ m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1(A_103,B_104))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_346,plain,(
    ! [B_106,C_107] :
      ( k1_relset_1('#skF_1',B_106,C_107) = k1_relat_1(C_107)
      | ~ m1_subset_1(C_107,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_252,c_339])).

tff(c_349,plain,(
    ! [B_106] : k1_relset_1('#skF_1',B_106,'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_251,c_346])).

tff(c_235,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_234,c_42])).

tff(c_32,plain,(
    ! [B_23,C_24] :
      ( k1_relset_1(k1_xboole_0,B_23,C_24) = k1_xboole_0
      | ~ v1_funct_2(C_24,k1_xboole_0,B_23)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_45,plain,(
    ! [B_23,C_24] :
      ( k1_relset_1(k1_xboole_0,B_23,C_24) = k1_xboole_0
      | ~ v1_funct_2(C_24,k1_xboole_0,B_23)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_32])).

tff(c_385,plain,(
    ! [B_114,C_115] :
      ( k1_relset_1('#skF_1',B_114,C_115) = '#skF_1'
      | ~ v1_funct_2(C_115,'#skF_1',B_114)
      | ~ m1_subset_1(C_115,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_228,c_228,c_228,c_45])).

tff(c_387,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_3') = '#skF_1'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_235,c_385])).

tff(c_390,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_251,c_349,c_387])).

tff(c_302,plain,(
    ! [A_94,B_95,C_96] :
      ( k2_relset_1(A_94,B_95,C_96) = k2_relat_1(C_96)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_94,B_95))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_309,plain,(
    ! [B_97,C_98] :
      ( k2_relset_1('#skF_1',B_97,C_98) = k2_relat_1(C_98)
      | ~ m1_subset_1(C_98,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_252,c_302])).

tff(c_312,plain,(
    ! [B_97] : k2_relset_1('#skF_1',B_97,'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_251,c_309])).

tff(c_482,plain,(
    ! [A_135,B_136,C_137] :
      ( k7_relset_1(A_135,B_136,C_137,A_135) = k2_relset_1(A_135,B_136,C_137)
      | ~ m1_subset_1(C_137,k1_zfmisc_1(k2_zfmisc_1(A_135,B_136))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_487,plain,(
    ! [B_138,C_139] :
      ( k7_relset_1('#skF_1',B_138,C_139,'#skF_1') = k2_relset_1('#skF_1',B_138,C_139)
      | ~ m1_subset_1(C_139,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_252,c_482])).

tff(c_489,plain,(
    ! [B_138] : k7_relset_1('#skF_1',B_138,'#skF_3','#skF_1') = k2_relset_1('#skF_1',B_138,'#skF_3') ),
    inference(resolution,[status(thm)],[c_251,c_487])).

tff(c_491,plain,(
    ! [B_138] : k7_relset_1('#skF_1',B_138,'#skF_3','#skF_1') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_312,c_489])).

tff(c_440,plain,(
    ! [A_121,B_122,C_123,D_124] :
      ( k8_relset_1(A_121,B_122,C_123,D_124) = k10_relat_1(C_123,D_124)
      | ~ m1_subset_1(C_123,k1_zfmisc_1(k2_zfmisc_1(A_121,B_122))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_445,plain,(
    ! [B_125,C_126,D_127] :
      ( k8_relset_1('#skF_1',B_125,C_126,D_127) = k10_relat_1(C_126,D_127)
      | ~ m1_subset_1(C_126,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_252,c_440])).

tff(c_448,plain,(
    ! [B_125,D_127] : k8_relset_1('#skF_1',B_125,'#skF_3',D_127) = k10_relat_1('#skF_3',D_127) ),
    inference(resolution,[status(thm)],[c_251,c_445])).

tff(c_301,plain,(
    k8_relset_1('#skF_1','#skF_1','#skF_3',k7_relset_1('#skF_1','#skF_1','#skF_3','#skF_1')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_234,c_234,c_36])).

tff(c_449,plain,(
    k10_relat_1('#skF_3',k7_relset_1('#skF_1','#skF_1','#skF_3','#skF_1')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_448,c_301])).

tff(c_497,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_491,c_449])).

tff(c_507,plain,
    ( k1_relat_1('#skF_3') != '#skF_1'
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_497])).

tff(c_510,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_289,c_390,c_507])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:18:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.57/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.57/1.36  
% 2.57/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.57/1.36  %$ v1_funct_2 > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.57/1.36  
% 2.57/1.36  %Foreground sorts:
% 2.57/1.36  
% 2.57/1.36  
% 2.57/1.36  %Background operators:
% 2.57/1.36  
% 2.57/1.36  
% 2.57/1.36  %Foreground operators:
% 2.57/1.36  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.57/1.36  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.57/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.57/1.36  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.57/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.57/1.36  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.57/1.36  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.57/1.36  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.57/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.57/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.57/1.36  tff('#skF_1', type, '#skF_1': $i).
% 2.57/1.36  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.57/1.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.57/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.57/1.36  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.57/1.36  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.57/1.36  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.57/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.57/1.36  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.57/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.57/1.36  
% 2.73/1.38  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.73/1.38  tff(f_93, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => (k8_relset_1(A, B, C, k7_relset_1(A, B, C, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_funct_2)).
% 2.73/1.38  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.73/1.38  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 2.73/1.38  tff(f_52, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.73/1.38  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 2.73/1.38  tff(f_56, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.73/1.38  tff(f_48, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.73/1.38  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.73/1.38  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.73/1.38  tff(c_10, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.73/1.38  tff(c_40, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.73/1.38  tff(c_78, plain, (![B_29, A_30]: (v1_relat_1(B_29) | ~m1_subset_1(B_29, k1_zfmisc_1(A_30)) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.73/1.38  tff(c_81, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_40, c_78])).
% 2.73/1.38  tff(c_84, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_81])).
% 2.73/1.38  tff(c_12, plain, (![A_8]: (k10_relat_1(A_8, k2_relat_1(A_8))=k1_relat_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.73/1.38  tff(c_124, plain, (![A_43, B_44, C_45]: (k2_relset_1(A_43, B_44, C_45)=k2_relat_1(C_45) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.73/1.38  tff(c_134, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_40, c_124])).
% 2.73/1.38  tff(c_176, plain, (![A_68, B_69, C_70]: (k7_relset_1(A_68, B_69, C_70, A_68)=k2_relset_1(A_68, B_69, C_70) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.73/1.38  tff(c_178, plain, (k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')=k2_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_40, c_176])).
% 2.73/1.38  tff(c_184, plain, (k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_134, c_178])).
% 2.73/1.38  tff(c_143, plain, (![A_54, B_55, C_56, D_57]: (k8_relset_1(A_54, B_55, C_56, D_57)=k10_relat_1(C_56, D_57) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.73/1.38  tff(c_150, plain, (![D_57]: (k8_relset_1('#skF_1', '#skF_2', '#skF_3', D_57)=k10_relat_1('#skF_3', D_57))), inference(resolution, [status(thm)], [c_40, c_143])).
% 2.73/1.38  tff(c_36, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.73/1.38  tff(c_151, plain, (k10_relat_1('#skF_3', k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_150, c_36])).
% 2.73/1.38  tff(c_185, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_184, c_151])).
% 2.73/1.38  tff(c_192, plain, (k1_relat_1('#skF_3')!='#skF_1' | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_12, c_185])).
% 2.73/1.38  tff(c_194, plain, (k1_relat_1('#skF_3')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_192])).
% 2.73/1.38  tff(c_38, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.73/1.38  tff(c_49, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_38])).
% 2.73/1.38  tff(c_42, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.73/1.38  tff(c_107, plain, (![A_36, B_37, C_38]: (k1_relset_1(A_36, B_37, C_38)=k1_relat_1(C_38) | ~m1_subset_1(C_38, k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.73/1.38  tff(c_117, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_40, c_107])).
% 2.73/1.38  tff(c_213, plain, (![B_82, A_83, C_84]: (k1_xboole_0=B_82 | k1_relset_1(A_83, B_82, C_84)=A_83 | ~v1_funct_2(C_84, A_83, B_82) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_83, B_82))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.73/1.38  tff(c_216, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_40, c_213])).
% 2.73/1.38  tff(c_225, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_117, c_216])).
% 2.73/1.38  tff(c_227, plain, $false, inference(negUnitSimplification, [status(thm)], [c_194, c_49, c_225])).
% 2.73/1.38  tff(c_228, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_38])).
% 2.73/1.38  tff(c_4, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.73/1.38  tff(c_242, plain, (![A_87]: (k2_zfmisc_1(A_87, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_228, c_228, c_4])).
% 2.73/1.38  tff(c_246, plain, (v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_242, c_10])).
% 2.73/1.38  tff(c_241, plain, (![A_1]: (k2_zfmisc_1(A_1, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_228, c_228, c_4])).
% 2.73/1.38  tff(c_229, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_38])).
% 2.73/1.38  tff(c_234, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_228, c_229])).
% 2.73/1.38  tff(c_251, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_241, c_234, c_40])).
% 2.73/1.38  tff(c_283, plain, (![B_91, A_92]: (v1_relat_1(B_91) | ~m1_subset_1(B_91, k1_zfmisc_1(A_92)) | ~v1_relat_1(A_92))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.73/1.38  tff(c_286, plain, (v1_relat_1('#skF_3') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_251, c_283])).
% 2.73/1.38  tff(c_289, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_246, c_286])).
% 2.73/1.38  tff(c_6, plain, (![B_2]: (k2_zfmisc_1(k1_xboole_0, B_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.73/1.38  tff(c_252, plain, (![B_2]: (k2_zfmisc_1('#skF_1', B_2)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_228, c_228, c_6])).
% 2.73/1.38  tff(c_339, plain, (![A_103, B_104, C_105]: (k1_relset_1(A_103, B_104, C_105)=k1_relat_1(C_105) | ~m1_subset_1(C_105, k1_zfmisc_1(k2_zfmisc_1(A_103, B_104))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.73/1.38  tff(c_346, plain, (![B_106, C_107]: (k1_relset_1('#skF_1', B_106, C_107)=k1_relat_1(C_107) | ~m1_subset_1(C_107, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_252, c_339])).
% 2.73/1.38  tff(c_349, plain, (![B_106]: (k1_relset_1('#skF_1', B_106, '#skF_3')=k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_251, c_346])).
% 2.73/1.38  tff(c_235, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_234, c_42])).
% 2.73/1.38  tff(c_32, plain, (![B_23, C_24]: (k1_relset_1(k1_xboole_0, B_23, C_24)=k1_xboole_0 | ~v1_funct_2(C_24, k1_xboole_0, B_23) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_23))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.73/1.38  tff(c_45, plain, (![B_23, C_24]: (k1_relset_1(k1_xboole_0, B_23, C_24)=k1_xboole_0 | ~v1_funct_2(C_24, k1_xboole_0, B_23) | ~m1_subset_1(C_24, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_32])).
% 2.73/1.38  tff(c_385, plain, (![B_114, C_115]: (k1_relset_1('#skF_1', B_114, C_115)='#skF_1' | ~v1_funct_2(C_115, '#skF_1', B_114) | ~m1_subset_1(C_115, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_228, c_228, c_228, c_228, c_45])).
% 2.73/1.38  tff(c_387, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')='#skF_1' | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_235, c_385])).
% 2.73/1.38  tff(c_390, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_251, c_349, c_387])).
% 2.73/1.38  tff(c_302, plain, (![A_94, B_95, C_96]: (k2_relset_1(A_94, B_95, C_96)=k2_relat_1(C_96) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.73/1.38  tff(c_309, plain, (![B_97, C_98]: (k2_relset_1('#skF_1', B_97, C_98)=k2_relat_1(C_98) | ~m1_subset_1(C_98, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_252, c_302])).
% 2.73/1.38  tff(c_312, plain, (![B_97]: (k2_relset_1('#skF_1', B_97, '#skF_3')=k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_251, c_309])).
% 2.73/1.38  tff(c_482, plain, (![A_135, B_136, C_137]: (k7_relset_1(A_135, B_136, C_137, A_135)=k2_relset_1(A_135, B_136, C_137) | ~m1_subset_1(C_137, k1_zfmisc_1(k2_zfmisc_1(A_135, B_136))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.73/1.38  tff(c_487, plain, (![B_138, C_139]: (k7_relset_1('#skF_1', B_138, C_139, '#skF_1')=k2_relset_1('#skF_1', B_138, C_139) | ~m1_subset_1(C_139, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_252, c_482])).
% 2.73/1.38  tff(c_489, plain, (![B_138]: (k7_relset_1('#skF_1', B_138, '#skF_3', '#skF_1')=k2_relset_1('#skF_1', B_138, '#skF_3'))), inference(resolution, [status(thm)], [c_251, c_487])).
% 2.73/1.38  tff(c_491, plain, (![B_138]: (k7_relset_1('#skF_1', B_138, '#skF_3', '#skF_1')=k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_312, c_489])).
% 2.73/1.38  tff(c_440, plain, (![A_121, B_122, C_123, D_124]: (k8_relset_1(A_121, B_122, C_123, D_124)=k10_relat_1(C_123, D_124) | ~m1_subset_1(C_123, k1_zfmisc_1(k2_zfmisc_1(A_121, B_122))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.73/1.38  tff(c_445, plain, (![B_125, C_126, D_127]: (k8_relset_1('#skF_1', B_125, C_126, D_127)=k10_relat_1(C_126, D_127) | ~m1_subset_1(C_126, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_252, c_440])).
% 2.73/1.38  tff(c_448, plain, (![B_125, D_127]: (k8_relset_1('#skF_1', B_125, '#skF_3', D_127)=k10_relat_1('#skF_3', D_127))), inference(resolution, [status(thm)], [c_251, c_445])).
% 2.73/1.38  tff(c_301, plain, (k8_relset_1('#skF_1', '#skF_1', '#skF_3', k7_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_1'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_234, c_234, c_36])).
% 2.73/1.38  tff(c_449, plain, (k10_relat_1('#skF_3', k7_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_1'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_448, c_301])).
% 2.73/1.38  tff(c_497, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_491, c_449])).
% 2.73/1.38  tff(c_507, plain, (k1_relat_1('#skF_3')!='#skF_1' | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_12, c_497])).
% 2.73/1.38  tff(c_510, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_289, c_390, c_507])).
% 2.73/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.73/1.38  
% 2.73/1.38  Inference rules
% 2.73/1.38  ----------------------
% 2.73/1.38  #Ref     : 0
% 2.73/1.38  #Sup     : 113
% 2.73/1.38  #Fact    : 0
% 2.73/1.38  #Define  : 0
% 2.73/1.38  #Split   : 3
% 2.73/1.38  #Chain   : 0
% 2.73/1.38  #Close   : 0
% 2.73/1.38  
% 2.73/1.38  Ordering : KBO
% 2.73/1.38  
% 2.73/1.38  Simplification rules
% 2.73/1.38  ----------------------
% 2.73/1.38  #Subsume      : 2
% 2.73/1.38  #Demod        : 63
% 2.73/1.38  #Tautology    : 69
% 2.73/1.38  #SimpNegUnit  : 2
% 2.73/1.38  #BackRed      : 7
% 2.73/1.38  
% 2.73/1.38  #Partial instantiations: 0
% 2.73/1.38  #Strategies tried      : 1
% 2.73/1.38  
% 2.73/1.38  Timing (in seconds)
% 2.73/1.38  ----------------------
% 2.73/1.38  Preprocessing        : 0.30
% 2.73/1.38  Parsing              : 0.16
% 2.73/1.38  CNF conversion       : 0.02
% 2.73/1.38  Main loop            : 0.26
% 2.73/1.38  Inferencing          : 0.10
% 2.73/1.38  Reduction            : 0.08
% 2.73/1.38  Demodulation         : 0.06
% 2.73/1.38  BG Simplification    : 0.02
% 2.73/1.38  Subsumption          : 0.04
% 2.73/1.38  Abstraction          : 0.01
% 2.73/1.38  MUC search           : 0.00
% 2.73/1.38  Cooper               : 0.00
% 2.73/1.38  Total                : 0.61
% 2.73/1.38  Index Insertion      : 0.00
% 2.73/1.38  Index Deletion       : 0.00
% 2.73/1.38  Index Matching       : 0.00
% 2.73/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
