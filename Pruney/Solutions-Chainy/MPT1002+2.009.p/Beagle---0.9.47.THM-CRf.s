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
% DateTime   : Thu Dec  3 10:13:58 EST 2020

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.54s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 424 expanded)
%              Number of leaves         :   30 ( 143 expanded)
%              Depth                    :   10
%              Number of atoms          :  143 (1123 expanded)
%              Number of equality atoms :   59 ( 545 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_92,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(C,A)
         => ( ( B = k1_xboole_0
              & A != k1_xboole_0 )
            | r1_tarski(C,k8_relset_1(A,B,D,k7_relset_1(A,B,D,C))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_funct_2)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_76,axiom,(
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

tff(f_40,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_54,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_58,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_36,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_34,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_57,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_40,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_38,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_96,plain,(
    ! [A_34,B_35,C_36] :
      ( k1_relset_1(A_34,B_35,C_36) = k1_relat_1(C_36)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_106,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_96])).

tff(c_176,plain,(
    ! [B_72,A_73,C_74] :
      ( k1_xboole_0 = B_72
      | k1_relset_1(A_73,B_72,C_74) = A_73
      | ~ v1_funct_2(C_74,A_73,B_72)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_73,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_179,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_176])).

tff(c_188,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_106,c_179])).

tff(c_189,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_188])).

tff(c_10,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_87,plain,(
    ! [B_30,A_31] :
      ( v1_relat_1(B_30)
      | ~ m1_subset_1(B_30,k1_zfmisc_1(A_31))
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_90,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_38,c_87])).

tff(c_93,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_90])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(A_8,k10_relat_1(B_9,k9_relat_1(B_9,A_8)))
      | ~ r1_tarski(A_8,k1_relat_1(B_9))
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_124,plain,(
    ! [A_51,B_52,C_53,D_54] :
      ( k7_relset_1(A_51,B_52,C_53,D_54) = k9_relat_1(C_53,D_54)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_131,plain,(
    ! [D_54] : k7_relset_1('#skF_1','#skF_2','#skF_4',D_54) = k9_relat_1('#skF_4',D_54) ),
    inference(resolution,[status(thm)],[c_38,c_124])).

tff(c_116,plain,(
    ! [A_47,B_48,C_49,D_50] :
      ( k8_relset_1(A_47,B_48,C_49,D_50) = k10_relat_1(C_49,D_50)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_123,plain,(
    ! [D_50] : k8_relset_1('#skF_1','#skF_2','#skF_4',D_50) = k10_relat_1('#skF_4',D_50) ),
    inference(resolution,[status(thm)],[c_38,c_116])).

tff(c_32,plain,(
    ~ r1_tarski('#skF_3',k8_relset_1('#skF_1','#skF_2','#skF_4',k7_relset_1('#skF_1','#skF_2','#skF_4','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_132,plain,(
    ~ r1_tarski('#skF_3',k10_relat_1('#skF_4',k7_relset_1('#skF_1','#skF_2','#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_32])).

tff(c_151,plain,(
    ~ r1_tarski('#skF_3',k10_relat_1('#skF_4',k9_relat_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_132])).

tff(c_154,plain,
    ( ~ r1_tarski('#skF_3',k1_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_151])).

tff(c_157,plain,(
    ~ r1_tarski('#skF_3',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_154])).

tff(c_191,plain,(
    ~ r1_tarski('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_157])).

tff(c_195,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_191])).

tff(c_196,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_48,plain,(
    ! [A_26] : k2_zfmisc_1(A_26,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_52,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_10])).

tff(c_210,plain,(
    v1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_52])).

tff(c_4,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_198,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_196,c_4])).

tff(c_197,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_203,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_197])).

tff(c_209,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_38])).

tff(c_211,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_209])).

tff(c_253,plain,(
    ! [B_79,A_80] :
      ( v1_relat_1(B_79)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(A_80))
      | ~ v1_relat_1(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_256,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_211,c_253])).

tff(c_259,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_256])).

tff(c_6,plain,(
    ! [B_2] : k2_zfmisc_1(k1_xboole_0,B_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_222,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_1',B_2) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_196,c_6])).

tff(c_271,plain,(
    ! [A_83,B_84,C_85] :
      ( k1_relset_1(A_83,B_84,C_85) = k1_relat_1(C_85)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_278,plain,(
    ! [B_86,C_87] :
      ( k1_relset_1('#skF_1',B_86,C_87) = k1_relat_1(C_87)
      | ~ m1_subset_1(C_87,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_222,c_271])).

tff(c_281,plain,(
    ! [B_86] : k1_relset_1('#skF_1',B_86,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_211,c_278])).

tff(c_24,plain,(
    ! [C_23,B_22] :
      ( v1_funct_2(C_23,k1_xboole_0,B_22)
      | k1_relset_1(k1_xboole_0,B_22,C_23) != k1_xboole_0
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_43,plain,(
    ! [C_23,B_22] :
      ( v1_funct_2(C_23,k1_xboole_0,B_22)
      | k1_relset_1(k1_xboole_0,B_22,C_23) != k1_xboole_0
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_24])).

tff(c_290,plain,(
    ! [C_89,B_90] :
      ( v1_funct_2(C_89,'#skF_1',B_90)
      | k1_relset_1('#skF_1',B_90,C_89) != '#skF_1'
      | ~ m1_subset_1(C_89,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_196,c_196,c_196,c_43])).

tff(c_292,plain,(
    ! [B_90] :
      ( v1_funct_2('#skF_4','#skF_1',B_90)
      | k1_relset_1('#skF_1',B_90,'#skF_4') != '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_211,c_290])).

tff(c_294,plain,(
    ! [B_90] :
      ( v1_funct_2('#skF_4','#skF_1',B_90)
      | k1_relat_1('#skF_4') != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_281,c_292])).

tff(c_295,plain,(
    k1_relat_1('#skF_4') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_294])).

tff(c_204,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_40])).

tff(c_28,plain,(
    ! [B_22,C_23] :
      ( k1_relset_1(k1_xboole_0,B_22,C_23) = k1_xboole_0
      | ~ v1_funct_2(C_23,k1_xboole_0,B_22)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_44,plain,(
    ! [B_22,C_23] :
      ( k1_relset_1(k1_xboole_0,B_22,C_23) = k1_xboole_0
      | ~ v1_funct_2(C_23,k1_xboole_0,B_22)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_28])).

tff(c_316,plain,(
    ! [B_94,C_95] :
      ( k1_relset_1('#skF_1',B_94,C_95) = '#skF_1'
      | ~ v1_funct_2(C_95,'#skF_1',B_94)
      | ~ m1_subset_1(C_95,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_196,c_196,c_196,c_44])).

tff(c_318,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_4') = '#skF_1'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_204,c_316])).

tff(c_321,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_281,c_318])).

tff(c_323,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_295,c_321])).

tff(c_325,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_294])).

tff(c_380,plain,(
    ! [A_109,B_110,C_111,D_112] :
      ( k7_relset_1(A_109,B_110,C_111,D_112) = k9_relat_1(C_111,D_112)
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k2_zfmisc_1(A_109,B_110))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_431,plain,(
    ! [B_126,C_127,D_128] :
      ( k7_relset_1('#skF_1',B_126,C_127,D_128) = k9_relat_1(C_127,D_128)
      | ~ m1_subset_1(C_127,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_222,c_380])).

tff(c_434,plain,(
    ! [B_126,D_128] : k7_relset_1('#skF_1',B_126,'#skF_4',D_128) = k9_relat_1('#skF_4',D_128) ),
    inference(resolution,[status(thm)],[c_211,c_431])).

tff(c_375,plain,(
    ! [A_105,B_106,C_107,D_108] :
      ( k8_relset_1(A_105,B_106,C_107,D_108) = k10_relat_1(C_107,D_108)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(A_105,B_106))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_385,plain,(
    ! [B_113,C_114,D_115] :
      ( k8_relset_1('#skF_1',B_113,C_114,D_115) = k10_relat_1(C_114,D_115)
      | ~ m1_subset_1(C_114,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_222,c_375])).

tff(c_388,plain,(
    ! [B_113,D_115] : k8_relset_1('#skF_1',B_113,'#skF_4',D_115) = k10_relat_1('#skF_4',D_115) ),
    inference(resolution,[status(thm)],[c_211,c_385])).

tff(c_262,plain,(
    ~ r1_tarski('#skF_3',k8_relset_1('#skF_1','#skF_1','#skF_4',k7_relset_1('#skF_1','#skF_1','#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_203,c_32])).

tff(c_389,plain,(
    ~ r1_tarski('#skF_3',k10_relat_1('#skF_4',k7_relset_1('#skF_1','#skF_1','#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_388,c_262])).

tff(c_435,plain,(
    ~ r1_tarski('#skF_3',k10_relat_1('#skF_4',k9_relat_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_434,c_389])).

tff(c_447,plain,
    ( ~ r1_tarski('#skF_3',k1_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_435])).

tff(c_451,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_259,c_36,c_325,c_447])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:34:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.18/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/1.33  
% 2.18/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.54/1.34  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.54/1.34  
% 2.54/1.34  %Foreground sorts:
% 2.54/1.34  
% 2.54/1.34  
% 2.54/1.34  %Background operators:
% 2.54/1.34  
% 2.54/1.34  
% 2.54/1.34  %Foreground operators:
% 2.54/1.34  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.54/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.54/1.34  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.54/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.54/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.54/1.34  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.54/1.34  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.54/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.54/1.34  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.54/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.54/1.34  tff('#skF_1', type, '#skF_1': $i).
% 2.54/1.34  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.54/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.54/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.54/1.34  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.54/1.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.54/1.34  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.54/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.54/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.54/1.34  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.54/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.54/1.34  
% 2.54/1.35  tff(f_92, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(C, A) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | r1_tarski(C, k8_relset_1(A, B, D, k7_relset_1(A, B, D, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_funct_2)).
% 2.54/1.35  tff(f_50, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.54/1.35  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.54/1.35  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.54/1.35  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.54/1.35  tff(f_46, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_funct_1)).
% 2.54/1.35  tff(f_54, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.54/1.35  tff(f_58, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.54/1.35  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.54/1.35  tff(c_36, plain, (r1_tarski('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.54/1.35  tff(c_34, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.54/1.35  tff(c_57, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_34])).
% 2.54/1.35  tff(c_40, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.54/1.35  tff(c_38, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.54/1.35  tff(c_96, plain, (![A_34, B_35, C_36]: (k1_relset_1(A_34, B_35, C_36)=k1_relat_1(C_36) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.54/1.35  tff(c_106, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_96])).
% 2.54/1.35  tff(c_176, plain, (![B_72, A_73, C_74]: (k1_xboole_0=B_72 | k1_relset_1(A_73, B_72, C_74)=A_73 | ~v1_funct_2(C_74, A_73, B_72) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_73, B_72))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.54/1.35  tff(c_179, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_38, c_176])).
% 2.54/1.35  tff(c_188, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_106, c_179])).
% 2.54/1.35  tff(c_189, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_57, c_188])).
% 2.54/1.35  tff(c_10, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.54/1.35  tff(c_87, plain, (![B_30, A_31]: (v1_relat_1(B_30) | ~m1_subset_1(B_30, k1_zfmisc_1(A_31)) | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.54/1.35  tff(c_90, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_38, c_87])).
% 2.54/1.35  tff(c_93, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_90])).
% 2.54/1.35  tff(c_12, plain, (![A_8, B_9]: (r1_tarski(A_8, k10_relat_1(B_9, k9_relat_1(B_9, A_8))) | ~r1_tarski(A_8, k1_relat_1(B_9)) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.54/1.35  tff(c_124, plain, (![A_51, B_52, C_53, D_54]: (k7_relset_1(A_51, B_52, C_53, D_54)=k9_relat_1(C_53, D_54) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.54/1.35  tff(c_131, plain, (![D_54]: (k7_relset_1('#skF_1', '#skF_2', '#skF_4', D_54)=k9_relat_1('#skF_4', D_54))), inference(resolution, [status(thm)], [c_38, c_124])).
% 2.54/1.35  tff(c_116, plain, (![A_47, B_48, C_49, D_50]: (k8_relset_1(A_47, B_48, C_49, D_50)=k10_relat_1(C_49, D_50) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.54/1.35  tff(c_123, plain, (![D_50]: (k8_relset_1('#skF_1', '#skF_2', '#skF_4', D_50)=k10_relat_1('#skF_4', D_50))), inference(resolution, [status(thm)], [c_38, c_116])).
% 2.54/1.35  tff(c_32, plain, (~r1_tarski('#skF_3', k8_relset_1('#skF_1', '#skF_2', '#skF_4', k7_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.54/1.35  tff(c_132, plain, (~r1_tarski('#skF_3', k10_relat_1('#skF_4', k7_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_123, c_32])).
% 2.54/1.35  tff(c_151, plain, (~r1_tarski('#skF_3', k10_relat_1('#skF_4', k9_relat_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_132])).
% 2.54/1.35  tff(c_154, plain, (~r1_tarski('#skF_3', k1_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_12, c_151])).
% 2.54/1.35  tff(c_157, plain, (~r1_tarski('#skF_3', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_154])).
% 2.54/1.35  tff(c_191, plain, (~r1_tarski('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_189, c_157])).
% 2.54/1.35  tff(c_195, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_191])).
% 2.54/1.35  tff(c_196, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_34])).
% 2.54/1.35  tff(c_48, plain, (![A_26]: (k2_zfmisc_1(A_26, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.54/1.35  tff(c_52, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_48, c_10])).
% 2.54/1.35  tff(c_210, plain, (v1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_196, c_52])).
% 2.54/1.35  tff(c_4, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.54/1.35  tff(c_198, plain, (![A_1]: (k2_zfmisc_1(A_1, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_196, c_196, c_4])).
% 2.54/1.35  tff(c_197, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_34])).
% 2.54/1.35  tff(c_203, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_196, c_197])).
% 2.54/1.35  tff(c_209, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_203, c_38])).
% 2.54/1.35  tff(c_211, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_198, c_209])).
% 2.54/1.35  tff(c_253, plain, (![B_79, A_80]: (v1_relat_1(B_79) | ~m1_subset_1(B_79, k1_zfmisc_1(A_80)) | ~v1_relat_1(A_80))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.54/1.35  tff(c_256, plain, (v1_relat_1('#skF_4') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_211, c_253])).
% 2.54/1.35  tff(c_259, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_210, c_256])).
% 2.54/1.35  tff(c_6, plain, (![B_2]: (k2_zfmisc_1(k1_xboole_0, B_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.54/1.35  tff(c_222, plain, (![B_2]: (k2_zfmisc_1('#skF_1', B_2)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_196, c_196, c_6])).
% 2.54/1.35  tff(c_271, plain, (![A_83, B_84, C_85]: (k1_relset_1(A_83, B_84, C_85)=k1_relat_1(C_85) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.54/1.35  tff(c_278, plain, (![B_86, C_87]: (k1_relset_1('#skF_1', B_86, C_87)=k1_relat_1(C_87) | ~m1_subset_1(C_87, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_222, c_271])).
% 2.54/1.35  tff(c_281, plain, (![B_86]: (k1_relset_1('#skF_1', B_86, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_211, c_278])).
% 2.54/1.35  tff(c_24, plain, (![C_23, B_22]: (v1_funct_2(C_23, k1_xboole_0, B_22) | k1_relset_1(k1_xboole_0, B_22, C_23)!=k1_xboole_0 | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_22))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.54/1.35  tff(c_43, plain, (![C_23, B_22]: (v1_funct_2(C_23, k1_xboole_0, B_22) | k1_relset_1(k1_xboole_0, B_22, C_23)!=k1_xboole_0 | ~m1_subset_1(C_23, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_24])).
% 2.54/1.35  tff(c_290, plain, (![C_89, B_90]: (v1_funct_2(C_89, '#skF_1', B_90) | k1_relset_1('#skF_1', B_90, C_89)!='#skF_1' | ~m1_subset_1(C_89, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_196, c_196, c_196, c_196, c_43])).
% 2.54/1.35  tff(c_292, plain, (![B_90]: (v1_funct_2('#skF_4', '#skF_1', B_90) | k1_relset_1('#skF_1', B_90, '#skF_4')!='#skF_1')), inference(resolution, [status(thm)], [c_211, c_290])).
% 2.54/1.35  tff(c_294, plain, (![B_90]: (v1_funct_2('#skF_4', '#skF_1', B_90) | k1_relat_1('#skF_4')!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_281, c_292])).
% 2.54/1.35  tff(c_295, plain, (k1_relat_1('#skF_4')!='#skF_1'), inference(splitLeft, [status(thm)], [c_294])).
% 2.54/1.35  tff(c_204, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_203, c_40])).
% 2.54/1.35  tff(c_28, plain, (![B_22, C_23]: (k1_relset_1(k1_xboole_0, B_22, C_23)=k1_xboole_0 | ~v1_funct_2(C_23, k1_xboole_0, B_22) | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_22))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.54/1.35  tff(c_44, plain, (![B_22, C_23]: (k1_relset_1(k1_xboole_0, B_22, C_23)=k1_xboole_0 | ~v1_funct_2(C_23, k1_xboole_0, B_22) | ~m1_subset_1(C_23, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_28])).
% 2.54/1.35  tff(c_316, plain, (![B_94, C_95]: (k1_relset_1('#skF_1', B_94, C_95)='#skF_1' | ~v1_funct_2(C_95, '#skF_1', B_94) | ~m1_subset_1(C_95, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_196, c_196, c_196, c_196, c_44])).
% 2.54/1.35  tff(c_318, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_4')='#skF_1' | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_204, c_316])).
% 2.54/1.35  tff(c_321, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_211, c_281, c_318])).
% 2.54/1.35  tff(c_323, plain, $false, inference(negUnitSimplification, [status(thm)], [c_295, c_321])).
% 2.54/1.35  tff(c_325, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_294])).
% 2.54/1.35  tff(c_380, plain, (![A_109, B_110, C_111, D_112]: (k7_relset_1(A_109, B_110, C_111, D_112)=k9_relat_1(C_111, D_112) | ~m1_subset_1(C_111, k1_zfmisc_1(k2_zfmisc_1(A_109, B_110))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.54/1.35  tff(c_431, plain, (![B_126, C_127, D_128]: (k7_relset_1('#skF_1', B_126, C_127, D_128)=k9_relat_1(C_127, D_128) | ~m1_subset_1(C_127, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_222, c_380])).
% 2.54/1.35  tff(c_434, plain, (![B_126, D_128]: (k7_relset_1('#skF_1', B_126, '#skF_4', D_128)=k9_relat_1('#skF_4', D_128))), inference(resolution, [status(thm)], [c_211, c_431])).
% 2.54/1.35  tff(c_375, plain, (![A_105, B_106, C_107, D_108]: (k8_relset_1(A_105, B_106, C_107, D_108)=k10_relat_1(C_107, D_108) | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1(A_105, B_106))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.54/1.35  tff(c_385, plain, (![B_113, C_114, D_115]: (k8_relset_1('#skF_1', B_113, C_114, D_115)=k10_relat_1(C_114, D_115) | ~m1_subset_1(C_114, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_222, c_375])).
% 2.54/1.35  tff(c_388, plain, (![B_113, D_115]: (k8_relset_1('#skF_1', B_113, '#skF_4', D_115)=k10_relat_1('#skF_4', D_115))), inference(resolution, [status(thm)], [c_211, c_385])).
% 2.54/1.35  tff(c_262, plain, (~r1_tarski('#skF_3', k8_relset_1('#skF_1', '#skF_1', '#skF_4', k7_relset_1('#skF_1', '#skF_1', '#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_203, c_203, c_32])).
% 2.54/1.35  tff(c_389, plain, (~r1_tarski('#skF_3', k10_relat_1('#skF_4', k7_relset_1('#skF_1', '#skF_1', '#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_388, c_262])).
% 2.54/1.35  tff(c_435, plain, (~r1_tarski('#skF_3', k10_relat_1('#skF_4', k9_relat_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_434, c_389])).
% 2.54/1.35  tff(c_447, plain, (~r1_tarski('#skF_3', k1_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_12, c_435])).
% 2.54/1.35  tff(c_451, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_259, c_36, c_325, c_447])).
% 2.54/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.54/1.35  
% 2.54/1.35  Inference rules
% 2.54/1.35  ----------------------
% 2.54/1.35  #Ref     : 0
% 2.54/1.35  #Sup     : 90
% 2.54/1.35  #Fact    : 0
% 2.54/1.35  #Define  : 0
% 2.54/1.35  #Split   : 4
% 2.54/1.35  #Chain   : 0
% 2.54/1.35  #Close   : 0
% 2.54/1.35  
% 2.54/1.35  Ordering : KBO
% 2.54/1.35  
% 2.54/1.35  Simplification rules
% 2.54/1.35  ----------------------
% 2.54/1.35  #Subsume      : 3
% 2.54/1.35  #Demod        : 70
% 2.54/1.35  #Tautology    : 59
% 2.54/1.35  #SimpNegUnit  : 3
% 2.54/1.35  #BackRed      : 9
% 2.54/1.35  
% 2.54/1.35  #Partial instantiations: 0
% 2.54/1.35  #Strategies tried      : 1
% 2.54/1.35  
% 2.54/1.35  Timing (in seconds)
% 2.54/1.35  ----------------------
% 2.54/1.36  Preprocessing        : 0.32
% 2.54/1.36  Parsing              : 0.17
% 2.54/1.36  CNF conversion       : 0.02
% 2.54/1.36  Main loop            : 0.25
% 2.54/1.36  Inferencing          : 0.09
% 2.54/1.36  Reduction            : 0.08
% 2.54/1.36  Demodulation         : 0.06
% 2.54/1.36  BG Simplification    : 0.02
% 2.54/1.36  Subsumption          : 0.04
% 2.54/1.36  Abstraction          : 0.01
% 2.54/1.36  MUC search           : 0.00
% 2.54/1.36  Cooper               : 0.00
% 2.54/1.36  Total                : 0.61
% 2.54/1.36  Index Insertion      : 0.00
% 2.54/1.36  Index Deletion       : 0.00
% 2.54/1.36  Index Matching       : 0.00
% 2.54/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
