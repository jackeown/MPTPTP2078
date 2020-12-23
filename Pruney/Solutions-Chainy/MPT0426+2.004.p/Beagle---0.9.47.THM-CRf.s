%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:54 EST 2020

% Result     : Theorem 2.98s
% Output     : CNFRefutation 2.98s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 318 expanded)
%              Number of leaves         :   29 ( 114 expanded)
%              Depth                    :    9
%              Number of atoms          :  158 ( 772 expanded)
%              Number of equality atoms :   64 ( 253 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > k8_setfam_1 > k6_setfam_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_7 > #skF_10 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k8_setfam_1,type,(
    k8_setfam_1: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k6_setfam_1,type,(
    k6_setfam_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_85,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ( r2_hidden(B,A)
         => ( r2_hidden(B,k8_setfam_1(A,C))
          <=> ! [D] :
                ( r2_hidden(D,C)
               => r2_hidden(B,D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_setfam_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k6_setfam_1(A,B) = k1_setfam_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( ( B != k1_xboole_0
         => k8_setfam_1(A,B) = k6_setfam_1(A,B) )
        & ( B = k1_xboole_0
         => k8_setfam_1(A,B) = A ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ( A != k1_xboole_0
       => ( B = k1_setfam_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ! [D] :
                  ( r2_hidden(D,A)
                 => r2_hidden(C,D) ) ) ) )
      & ( A = k1_xboole_0
       => ( B = k1_setfam_1(A)
        <=> B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_setfam_1)).

tff(f_37,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_52,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_54,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k1_zfmisc_1('#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_458,plain,(
    ! [A_99,B_100] :
      ( k6_setfam_1(A_99,B_100) = k1_setfam_1(B_100)
      | ~ m1_subset_1(B_100,k1_zfmisc_1(k1_zfmisc_1(A_99))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_462,plain,(
    k6_setfam_1('#skF_7','#skF_9') = k1_setfam_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_54,c_458])).

tff(c_536,plain,(
    ! [A_111,B_112] :
      ( k8_setfam_1(A_111,B_112) = k6_setfam_1(A_111,B_112)
      | k1_xboole_0 = B_112
      | ~ m1_subset_1(B_112,k1_zfmisc_1(k1_zfmisc_1(A_111))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_539,plain,
    ( k8_setfam_1('#skF_7','#skF_9') = k6_setfam_1('#skF_7','#skF_9')
    | k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_54,c_536])).

tff(c_541,plain,
    ( k8_setfam_1('#skF_7','#skF_9') = k1_setfam_1('#skF_9')
    | k1_xboole_0 = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_462,c_539])).

tff(c_542,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_541])).

tff(c_24,plain,(
    ! [A_10] :
      ( k8_setfam_1(A_10,k1_xboole_0) = A_10
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_10))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_673,plain,(
    ! [A_125] :
      ( k8_setfam_1(A_125,'#skF_9') = A_125
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k1_zfmisc_1(A_125))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_542,c_542,c_24])).

tff(c_677,plain,(
    k8_setfam_1('#skF_7','#skF_9') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_54,c_673])).

tff(c_56,plain,
    ( ~ r2_hidden('#skF_8','#skF_10')
    | ~ r2_hidden('#skF_8',k8_setfam_1('#skF_7','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_91,plain,(
    ~ r2_hidden('#skF_8',k8_setfam_1('#skF_7','#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_678,plain,(
    ~ r2_hidden('#skF_8','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_677,c_91])).

tff(c_681,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_678])).

tff(c_682,plain,(
    k8_setfam_1('#skF_7','#skF_9') = k1_setfam_1('#skF_9') ),
    inference(splitRight,[status(thm)],[c_541])).

tff(c_684,plain,(
    ~ r2_hidden('#skF_8',k1_setfam_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_682,c_91])).

tff(c_683,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(splitRight,[status(thm)],[c_541])).

tff(c_699,plain,(
    ! [A_129,C_130] :
      ( r2_hidden('#skF_3'(A_129,k1_setfam_1(A_129),C_130),A_129)
      | r2_hidden(C_130,k1_setfam_1(A_129))
      | k1_xboole_0 = A_129 ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_139,plain,(
    ! [A_55,B_56] :
      ( k6_setfam_1(A_55,B_56) = k1_setfam_1(B_56)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(k1_zfmisc_1(A_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_143,plain,(
    k6_setfam_1('#skF_7','#skF_9') = k1_setfam_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_54,c_139])).

tff(c_207,plain,(
    ! [A_69,B_70] :
      ( k8_setfam_1(A_69,B_70) = k6_setfam_1(A_69,B_70)
      | k1_xboole_0 = B_70
      | ~ m1_subset_1(B_70,k1_zfmisc_1(k1_zfmisc_1(A_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_210,plain,
    ( k8_setfam_1('#skF_7','#skF_9') = k6_setfam_1('#skF_7','#skF_9')
    | k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_54,c_207])).

tff(c_212,plain,
    ( k8_setfam_1('#skF_7','#skF_9') = k1_setfam_1('#skF_9')
    | k1_xboole_0 = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_210])).

tff(c_213,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_212])).

tff(c_364,plain,(
    ! [A_83] :
      ( k8_setfam_1(A_83,'#skF_9') = A_83
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k1_zfmisc_1(A_83))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_213,c_213,c_24])).

tff(c_368,plain,(
    k8_setfam_1('#skF_7','#skF_9') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_54,c_364])).

tff(c_369,plain,(
    ~ r2_hidden('#skF_8','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_368,c_91])).

tff(c_372,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_369])).

tff(c_373,plain,(
    k8_setfam_1('#skF_7','#skF_9') = k1_setfam_1('#skF_9') ),
    inference(splitRight,[status(thm)],[c_212])).

tff(c_375,plain,(
    ~ r2_hidden('#skF_8',k1_setfam_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_373,c_91])).

tff(c_374,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(splitRight,[status(thm)],[c_212])).

tff(c_380,plain,(
    ! [A_84,C_85] :
      ( r2_hidden('#skF_3'(A_84,k1_setfam_1(A_84),C_85),A_84)
      | r2_hidden(C_85,k1_setfam_1(A_84))
      | k1_xboole_0 = A_84 ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_62,plain,(
    ! [D_35] :
      ( ~ r2_hidden('#skF_8','#skF_10')
      | r2_hidden('#skF_8',D_35)
      | ~ r2_hidden(D_35,'#skF_9') ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_99,plain,(
    ~ r2_hidden('#skF_8','#skF_10') ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_64,plain,(
    ! [D_35] :
      ( r2_hidden('#skF_10','#skF_9')
      | r2_hidden('#skF_8',D_35)
      | ~ r2_hidden(D_35,'#skF_9') ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_115,plain,(
    r2_hidden('#skF_10','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_66,plain,(
    ! [D_35] :
      ( r2_hidden('#skF_8',k8_setfam_1('#skF_7','#skF_9'))
      | r2_hidden('#skF_8',D_35)
      | ~ r2_hidden(D_35,'#skF_9') ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_124,plain,(
    ! [D_50] :
      ( r2_hidden('#skF_8',D_50)
      | ~ r2_hidden(D_50,'#skF_9') ) ),
    inference(negUnitSimplification,[status(thm)],[c_91,c_66])).

tff(c_126,plain,(
    r2_hidden('#skF_8','#skF_10') ),
    inference(resolution,[status(thm)],[c_115,c_124])).

tff(c_130,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_126])).

tff(c_131,plain,(
    ! [D_35] :
      ( r2_hidden('#skF_8',D_35)
      | ~ r2_hidden(D_35,'#skF_9') ) ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_391,plain,(
    ! [C_85] :
      ( r2_hidden('#skF_8','#skF_3'('#skF_9',k1_setfam_1('#skF_9'),C_85))
      | r2_hidden(C_85,k1_setfam_1('#skF_9'))
      | k1_xboole_0 = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_380,c_131])).

tff(c_419,plain,(
    ! [C_86] :
      ( r2_hidden('#skF_8','#skF_3'('#skF_9',k1_setfam_1('#skF_9'),C_86))
      | r2_hidden(C_86,k1_setfam_1('#skF_9')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_374,c_391])).

tff(c_42,plain,(
    ! [C_24,A_12] :
      ( ~ r2_hidden(C_24,'#skF_3'(A_12,k1_setfam_1(A_12),C_24))
      | r2_hidden(C_24,k1_setfam_1(A_12))
      | k1_xboole_0 = A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_423,plain,
    ( k1_xboole_0 = '#skF_9'
    | r2_hidden('#skF_8',k1_setfam_1('#skF_9')) ),
    inference(resolution,[status(thm)],[c_419,c_42])).

tff(c_431,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_375,c_374,c_375,c_423])).

tff(c_432,plain,(
    ! [D_35] :
      ( r2_hidden('#skF_8',D_35)
      | ~ r2_hidden(D_35,'#skF_9') ) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_725,plain,(
    ! [C_130] :
      ( r2_hidden('#skF_8','#skF_3'('#skF_9',k1_setfam_1('#skF_9'),C_130))
      | r2_hidden(C_130,k1_setfam_1('#skF_9'))
      | k1_xboole_0 = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_699,c_432])).

tff(c_740,plain,(
    ! [C_130] :
      ( r2_hidden('#skF_8','#skF_3'('#skF_9',k1_setfam_1('#skF_9'),C_130))
      | r2_hidden(C_130,k1_setfam_1('#skF_9')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_683,c_725])).

tff(c_750,plain,(
    ! [C_132,A_133] :
      ( ~ r2_hidden(C_132,'#skF_3'(A_133,k1_setfam_1(A_133),C_132))
      | r2_hidden(C_132,k1_setfam_1(A_133))
      | k1_xboole_0 = A_133 ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_754,plain,
    ( k1_xboole_0 = '#skF_9'
    | r2_hidden('#skF_8',k1_setfam_1('#skF_9')) ),
    inference(resolution,[status(thm)],[c_740,c_750])).

tff(c_761,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_684,c_683,c_684,c_754])).

tff(c_762,plain,(
    ~ r2_hidden('#skF_8','#skF_10') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_763,plain,(
    r2_hidden('#skF_8',k8_setfam_1('#skF_7','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_58,plain,
    ( r2_hidden('#skF_10','#skF_9')
    | ~ r2_hidden('#skF_8',k8_setfam_1('#skF_7','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_772,plain,(
    r2_hidden('#skF_10','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_763,c_58])).

tff(c_835,plain,(
    ! [C_154,D_155,A_156] :
      ( r2_hidden(C_154,D_155)
      | ~ r2_hidden(D_155,A_156)
      | ~ r2_hidden(C_154,k1_setfam_1(A_156))
      | k1_xboole_0 = A_156 ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_848,plain,(
    ! [C_154] :
      ( r2_hidden(C_154,'#skF_10')
      | ~ r2_hidden(C_154,k1_setfam_1('#skF_9'))
      | k1_xboole_0 = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_772,c_835])).

tff(c_851,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_848])).

tff(c_20,plain,(
    ! [A_7] : k2_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_81,plain,(
    ! [A_37,B_38] : k4_xboole_0(A_37,k2_xboole_0(A_37,B_38)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_88,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_81])).

tff(c_781,plain,(
    ! [D_140,B_141,A_142] :
      ( ~ r2_hidden(D_140,B_141)
      | ~ r2_hidden(D_140,k4_xboole_0(A_142,B_141)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_788,plain,(
    ! [D_143,A_144] :
      ( ~ r2_hidden(D_143,A_144)
      | ~ r2_hidden(D_143,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_781])).

tff(c_795,plain,(
    ~ r2_hidden('#skF_10',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_772,c_788])).

tff(c_857,plain,(
    ~ r2_hidden('#skF_10','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_851,c_795])).

tff(c_866,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_772,c_857])).

tff(c_868,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(splitRight,[status(thm)],[c_848])).

tff(c_800,plain,(
    ! [A_146,B_147] :
      ( k6_setfam_1(A_146,B_147) = k1_setfam_1(B_147)
      | ~ m1_subset_1(B_147,k1_zfmisc_1(k1_zfmisc_1(A_146))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_804,plain,(
    k6_setfam_1('#skF_7','#skF_9') = k1_setfam_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_54,c_800])).

tff(c_895,plain,(
    ! [A_161,B_162] :
      ( k8_setfam_1(A_161,B_162) = k6_setfam_1(A_161,B_162)
      | k1_xboole_0 = B_162
      | ~ m1_subset_1(B_162,k1_zfmisc_1(k1_zfmisc_1(A_161))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_898,plain,
    ( k8_setfam_1('#skF_7','#skF_9') = k6_setfam_1('#skF_7','#skF_9')
    | k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_54,c_895])).

tff(c_900,plain,
    ( k8_setfam_1('#skF_7','#skF_9') = k1_setfam_1('#skF_9')
    | k1_xboole_0 = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_804,c_898])).

tff(c_901,plain,(
    k8_setfam_1('#skF_7','#skF_9') = k1_setfam_1('#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_868,c_900])).

tff(c_909,plain,(
    r2_hidden('#skF_8',k1_setfam_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_901,c_763])).

tff(c_867,plain,(
    ! [C_154] :
      ( r2_hidden(C_154,'#skF_10')
      | ~ r2_hidden(C_154,k1_setfam_1('#skF_9')) ) ),
    inference(splitRight,[status(thm)],[c_848])).

tff(c_916,plain,(
    r2_hidden('#skF_8','#skF_10') ),
    inference(resolution,[status(thm)],[c_909,c_867])).

tff(c_924,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_762,c_916])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:33:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.98/1.57  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.98/1.58  
% 2.98/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.98/1.59  %$ r2_hidden > m1_subset_1 > k8_setfam_1 > k6_setfam_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_7 > #skF_10 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_5 > #skF_4
% 2.98/1.59  
% 2.98/1.59  %Foreground sorts:
% 2.98/1.59  
% 2.98/1.59  
% 2.98/1.59  %Background operators:
% 2.98/1.59  
% 2.98/1.59  
% 2.98/1.59  %Foreground operators:
% 2.98/1.59  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 2.98/1.59  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.98/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.98/1.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.98/1.59  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.98/1.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.98/1.59  tff(k8_setfam_1, type, k8_setfam_1: ($i * $i) > $i).
% 2.98/1.59  tff('#skF_7', type, '#skF_7': $i).
% 2.98/1.59  tff('#skF_10', type, '#skF_10': $i).
% 2.98/1.59  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.98/1.59  tff('#skF_9', type, '#skF_9': $i).
% 2.98/1.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.98/1.59  tff('#skF_8', type, '#skF_8': $i).
% 2.98/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.98/1.59  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 2.98/1.59  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.98/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.98/1.59  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.98/1.59  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.98/1.59  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.98/1.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.98/1.59  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.98/1.59  
% 2.98/1.61  tff(f_85, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => (r2_hidden(B, A) => (r2_hidden(B, k8_setfam_1(A, C)) <=> (![D]: (r2_hidden(D, C) => r2_hidden(B, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_setfam_1)).
% 2.98/1.61  tff(f_73, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k6_setfam_1(A, B) = k1_setfam_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_setfam_1)).
% 2.98/1.61  tff(f_50, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ((~(B = k1_xboole_0) => (k8_setfam_1(A, B) = k6_setfam_1(A, B))) & ((B = k1_xboole_0) => (k8_setfam_1(A, B) = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_setfam_1)).
% 2.98/1.61  tff(f_69, axiom, (![A, B]: ((~(A = k1_xboole_0) => ((B = k1_setfam_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (![D]: (r2_hidden(D, A) => r2_hidden(C, D))))))) & ((A = k1_xboole_0) => ((B = k1_setfam_1(A)) <=> (B = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_setfam_1)).
% 2.98/1.61  tff(f_37, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 2.98/1.61  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 2.98/1.61  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.98/1.61  tff(c_52, plain, (r2_hidden('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.98/1.61  tff(c_54, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k1_zfmisc_1('#skF_7')))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.98/1.61  tff(c_458, plain, (![A_99, B_100]: (k6_setfam_1(A_99, B_100)=k1_setfam_1(B_100) | ~m1_subset_1(B_100, k1_zfmisc_1(k1_zfmisc_1(A_99))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.98/1.61  tff(c_462, plain, (k6_setfam_1('#skF_7', '#skF_9')=k1_setfam_1('#skF_9')), inference(resolution, [status(thm)], [c_54, c_458])).
% 2.98/1.61  tff(c_536, plain, (![A_111, B_112]: (k8_setfam_1(A_111, B_112)=k6_setfam_1(A_111, B_112) | k1_xboole_0=B_112 | ~m1_subset_1(B_112, k1_zfmisc_1(k1_zfmisc_1(A_111))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.98/1.61  tff(c_539, plain, (k8_setfam_1('#skF_7', '#skF_9')=k6_setfam_1('#skF_7', '#skF_9') | k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_54, c_536])).
% 2.98/1.61  tff(c_541, plain, (k8_setfam_1('#skF_7', '#skF_9')=k1_setfam_1('#skF_9') | k1_xboole_0='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_462, c_539])).
% 2.98/1.61  tff(c_542, plain, (k1_xboole_0='#skF_9'), inference(splitLeft, [status(thm)], [c_541])).
% 2.98/1.61  tff(c_24, plain, (![A_10]: (k8_setfam_1(A_10, k1_xboole_0)=A_10 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_10))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.98/1.61  tff(c_673, plain, (![A_125]: (k8_setfam_1(A_125, '#skF_9')=A_125 | ~m1_subset_1('#skF_9', k1_zfmisc_1(k1_zfmisc_1(A_125))))), inference(demodulation, [status(thm), theory('equality')], [c_542, c_542, c_24])).
% 2.98/1.61  tff(c_677, plain, (k8_setfam_1('#skF_7', '#skF_9')='#skF_7'), inference(resolution, [status(thm)], [c_54, c_673])).
% 2.98/1.61  tff(c_56, plain, (~r2_hidden('#skF_8', '#skF_10') | ~r2_hidden('#skF_8', k8_setfam_1('#skF_7', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.98/1.61  tff(c_91, plain, (~r2_hidden('#skF_8', k8_setfam_1('#skF_7', '#skF_9'))), inference(splitLeft, [status(thm)], [c_56])).
% 2.98/1.61  tff(c_678, plain, (~r2_hidden('#skF_8', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_677, c_91])).
% 2.98/1.61  tff(c_681, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_678])).
% 2.98/1.61  tff(c_682, plain, (k8_setfam_1('#skF_7', '#skF_9')=k1_setfam_1('#skF_9')), inference(splitRight, [status(thm)], [c_541])).
% 2.98/1.61  tff(c_684, plain, (~r2_hidden('#skF_8', k1_setfam_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_682, c_91])).
% 2.98/1.61  tff(c_683, plain, (k1_xboole_0!='#skF_9'), inference(splitRight, [status(thm)], [c_541])).
% 2.98/1.61  tff(c_699, plain, (![A_129, C_130]: (r2_hidden('#skF_3'(A_129, k1_setfam_1(A_129), C_130), A_129) | r2_hidden(C_130, k1_setfam_1(A_129)) | k1_xboole_0=A_129)), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.98/1.61  tff(c_139, plain, (![A_55, B_56]: (k6_setfam_1(A_55, B_56)=k1_setfam_1(B_56) | ~m1_subset_1(B_56, k1_zfmisc_1(k1_zfmisc_1(A_55))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.98/1.61  tff(c_143, plain, (k6_setfam_1('#skF_7', '#skF_9')=k1_setfam_1('#skF_9')), inference(resolution, [status(thm)], [c_54, c_139])).
% 2.98/1.61  tff(c_207, plain, (![A_69, B_70]: (k8_setfam_1(A_69, B_70)=k6_setfam_1(A_69, B_70) | k1_xboole_0=B_70 | ~m1_subset_1(B_70, k1_zfmisc_1(k1_zfmisc_1(A_69))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.98/1.61  tff(c_210, plain, (k8_setfam_1('#skF_7', '#skF_9')=k6_setfam_1('#skF_7', '#skF_9') | k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_54, c_207])).
% 2.98/1.61  tff(c_212, plain, (k8_setfam_1('#skF_7', '#skF_9')=k1_setfam_1('#skF_9') | k1_xboole_0='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_143, c_210])).
% 2.98/1.61  tff(c_213, plain, (k1_xboole_0='#skF_9'), inference(splitLeft, [status(thm)], [c_212])).
% 2.98/1.61  tff(c_364, plain, (![A_83]: (k8_setfam_1(A_83, '#skF_9')=A_83 | ~m1_subset_1('#skF_9', k1_zfmisc_1(k1_zfmisc_1(A_83))))), inference(demodulation, [status(thm), theory('equality')], [c_213, c_213, c_24])).
% 2.98/1.61  tff(c_368, plain, (k8_setfam_1('#skF_7', '#skF_9')='#skF_7'), inference(resolution, [status(thm)], [c_54, c_364])).
% 2.98/1.61  tff(c_369, plain, (~r2_hidden('#skF_8', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_368, c_91])).
% 2.98/1.61  tff(c_372, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_369])).
% 2.98/1.61  tff(c_373, plain, (k8_setfam_1('#skF_7', '#skF_9')=k1_setfam_1('#skF_9')), inference(splitRight, [status(thm)], [c_212])).
% 2.98/1.61  tff(c_375, plain, (~r2_hidden('#skF_8', k1_setfam_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_373, c_91])).
% 2.98/1.61  tff(c_374, plain, (k1_xboole_0!='#skF_9'), inference(splitRight, [status(thm)], [c_212])).
% 2.98/1.61  tff(c_380, plain, (![A_84, C_85]: (r2_hidden('#skF_3'(A_84, k1_setfam_1(A_84), C_85), A_84) | r2_hidden(C_85, k1_setfam_1(A_84)) | k1_xboole_0=A_84)), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.98/1.61  tff(c_62, plain, (![D_35]: (~r2_hidden('#skF_8', '#skF_10') | r2_hidden('#skF_8', D_35) | ~r2_hidden(D_35, '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.98/1.61  tff(c_99, plain, (~r2_hidden('#skF_8', '#skF_10')), inference(splitLeft, [status(thm)], [c_62])).
% 2.98/1.61  tff(c_64, plain, (![D_35]: (r2_hidden('#skF_10', '#skF_9') | r2_hidden('#skF_8', D_35) | ~r2_hidden(D_35, '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.98/1.61  tff(c_115, plain, (r2_hidden('#skF_10', '#skF_9')), inference(splitLeft, [status(thm)], [c_64])).
% 2.98/1.61  tff(c_66, plain, (![D_35]: (r2_hidden('#skF_8', k8_setfam_1('#skF_7', '#skF_9')) | r2_hidden('#skF_8', D_35) | ~r2_hidden(D_35, '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.98/1.61  tff(c_124, plain, (![D_50]: (r2_hidden('#skF_8', D_50) | ~r2_hidden(D_50, '#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_91, c_66])).
% 2.98/1.61  tff(c_126, plain, (r2_hidden('#skF_8', '#skF_10')), inference(resolution, [status(thm)], [c_115, c_124])).
% 2.98/1.61  tff(c_130, plain, $false, inference(negUnitSimplification, [status(thm)], [c_99, c_126])).
% 2.98/1.61  tff(c_131, plain, (![D_35]: (r2_hidden('#skF_8', D_35) | ~r2_hidden(D_35, '#skF_9'))), inference(splitRight, [status(thm)], [c_64])).
% 2.98/1.61  tff(c_391, plain, (![C_85]: (r2_hidden('#skF_8', '#skF_3'('#skF_9', k1_setfam_1('#skF_9'), C_85)) | r2_hidden(C_85, k1_setfam_1('#skF_9')) | k1_xboole_0='#skF_9')), inference(resolution, [status(thm)], [c_380, c_131])).
% 2.98/1.61  tff(c_419, plain, (![C_86]: (r2_hidden('#skF_8', '#skF_3'('#skF_9', k1_setfam_1('#skF_9'), C_86)) | r2_hidden(C_86, k1_setfam_1('#skF_9')))), inference(negUnitSimplification, [status(thm)], [c_374, c_391])).
% 2.98/1.61  tff(c_42, plain, (![C_24, A_12]: (~r2_hidden(C_24, '#skF_3'(A_12, k1_setfam_1(A_12), C_24)) | r2_hidden(C_24, k1_setfam_1(A_12)) | k1_xboole_0=A_12)), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.98/1.61  tff(c_423, plain, (k1_xboole_0='#skF_9' | r2_hidden('#skF_8', k1_setfam_1('#skF_9'))), inference(resolution, [status(thm)], [c_419, c_42])).
% 2.98/1.61  tff(c_431, plain, $false, inference(negUnitSimplification, [status(thm)], [c_375, c_374, c_375, c_423])).
% 2.98/1.61  tff(c_432, plain, (![D_35]: (r2_hidden('#skF_8', D_35) | ~r2_hidden(D_35, '#skF_9'))), inference(splitRight, [status(thm)], [c_62])).
% 2.98/1.61  tff(c_725, plain, (![C_130]: (r2_hidden('#skF_8', '#skF_3'('#skF_9', k1_setfam_1('#skF_9'), C_130)) | r2_hidden(C_130, k1_setfam_1('#skF_9')) | k1_xboole_0='#skF_9')), inference(resolution, [status(thm)], [c_699, c_432])).
% 2.98/1.61  tff(c_740, plain, (![C_130]: (r2_hidden('#skF_8', '#skF_3'('#skF_9', k1_setfam_1('#skF_9'), C_130)) | r2_hidden(C_130, k1_setfam_1('#skF_9')))), inference(negUnitSimplification, [status(thm)], [c_683, c_725])).
% 2.98/1.61  tff(c_750, plain, (![C_132, A_133]: (~r2_hidden(C_132, '#skF_3'(A_133, k1_setfam_1(A_133), C_132)) | r2_hidden(C_132, k1_setfam_1(A_133)) | k1_xboole_0=A_133)), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.98/1.61  tff(c_754, plain, (k1_xboole_0='#skF_9' | r2_hidden('#skF_8', k1_setfam_1('#skF_9'))), inference(resolution, [status(thm)], [c_740, c_750])).
% 2.98/1.61  tff(c_761, plain, $false, inference(negUnitSimplification, [status(thm)], [c_684, c_683, c_684, c_754])).
% 2.98/1.61  tff(c_762, plain, (~r2_hidden('#skF_8', '#skF_10')), inference(splitRight, [status(thm)], [c_56])).
% 2.98/1.61  tff(c_763, plain, (r2_hidden('#skF_8', k8_setfam_1('#skF_7', '#skF_9'))), inference(splitRight, [status(thm)], [c_56])).
% 2.98/1.61  tff(c_58, plain, (r2_hidden('#skF_10', '#skF_9') | ~r2_hidden('#skF_8', k8_setfam_1('#skF_7', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.98/1.61  tff(c_772, plain, (r2_hidden('#skF_10', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_763, c_58])).
% 2.98/1.61  tff(c_835, plain, (![C_154, D_155, A_156]: (r2_hidden(C_154, D_155) | ~r2_hidden(D_155, A_156) | ~r2_hidden(C_154, k1_setfam_1(A_156)) | k1_xboole_0=A_156)), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.98/1.61  tff(c_848, plain, (![C_154]: (r2_hidden(C_154, '#skF_10') | ~r2_hidden(C_154, k1_setfam_1('#skF_9')) | k1_xboole_0='#skF_9')), inference(resolution, [status(thm)], [c_772, c_835])).
% 2.98/1.61  tff(c_851, plain, (k1_xboole_0='#skF_9'), inference(splitLeft, [status(thm)], [c_848])).
% 2.98/1.61  tff(c_20, plain, (![A_7]: (k2_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.98/1.61  tff(c_81, plain, (![A_37, B_38]: (k4_xboole_0(A_37, k2_xboole_0(A_37, B_38))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.98/1.61  tff(c_88, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_20, c_81])).
% 2.98/1.61  tff(c_781, plain, (![D_140, B_141, A_142]: (~r2_hidden(D_140, B_141) | ~r2_hidden(D_140, k4_xboole_0(A_142, B_141)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.98/1.61  tff(c_788, plain, (![D_143, A_144]: (~r2_hidden(D_143, A_144) | ~r2_hidden(D_143, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_88, c_781])).
% 2.98/1.61  tff(c_795, plain, (~r2_hidden('#skF_10', k1_xboole_0)), inference(resolution, [status(thm)], [c_772, c_788])).
% 2.98/1.61  tff(c_857, plain, (~r2_hidden('#skF_10', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_851, c_795])).
% 2.98/1.61  tff(c_866, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_772, c_857])).
% 2.98/1.61  tff(c_868, plain, (k1_xboole_0!='#skF_9'), inference(splitRight, [status(thm)], [c_848])).
% 2.98/1.61  tff(c_800, plain, (![A_146, B_147]: (k6_setfam_1(A_146, B_147)=k1_setfam_1(B_147) | ~m1_subset_1(B_147, k1_zfmisc_1(k1_zfmisc_1(A_146))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.98/1.61  tff(c_804, plain, (k6_setfam_1('#skF_7', '#skF_9')=k1_setfam_1('#skF_9')), inference(resolution, [status(thm)], [c_54, c_800])).
% 2.98/1.61  tff(c_895, plain, (![A_161, B_162]: (k8_setfam_1(A_161, B_162)=k6_setfam_1(A_161, B_162) | k1_xboole_0=B_162 | ~m1_subset_1(B_162, k1_zfmisc_1(k1_zfmisc_1(A_161))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.98/1.61  tff(c_898, plain, (k8_setfam_1('#skF_7', '#skF_9')=k6_setfam_1('#skF_7', '#skF_9') | k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_54, c_895])).
% 2.98/1.61  tff(c_900, plain, (k8_setfam_1('#skF_7', '#skF_9')=k1_setfam_1('#skF_9') | k1_xboole_0='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_804, c_898])).
% 2.98/1.61  tff(c_901, plain, (k8_setfam_1('#skF_7', '#skF_9')=k1_setfam_1('#skF_9')), inference(negUnitSimplification, [status(thm)], [c_868, c_900])).
% 2.98/1.61  tff(c_909, plain, (r2_hidden('#skF_8', k1_setfam_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_901, c_763])).
% 2.98/1.61  tff(c_867, plain, (![C_154]: (r2_hidden(C_154, '#skF_10') | ~r2_hidden(C_154, k1_setfam_1('#skF_9')))), inference(splitRight, [status(thm)], [c_848])).
% 2.98/1.61  tff(c_916, plain, (r2_hidden('#skF_8', '#skF_10')), inference(resolution, [status(thm)], [c_909, c_867])).
% 2.98/1.61  tff(c_924, plain, $false, inference(negUnitSimplification, [status(thm)], [c_762, c_916])).
% 2.98/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.98/1.61  
% 2.98/1.61  Inference rules
% 2.98/1.61  ----------------------
% 2.98/1.61  #Ref     : 0
% 2.98/1.61  #Sup     : 182
% 2.98/1.61  #Fact    : 0
% 2.98/1.61  #Define  : 0
% 2.98/1.61  #Split   : 13
% 2.98/1.61  #Chain   : 0
% 2.98/1.61  #Close   : 0
% 2.98/1.61  
% 2.98/1.61  Ordering : KBO
% 2.98/1.61  
% 2.98/1.61  Simplification rules
% 2.98/1.61  ----------------------
% 2.98/1.61  #Subsume      : 34
% 2.98/1.61  #Demod        : 143
% 2.98/1.61  #Tautology    : 81
% 2.98/1.61  #SimpNegUnit  : 12
% 2.98/1.61  #BackRed      : 88
% 2.98/1.61  
% 2.98/1.61  #Partial instantiations: 0
% 2.98/1.61  #Strategies tried      : 1
% 2.98/1.61  
% 2.98/1.61  Timing (in seconds)
% 2.98/1.61  ----------------------
% 2.98/1.61  Preprocessing        : 0.35
% 2.98/1.61  Parsing              : 0.17
% 2.98/1.61  CNF conversion       : 0.03
% 2.98/1.61  Main loop            : 0.37
% 2.98/1.61  Inferencing          : 0.12
% 2.98/1.61  Reduction            : 0.11
% 2.98/1.61  Demodulation         : 0.07
% 2.98/1.61  BG Simplification    : 0.02
% 2.98/1.61  Subsumption          : 0.07
% 2.98/1.61  Abstraction          : 0.02
% 2.98/1.61  MUC search           : 0.00
% 2.98/1.61  Cooper               : 0.00
% 2.98/1.61  Total                : 0.76
% 2.98/1.61  Index Insertion      : 0.00
% 2.98/1.61  Index Deletion       : 0.00
% 2.98/1.61  Index Matching       : 0.00
% 2.98/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
