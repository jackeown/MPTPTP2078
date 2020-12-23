%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:55 EST 2020

% Result     : Theorem 3.11s
% Output     : CNFRefutation 3.14s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 230 expanded)
%              Number of leaves         :   27 (  85 expanded)
%              Depth                    :    7
%              Number of atoms          :  149 ( 523 expanded)
%              Number of equality atoms :   61 ( 170 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > k8_setfam_1 > k6_setfam_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k8_setfam_1,type,(
    k8_setfam_1: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k6_setfam_1,type,(
    k6_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_86,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ( r2_hidden(B,A)
         => ( r2_hidden(B,k8_setfam_1(A,C))
          <=> ! [D] :
                ( r2_hidden(D,C)
               => r2_hidden(B,D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_setfam_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k6_setfam_1(A,B) = k1_setfam_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( ( B != k1_xboole_0
         => k8_setfam_1(A,B) = k6_setfam_1(A,B) )
        & ( B = k1_xboole_0
         => k8_setfam_1(A,B) = A ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).

tff(f_34,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_64,axiom,(
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

tff(f_29,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(c_38,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_40,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k1_zfmisc_1('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_333,plain,(
    ! [A_76,B_77] :
      ( k6_setfam_1(A_76,B_77) = k1_setfam_1(B_77)
      | ~ m1_subset_1(B_77,k1_zfmisc_1(k1_zfmisc_1(A_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_341,plain,(
    k6_setfam_1('#skF_5','#skF_7') = k1_setfam_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_40,c_333])).

tff(c_380,plain,(
    ! [A_91,B_92] :
      ( k8_setfam_1(A_91,B_92) = k6_setfam_1(A_91,B_92)
      | k1_xboole_0 = B_92
      | ~ m1_subset_1(B_92,k1_zfmisc_1(k1_zfmisc_1(A_91))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_383,plain,
    ( k8_setfam_1('#skF_5','#skF_7') = k6_setfam_1('#skF_5','#skF_7')
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_40,c_380])).

tff(c_389,plain,
    ( k8_setfam_1('#skF_5','#skF_7') = k1_setfam_1('#skF_7')
    | k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_341,c_383])).

tff(c_393,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_389])).

tff(c_6,plain,(
    ! [A_5] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_8,plain,(
    ! [A_6] :
      ( k8_setfam_1(A_6,k1_xboole_0) = A_6
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_6))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_55,plain,(
    ! [A_6] : k8_setfam_1(A_6,k1_xboole_0) = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8])).

tff(c_401,plain,(
    ! [A_6] : k8_setfam_1(A_6,'#skF_7') = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_393,c_55])).

tff(c_44,plain,
    ( r2_hidden('#skF_8','#skF_7')
    | ~ r2_hidden('#skF_6',k8_setfam_1('#skF_5','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_71,plain,(
    ~ r2_hidden('#skF_6',k8_setfam_1('#skF_5','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_433,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_401,c_71])).

tff(c_436,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_433])).

tff(c_437,plain,(
    k8_setfam_1('#skF_5','#skF_7') = k1_setfam_1('#skF_7') ),
    inference(splitRight,[status(thm)],[c_389])).

tff(c_439,plain,(
    ~ r2_hidden('#skF_6',k1_setfam_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_437,c_71])).

tff(c_438,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_389])).

tff(c_444,plain,(
    ! [A_95,C_96] :
      ( r2_hidden('#skF_1'(A_95,k1_setfam_1(A_95),C_96),A_95)
      | r2_hidden(C_96,k1_setfam_1(A_95))
      | k1_xboole_0 = A_95 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_50,plain,(
    ! [D_34] :
      ( r2_hidden('#skF_8','#skF_7')
      | r2_hidden('#skF_6',D_34)
      | ~ r2_hidden(D_34,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_89,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_72,plain,(
    ! [A_39,B_40] :
      ( k2_xboole_0(k1_tarski(A_39),B_40) = B_40
      | ~ r2_hidden(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(k1_tarski(A_3),B_4) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_77,plain,(
    ! [B_40,A_39] :
      ( k1_xboole_0 != B_40
      | ~ r2_hidden(A_39,B_40) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_4])).

tff(c_93,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(resolution,[status(thm)],[c_89,c_77])).

tff(c_200,plain,(
    ! [A_65,C_66] :
      ( r2_hidden('#skF_1'(A_65,k1_setfam_1(A_65),C_66),A_65)
      | r2_hidden(C_66,k1_setfam_1(A_65))
      | k1_xboole_0 = A_65 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_48,plain,(
    ! [D_34] :
      ( ~ r2_hidden('#skF_6','#skF_8')
      | r2_hidden('#skF_6',D_34)
      | ~ r2_hidden(D_34,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_94,plain,(
    ~ r2_hidden('#skF_6','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_52,plain,(
    ! [D_34] :
      ( r2_hidden('#skF_6',k8_setfam_1('#skF_5','#skF_7'))
      | r2_hidden('#skF_6',D_34)
      | ~ r2_hidden(D_34,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_114,plain,(
    ! [D_46] :
      ( r2_hidden('#skF_6',D_46)
      | ~ r2_hidden(D_46,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_52])).

tff(c_116,plain,(
    r2_hidden('#skF_6','#skF_8') ),
    inference(resolution,[status(thm)],[c_89,c_114])).

tff(c_120,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_116])).

tff(c_121,plain,(
    ! [D_34] :
      ( r2_hidden('#skF_6',D_34)
      | ~ r2_hidden(D_34,'#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_222,plain,(
    ! [C_66] :
      ( r2_hidden('#skF_6','#skF_1'('#skF_7',k1_setfam_1('#skF_7'),C_66))
      | r2_hidden(C_66,k1_setfam_1('#skF_7'))
      | k1_xboole_0 = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_200,c_121])).

tff(c_240,plain,(
    ! [C_66] :
      ( r2_hidden('#skF_6','#skF_1'('#skF_7',k1_setfam_1('#skF_7'),C_66))
      | r2_hidden(C_66,k1_setfam_1('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_222])).

tff(c_274,plain,(
    ! [C_70,A_71] :
      ( ~ r2_hidden(C_70,'#skF_1'(A_71,k1_setfam_1(A_71),C_70))
      | r2_hidden(C_70,k1_setfam_1(A_71))
      | k1_xboole_0 = A_71 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_278,plain,
    ( k1_xboole_0 = '#skF_7'
    | r2_hidden('#skF_6',k1_setfam_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_240,c_274])).

tff(c_284,plain,(
    r2_hidden('#skF_6',k1_setfam_1('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_278])).

tff(c_132,plain,(
    ! [A_48,B_49] :
      ( k6_setfam_1(A_48,B_49) = k1_setfam_1(B_49)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(k1_zfmisc_1(A_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_140,plain,(
    k6_setfam_1('#skF_5','#skF_7') = k1_setfam_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_40,c_132])).

tff(c_312,plain,(
    ! [A_73,B_74] :
      ( k8_setfam_1(A_73,B_74) = k6_setfam_1(A_73,B_74)
      | k1_xboole_0 = B_74
      | ~ m1_subset_1(B_74,k1_zfmisc_1(k1_zfmisc_1(A_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_315,plain,
    ( k8_setfam_1('#skF_5','#skF_7') = k6_setfam_1('#skF_5','#skF_7')
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_40,c_312])).

tff(c_321,plain,
    ( k8_setfam_1('#skF_5','#skF_7') = k1_setfam_1('#skF_7')
    | k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_315])).

tff(c_322,plain,(
    k8_setfam_1('#skF_5','#skF_7') = k1_setfam_1('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_321])).

tff(c_326,plain,(
    ~ r2_hidden('#skF_6',k1_setfam_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_322,c_71])).

tff(c_329,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_284,c_326])).

tff(c_330,plain,(
    ! [D_34] :
      ( r2_hidden('#skF_6',D_34)
      | ~ r2_hidden(D_34,'#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_458,plain,(
    ! [C_96] :
      ( r2_hidden('#skF_6','#skF_1'('#skF_7',k1_setfam_1('#skF_7'),C_96))
      | r2_hidden(C_96,k1_setfam_1('#skF_7'))
      | k1_xboole_0 = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_444,c_330])).

tff(c_474,plain,(
    ! [C_96] :
      ( r2_hidden('#skF_6','#skF_1'('#skF_7',k1_setfam_1('#skF_7'),C_96))
      | r2_hidden(C_96,k1_setfam_1('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_438,c_458])).

tff(c_507,plain,(
    ! [C_99,A_100] :
      ( ~ r2_hidden(C_99,'#skF_1'(A_100,k1_setfam_1(A_100),C_99))
      | r2_hidden(C_99,k1_setfam_1(A_100))
      | k1_xboole_0 = A_100 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_511,plain,
    ( k1_xboole_0 = '#skF_7'
    | r2_hidden('#skF_6',k1_setfam_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_474,c_507])).

tff(c_518,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_439,c_438,c_439,c_511])).

tff(c_520,plain,(
    r2_hidden('#skF_6',k8_setfam_1('#skF_5','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_42,plain,
    ( ~ r2_hidden('#skF_6','#skF_8')
    | ~ r2_hidden('#skF_6',k8_setfam_1('#skF_5','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_522,plain,(
    ~ r2_hidden('#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_520,c_42])).

tff(c_519,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_523,plain,(
    ! [A_101,B_102] :
      ( k2_xboole_0(k1_tarski(A_101),B_102) = B_102
      | ~ r2_hidden(A_101,B_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_535,plain,(
    ! [B_103,A_104] :
      ( k1_xboole_0 != B_103
      | ~ r2_hidden(A_104,B_103) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_523,c_4])).

tff(c_546,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(resolution,[status(thm)],[c_519,c_535])).

tff(c_556,plain,(
    ! [A_108,B_109] :
      ( k6_setfam_1(A_108,B_109) = k1_setfam_1(B_109)
      | ~ m1_subset_1(B_109,k1_zfmisc_1(k1_zfmisc_1(A_108))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_564,plain,(
    k6_setfam_1('#skF_5','#skF_7') = k1_setfam_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_40,c_556])).

tff(c_616,plain,(
    ! [A_122,B_123] :
      ( k8_setfam_1(A_122,B_123) = k6_setfam_1(A_122,B_123)
      | k1_xboole_0 = B_123
      | ~ m1_subset_1(B_123,k1_zfmisc_1(k1_zfmisc_1(A_122))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_619,plain,
    ( k8_setfam_1('#skF_5','#skF_7') = k6_setfam_1('#skF_5','#skF_7')
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_40,c_616])).

tff(c_625,plain,
    ( k8_setfam_1('#skF_5','#skF_7') = k1_setfam_1('#skF_7')
    | k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_564,c_619])).

tff(c_626,plain,(
    k8_setfam_1('#skF_5','#skF_7') = k1_setfam_1('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_546,c_625])).

tff(c_633,plain,(
    r2_hidden('#skF_6',k1_setfam_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_626,c_520])).

tff(c_596,plain,(
    ! [C_116,D_117,A_118] :
      ( r2_hidden(C_116,D_117)
      | ~ r2_hidden(D_117,A_118)
      | ~ r2_hidden(C_116,k1_setfam_1(A_118))
      | k1_xboole_0 = A_118 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_600,plain,(
    ! [C_116] :
      ( r2_hidden(C_116,'#skF_8')
      | ~ r2_hidden(C_116,k1_setfam_1('#skF_7'))
      | k1_xboole_0 = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_519,c_596])).

tff(c_608,plain,(
    ! [C_116] :
      ( r2_hidden(C_116,'#skF_8')
      | ~ r2_hidden(C_116,k1_setfam_1('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_546,c_600])).

tff(c_676,plain,(
    r2_hidden('#skF_6','#skF_8') ),
    inference(resolution,[status(thm)],[c_633,c_608])).

tff(c_687,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_522,c_676])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:40:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.11/1.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.14/1.48  
% 3.14/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.14/1.48  %$ r2_hidden > m1_subset_1 > k8_setfam_1 > k6_setfam_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_4
% 3.14/1.48  
% 3.14/1.48  %Foreground sorts:
% 3.14/1.48  
% 3.14/1.48  
% 3.14/1.48  %Background operators:
% 3.14/1.48  
% 3.14/1.48  
% 3.14/1.48  %Foreground operators:
% 3.14/1.48  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.14/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.14/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.14/1.48  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.14/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.14/1.48  tff(k8_setfam_1, type, k8_setfam_1: ($i * $i) > $i).
% 3.14/1.48  tff('#skF_7', type, '#skF_7': $i).
% 3.14/1.48  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.14/1.48  tff('#skF_5', type, '#skF_5': $i).
% 3.14/1.48  tff('#skF_6', type, '#skF_6': $i).
% 3.14/1.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.14/1.48  tff('#skF_8', type, '#skF_8': $i).
% 3.14/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.14/1.48  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 3.14/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.14/1.48  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.14/1.48  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.14/1.48  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.14/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.14/1.48  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.14/1.48  
% 3.14/1.50  tff(f_86, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => (r2_hidden(B, A) => (r2_hidden(B, k8_setfam_1(A, C)) <=> (![D]: (r2_hidden(D, C) => r2_hidden(B, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_setfam_1)).
% 3.14/1.50  tff(f_68, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k6_setfam_1(A, B) = k1_setfam_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_setfam_1)).
% 3.14/1.50  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ((~(B = k1_xboole_0) => (k8_setfam_1(A, B) = k6_setfam_1(A, B))) & ((B = k1_xboole_0) => (k8_setfam_1(A, B) = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_setfam_1)).
% 3.14/1.50  tff(f_34, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.14/1.50  tff(f_64, axiom, (![A, B]: ((~(A = k1_xboole_0) => ((B = k1_setfam_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (![D]: (r2_hidden(D, A) => r2_hidden(C, D))))))) & ((A = k1_xboole_0) => ((B = k1_setfam_1(A)) <=> (B = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_setfam_1)).
% 3.14/1.50  tff(f_29, axiom, (![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 3.14/1.50  tff(f_32, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 3.14/1.50  tff(c_38, plain, (r2_hidden('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.14/1.50  tff(c_40, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k1_zfmisc_1('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.14/1.50  tff(c_333, plain, (![A_76, B_77]: (k6_setfam_1(A_76, B_77)=k1_setfam_1(B_77) | ~m1_subset_1(B_77, k1_zfmisc_1(k1_zfmisc_1(A_76))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.14/1.50  tff(c_341, plain, (k6_setfam_1('#skF_5', '#skF_7')=k1_setfam_1('#skF_7')), inference(resolution, [status(thm)], [c_40, c_333])).
% 3.14/1.50  tff(c_380, plain, (![A_91, B_92]: (k8_setfam_1(A_91, B_92)=k6_setfam_1(A_91, B_92) | k1_xboole_0=B_92 | ~m1_subset_1(B_92, k1_zfmisc_1(k1_zfmisc_1(A_91))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.14/1.50  tff(c_383, plain, (k8_setfam_1('#skF_5', '#skF_7')=k6_setfam_1('#skF_5', '#skF_7') | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_40, c_380])).
% 3.14/1.50  tff(c_389, plain, (k8_setfam_1('#skF_5', '#skF_7')=k1_setfam_1('#skF_7') | k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_341, c_383])).
% 3.14/1.50  tff(c_393, plain, (k1_xboole_0='#skF_7'), inference(splitLeft, [status(thm)], [c_389])).
% 3.14/1.50  tff(c_6, plain, (![A_5]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.14/1.50  tff(c_8, plain, (![A_6]: (k8_setfam_1(A_6, k1_xboole_0)=A_6 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_6))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.14/1.50  tff(c_55, plain, (![A_6]: (k8_setfam_1(A_6, k1_xboole_0)=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_8])).
% 3.14/1.50  tff(c_401, plain, (![A_6]: (k8_setfam_1(A_6, '#skF_7')=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_393, c_55])).
% 3.14/1.50  tff(c_44, plain, (r2_hidden('#skF_8', '#skF_7') | ~r2_hidden('#skF_6', k8_setfam_1('#skF_5', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.14/1.50  tff(c_71, plain, (~r2_hidden('#skF_6', k8_setfam_1('#skF_5', '#skF_7'))), inference(splitLeft, [status(thm)], [c_44])).
% 3.14/1.50  tff(c_433, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_401, c_71])).
% 3.14/1.50  tff(c_436, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_433])).
% 3.14/1.50  tff(c_437, plain, (k8_setfam_1('#skF_5', '#skF_7')=k1_setfam_1('#skF_7')), inference(splitRight, [status(thm)], [c_389])).
% 3.14/1.50  tff(c_439, plain, (~r2_hidden('#skF_6', k1_setfam_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_437, c_71])).
% 3.14/1.50  tff(c_438, plain, (k1_xboole_0!='#skF_7'), inference(splitRight, [status(thm)], [c_389])).
% 3.14/1.50  tff(c_444, plain, (![A_95, C_96]: (r2_hidden('#skF_1'(A_95, k1_setfam_1(A_95), C_96), A_95) | r2_hidden(C_96, k1_setfam_1(A_95)) | k1_xboole_0=A_95)), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.14/1.50  tff(c_50, plain, (![D_34]: (r2_hidden('#skF_8', '#skF_7') | r2_hidden('#skF_6', D_34) | ~r2_hidden(D_34, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.14/1.50  tff(c_89, plain, (r2_hidden('#skF_8', '#skF_7')), inference(splitLeft, [status(thm)], [c_50])).
% 3.14/1.50  tff(c_72, plain, (![A_39, B_40]: (k2_xboole_0(k1_tarski(A_39), B_40)=B_40 | ~r2_hidden(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.14/1.50  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(k1_tarski(A_3), B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.14/1.50  tff(c_77, plain, (![B_40, A_39]: (k1_xboole_0!=B_40 | ~r2_hidden(A_39, B_40))), inference(superposition, [status(thm), theory('equality')], [c_72, c_4])).
% 3.14/1.50  tff(c_93, plain, (k1_xboole_0!='#skF_7'), inference(resolution, [status(thm)], [c_89, c_77])).
% 3.14/1.50  tff(c_200, plain, (![A_65, C_66]: (r2_hidden('#skF_1'(A_65, k1_setfam_1(A_65), C_66), A_65) | r2_hidden(C_66, k1_setfam_1(A_65)) | k1_xboole_0=A_65)), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.14/1.50  tff(c_48, plain, (![D_34]: (~r2_hidden('#skF_6', '#skF_8') | r2_hidden('#skF_6', D_34) | ~r2_hidden(D_34, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.14/1.50  tff(c_94, plain, (~r2_hidden('#skF_6', '#skF_8')), inference(splitLeft, [status(thm)], [c_48])).
% 3.14/1.50  tff(c_52, plain, (![D_34]: (r2_hidden('#skF_6', k8_setfam_1('#skF_5', '#skF_7')) | r2_hidden('#skF_6', D_34) | ~r2_hidden(D_34, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.14/1.50  tff(c_114, plain, (![D_46]: (r2_hidden('#skF_6', D_46) | ~r2_hidden(D_46, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_71, c_52])).
% 3.14/1.50  tff(c_116, plain, (r2_hidden('#skF_6', '#skF_8')), inference(resolution, [status(thm)], [c_89, c_114])).
% 3.14/1.50  tff(c_120, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_116])).
% 3.14/1.50  tff(c_121, plain, (![D_34]: (r2_hidden('#skF_6', D_34) | ~r2_hidden(D_34, '#skF_7'))), inference(splitRight, [status(thm)], [c_48])).
% 3.14/1.50  tff(c_222, plain, (![C_66]: (r2_hidden('#skF_6', '#skF_1'('#skF_7', k1_setfam_1('#skF_7'), C_66)) | r2_hidden(C_66, k1_setfam_1('#skF_7')) | k1_xboole_0='#skF_7')), inference(resolution, [status(thm)], [c_200, c_121])).
% 3.14/1.50  tff(c_240, plain, (![C_66]: (r2_hidden('#skF_6', '#skF_1'('#skF_7', k1_setfam_1('#skF_7'), C_66)) | r2_hidden(C_66, k1_setfam_1('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_93, c_222])).
% 3.14/1.50  tff(c_274, plain, (![C_70, A_71]: (~r2_hidden(C_70, '#skF_1'(A_71, k1_setfam_1(A_71), C_70)) | r2_hidden(C_70, k1_setfam_1(A_71)) | k1_xboole_0=A_71)), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.14/1.50  tff(c_278, plain, (k1_xboole_0='#skF_7' | r2_hidden('#skF_6', k1_setfam_1('#skF_7'))), inference(resolution, [status(thm)], [c_240, c_274])).
% 3.14/1.50  tff(c_284, plain, (r2_hidden('#skF_6', k1_setfam_1('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_93, c_278])).
% 3.14/1.50  tff(c_132, plain, (![A_48, B_49]: (k6_setfam_1(A_48, B_49)=k1_setfam_1(B_49) | ~m1_subset_1(B_49, k1_zfmisc_1(k1_zfmisc_1(A_48))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.14/1.50  tff(c_140, plain, (k6_setfam_1('#skF_5', '#skF_7')=k1_setfam_1('#skF_7')), inference(resolution, [status(thm)], [c_40, c_132])).
% 3.14/1.50  tff(c_312, plain, (![A_73, B_74]: (k8_setfam_1(A_73, B_74)=k6_setfam_1(A_73, B_74) | k1_xboole_0=B_74 | ~m1_subset_1(B_74, k1_zfmisc_1(k1_zfmisc_1(A_73))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.14/1.50  tff(c_315, plain, (k8_setfam_1('#skF_5', '#skF_7')=k6_setfam_1('#skF_5', '#skF_7') | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_40, c_312])).
% 3.14/1.50  tff(c_321, plain, (k8_setfam_1('#skF_5', '#skF_7')=k1_setfam_1('#skF_7') | k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_140, c_315])).
% 3.14/1.50  tff(c_322, plain, (k8_setfam_1('#skF_5', '#skF_7')=k1_setfam_1('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_93, c_321])).
% 3.14/1.50  tff(c_326, plain, (~r2_hidden('#skF_6', k1_setfam_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_322, c_71])).
% 3.14/1.50  tff(c_329, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_284, c_326])).
% 3.14/1.50  tff(c_330, plain, (![D_34]: (r2_hidden('#skF_6', D_34) | ~r2_hidden(D_34, '#skF_7'))), inference(splitRight, [status(thm)], [c_50])).
% 3.14/1.50  tff(c_458, plain, (![C_96]: (r2_hidden('#skF_6', '#skF_1'('#skF_7', k1_setfam_1('#skF_7'), C_96)) | r2_hidden(C_96, k1_setfam_1('#skF_7')) | k1_xboole_0='#skF_7')), inference(resolution, [status(thm)], [c_444, c_330])).
% 3.14/1.50  tff(c_474, plain, (![C_96]: (r2_hidden('#skF_6', '#skF_1'('#skF_7', k1_setfam_1('#skF_7'), C_96)) | r2_hidden(C_96, k1_setfam_1('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_438, c_458])).
% 3.14/1.50  tff(c_507, plain, (![C_99, A_100]: (~r2_hidden(C_99, '#skF_1'(A_100, k1_setfam_1(A_100), C_99)) | r2_hidden(C_99, k1_setfam_1(A_100)) | k1_xboole_0=A_100)), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.14/1.50  tff(c_511, plain, (k1_xboole_0='#skF_7' | r2_hidden('#skF_6', k1_setfam_1('#skF_7'))), inference(resolution, [status(thm)], [c_474, c_507])).
% 3.14/1.50  tff(c_518, plain, $false, inference(negUnitSimplification, [status(thm)], [c_439, c_438, c_439, c_511])).
% 3.14/1.50  tff(c_520, plain, (r2_hidden('#skF_6', k8_setfam_1('#skF_5', '#skF_7'))), inference(splitRight, [status(thm)], [c_44])).
% 3.14/1.50  tff(c_42, plain, (~r2_hidden('#skF_6', '#skF_8') | ~r2_hidden('#skF_6', k8_setfam_1('#skF_5', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.14/1.50  tff(c_522, plain, (~r2_hidden('#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_520, c_42])).
% 3.14/1.50  tff(c_519, plain, (r2_hidden('#skF_8', '#skF_7')), inference(splitRight, [status(thm)], [c_44])).
% 3.14/1.50  tff(c_523, plain, (![A_101, B_102]: (k2_xboole_0(k1_tarski(A_101), B_102)=B_102 | ~r2_hidden(A_101, B_102))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.14/1.50  tff(c_535, plain, (![B_103, A_104]: (k1_xboole_0!=B_103 | ~r2_hidden(A_104, B_103))), inference(superposition, [status(thm), theory('equality')], [c_523, c_4])).
% 3.14/1.50  tff(c_546, plain, (k1_xboole_0!='#skF_7'), inference(resolution, [status(thm)], [c_519, c_535])).
% 3.14/1.50  tff(c_556, plain, (![A_108, B_109]: (k6_setfam_1(A_108, B_109)=k1_setfam_1(B_109) | ~m1_subset_1(B_109, k1_zfmisc_1(k1_zfmisc_1(A_108))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.14/1.50  tff(c_564, plain, (k6_setfam_1('#skF_5', '#skF_7')=k1_setfam_1('#skF_7')), inference(resolution, [status(thm)], [c_40, c_556])).
% 3.14/1.50  tff(c_616, plain, (![A_122, B_123]: (k8_setfam_1(A_122, B_123)=k6_setfam_1(A_122, B_123) | k1_xboole_0=B_123 | ~m1_subset_1(B_123, k1_zfmisc_1(k1_zfmisc_1(A_122))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.14/1.50  tff(c_619, plain, (k8_setfam_1('#skF_5', '#skF_7')=k6_setfam_1('#skF_5', '#skF_7') | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_40, c_616])).
% 3.14/1.50  tff(c_625, plain, (k8_setfam_1('#skF_5', '#skF_7')=k1_setfam_1('#skF_7') | k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_564, c_619])).
% 3.14/1.50  tff(c_626, plain, (k8_setfam_1('#skF_5', '#skF_7')=k1_setfam_1('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_546, c_625])).
% 3.14/1.50  tff(c_633, plain, (r2_hidden('#skF_6', k1_setfam_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_626, c_520])).
% 3.14/1.50  tff(c_596, plain, (![C_116, D_117, A_118]: (r2_hidden(C_116, D_117) | ~r2_hidden(D_117, A_118) | ~r2_hidden(C_116, k1_setfam_1(A_118)) | k1_xboole_0=A_118)), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.14/1.50  tff(c_600, plain, (![C_116]: (r2_hidden(C_116, '#skF_8') | ~r2_hidden(C_116, k1_setfam_1('#skF_7')) | k1_xboole_0='#skF_7')), inference(resolution, [status(thm)], [c_519, c_596])).
% 3.14/1.50  tff(c_608, plain, (![C_116]: (r2_hidden(C_116, '#skF_8') | ~r2_hidden(C_116, k1_setfam_1('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_546, c_600])).
% 3.14/1.50  tff(c_676, plain, (r2_hidden('#skF_6', '#skF_8')), inference(resolution, [status(thm)], [c_633, c_608])).
% 3.14/1.50  tff(c_687, plain, $false, inference(negUnitSimplification, [status(thm)], [c_522, c_676])).
% 3.14/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.14/1.50  
% 3.14/1.50  Inference rules
% 3.14/1.50  ----------------------
% 3.14/1.50  #Ref     : 0
% 3.14/1.50  #Sup     : 131
% 3.14/1.50  #Fact    : 0
% 3.14/1.50  #Define  : 0
% 3.14/1.50  #Split   : 12
% 3.14/1.50  #Chain   : 0
% 3.14/1.50  #Close   : 0
% 3.14/1.50  
% 3.14/1.50  Ordering : KBO
% 3.14/1.50  
% 3.14/1.50  Simplification rules
% 3.14/1.50  ----------------------
% 3.14/1.50  #Subsume      : 6
% 3.14/1.50  #Demod        : 58
% 3.14/1.50  #Tautology    : 54
% 3.14/1.50  #SimpNegUnit  : 27
% 3.14/1.50  #BackRed      : 18
% 3.14/1.50  
% 3.14/1.50  #Partial instantiations: 0
% 3.14/1.50  #Strategies tried      : 1
% 3.14/1.50  
% 3.14/1.50  Timing (in seconds)
% 3.14/1.50  ----------------------
% 3.14/1.50  Preprocessing        : 0.34
% 3.14/1.50  Parsing              : 0.17
% 3.14/1.50  CNF conversion       : 0.03
% 3.14/1.50  Main loop            : 0.33
% 3.14/1.50  Inferencing          : 0.11
% 3.14/1.50  Reduction            : 0.11
% 3.14/1.50  Demodulation         : 0.07
% 3.14/1.50  BG Simplification    : 0.02
% 3.14/1.50  Subsumption          : 0.07
% 3.14/1.50  Abstraction          : 0.02
% 3.14/1.50  MUC search           : 0.00
% 3.14/1.50  Cooper               : 0.00
% 3.14/1.50  Total                : 0.72
% 3.14/1.50  Index Insertion      : 0.00
% 3.14/1.50  Index Deletion       : 0.00
% 3.14/1.50  Index Matching       : 0.00
% 3.14/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
