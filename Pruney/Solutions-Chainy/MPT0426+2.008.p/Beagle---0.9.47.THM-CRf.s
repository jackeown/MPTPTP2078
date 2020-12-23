%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:55 EST 2020

% Result     : Theorem 2.56s
% Output     : CNFRefutation 2.91s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 272 expanded)
%              Number of leaves         :   26 (  95 expanded)
%              Depth                    :    8
%              Number of atoms          :  156 ( 690 expanded)
%              Number of equality atoms :   61 ( 218 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > k8_setfam_1 > k6_setfam_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_setfam_1,type,(
    k6_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_88,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ( r2_hidden(B,A)
         => ( r2_hidden(B,k8_setfam_1(A,C))
          <=> ! [D] :
                ( r2_hidden(D,C)
               => r2_hidden(B,D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_setfam_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k6_setfam_1(A,B) = k1_setfam_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( ( B != k1_xboole_0
         => k8_setfam_1(A,B) = k6_setfam_1(A,B) )
        & ( B = k1_xboole_0
         => k8_setfam_1(A,B) = A ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).

tff(f_36,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_66,axiom,(
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

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(c_42,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_44,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k1_zfmisc_1('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_379,plain,(
    ! [A_74,B_75] :
      ( k6_setfam_1(A_74,B_75) = k1_setfam_1(B_75)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(k1_zfmisc_1(A_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_387,plain,(
    k6_setfam_1('#skF_5','#skF_7') = k1_setfam_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_44,c_379])).

tff(c_474,plain,(
    ! [A_91,B_92] :
      ( k8_setfam_1(A_91,B_92) = k6_setfam_1(A_91,B_92)
      | k1_xboole_0 = B_92
      | ~ m1_subset_1(B_92,k1_zfmisc_1(k1_zfmisc_1(A_91))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_477,plain,
    ( k8_setfam_1('#skF_5','#skF_7') = k6_setfam_1('#skF_5','#skF_7')
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_44,c_474])).

tff(c_483,plain,
    ( k8_setfam_1('#skF_5','#skF_7') = k1_setfam_1('#skF_7')
    | k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_387,c_477])).

tff(c_487,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_483])).

tff(c_10,plain,(
    ! [A_5] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_12,plain,(
    ! [A_6] :
      ( k8_setfam_1(A_6,k1_xboole_0) = A_6
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_6))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_59,plain,(
    ! [A_6] : k8_setfam_1(A_6,k1_xboole_0) = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_12])).

tff(c_497,plain,(
    ! [A_6] : k8_setfam_1(A_6,'#skF_7') = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_487,c_59])).

tff(c_46,plain,
    ( ~ r2_hidden('#skF_6','#skF_8')
    | ~ r2_hidden('#skF_6',k8_setfam_1('#skF_5','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_104,plain,(
    ~ r2_hidden('#skF_6',k8_setfam_1('#skF_5','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_589,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_497,c_104])).

tff(c_592,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_589])).

tff(c_593,plain,(
    k8_setfam_1('#skF_5','#skF_7') = k1_setfam_1('#skF_7') ),
    inference(splitRight,[status(thm)],[c_483])).

tff(c_627,plain,(
    ~ r2_hidden('#skF_6',k1_setfam_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_593,c_104])).

tff(c_594,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_483])).

tff(c_595,plain,(
    ! [A_100,C_101] :
      ( r2_hidden('#skF_1'(A_100,k1_setfam_1(A_100),C_101),A_100)
      | r2_hidden(C_101,k1_setfam_1(A_100))
      | k1_xboole_0 = A_100 ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_54,plain,(
    ! [D_34] :
      ( r2_hidden('#skF_8','#skF_7')
      | r2_hidden('#skF_6',D_34)
      | ~ r2_hidden(D_34,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_116,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_188,plain,(
    ! [C_58,D_59,A_60] :
      ( r2_hidden(C_58,D_59)
      | ~ r2_hidden(D_59,A_60)
      | ~ r2_hidden(C_58,k1_setfam_1(A_60))
      | k1_xboole_0 = A_60 ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_196,plain,(
    ! [C_58] :
      ( r2_hidden(C_58,'#skF_8')
      | ~ r2_hidden(C_58,k1_setfam_1('#skF_7'))
      | k1_xboole_0 = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_116,c_188])).

tff(c_243,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_196])).

tff(c_4,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_96,plain,(
    ! [A_39,B_40] : ~ r2_hidden(A_39,k2_zfmisc_1(A_39,B_40)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_99,plain,(
    ! [A_1] : ~ r2_hidden(A_1,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_96])).

tff(c_248,plain,(
    ! [A_1] : ~ r2_hidden(A_1,'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_243,c_99])).

tff(c_264,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_248,c_116])).

tff(c_266,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_196])).

tff(c_140,plain,(
    ! [A_49,B_50] :
      ( k6_setfam_1(A_49,B_50) = k1_setfam_1(B_50)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(k1_zfmisc_1(A_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_148,plain,(
    k6_setfam_1('#skF_5','#skF_7') = k1_setfam_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_44,c_140])).

tff(c_301,plain,(
    ! [A_67,B_68] :
      ( k8_setfam_1(A_67,B_68) = k6_setfam_1(A_67,B_68)
      | k1_xboole_0 = B_68
      | ~ m1_subset_1(B_68,k1_zfmisc_1(k1_zfmisc_1(A_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_304,plain,
    ( k8_setfam_1('#skF_5','#skF_7') = k6_setfam_1('#skF_5','#skF_7')
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_44,c_301])).

tff(c_310,plain,
    ( k8_setfam_1('#skF_5','#skF_7') = k1_setfam_1('#skF_7')
    | k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_304])).

tff(c_311,plain,(
    k8_setfam_1('#skF_5','#skF_7') = k1_setfam_1('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_266,c_310])).

tff(c_315,plain,(
    ~ r2_hidden('#skF_6',k1_setfam_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_311,c_104])).

tff(c_321,plain,(
    ! [A_70,C_71] :
      ( r2_hidden('#skF_1'(A_70,k1_setfam_1(A_70),C_71),A_70)
      | r2_hidden(C_71,k1_setfam_1(A_70))
      | k1_xboole_0 = A_70 ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_52,plain,(
    ! [D_34] :
      ( ~ r2_hidden('#skF_6','#skF_8')
      | r2_hidden('#skF_6',D_34)
      | ~ r2_hidden(D_34,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_117,plain,(
    ~ r2_hidden('#skF_6','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_56,plain,(
    ! [D_34] :
      ( r2_hidden('#skF_6',k8_setfam_1('#skF_5','#skF_7'))
      | r2_hidden('#skF_6',D_34)
      | ~ r2_hidden(D_34,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_126,plain,(
    ! [D_47] :
      ( r2_hidden('#skF_6',D_47)
      | ~ r2_hidden(D_47,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_56])).

tff(c_128,plain,(
    r2_hidden('#skF_6','#skF_8') ),
    inference(resolution,[status(thm)],[c_116,c_126])).

tff(c_132,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_117,c_128])).

tff(c_133,plain,(
    ! [D_34] :
      ( r2_hidden('#skF_6',D_34)
      | ~ r2_hidden(D_34,'#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_340,plain,(
    ! [C_71] :
      ( r2_hidden('#skF_6','#skF_1'('#skF_7',k1_setfam_1('#skF_7'),C_71))
      | r2_hidden(C_71,k1_setfam_1('#skF_7'))
      | k1_xboole_0 = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_321,c_133])).

tff(c_363,plain,(
    ! [C_72] :
      ( r2_hidden('#skF_6','#skF_1'('#skF_7',k1_setfam_1('#skF_7'),C_72))
      | r2_hidden(C_72,k1_setfam_1('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_266,c_340])).

tff(c_30,plain,(
    ! [C_20,A_8] :
      ( ~ r2_hidden(C_20,'#skF_1'(A_8,k1_setfam_1(A_8),C_20))
      | r2_hidden(C_20,k1_setfam_1(A_8))
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_367,plain,
    ( k1_xboole_0 = '#skF_7'
    | r2_hidden('#skF_6',k1_setfam_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_363,c_30])).

tff(c_375,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_315,c_266,c_315,c_367])).

tff(c_376,plain,(
    ! [D_34] :
      ( r2_hidden('#skF_6',D_34)
      | ~ r2_hidden(D_34,'#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_606,plain,(
    ! [C_101] :
      ( r2_hidden('#skF_6','#skF_1'('#skF_7',k1_setfam_1('#skF_7'),C_101))
      | r2_hidden(C_101,k1_setfam_1('#skF_7'))
      | k1_xboole_0 = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_595,c_376])).

tff(c_632,plain,(
    ! [C_102] :
      ( r2_hidden('#skF_6','#skF_1'('#skF_7',k1_setfam_1('#skF_7'),C_102))
      | r2_hidden(C_102,k1_setfam_1('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_594,c_606])).

tff(c_636,plain,
    ( k1_xboole_0 = '#skF_7'
    | r2_hidden('#skF_6',k1_setfam_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_632,c_30])).

tff(c_644,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_627,c_594,c_627,c_636])).

tff(c_645,plain,(
    ~ r2_hidden('#skF_6','#skF_8') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_646,plain,(
    r2_hidden('#skF_6',k8_setfam_1('#skF_5','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_48,plain,
    ( r2_hidden('#skF_8','#skF_7')
    | ~ r2_hidden('#skF_6',k8_setfam_1('#skF_5','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_647,plain,(
    ~ r2_hidden('#skF_6',k8_setfam_1('#skF_5','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_649,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_646,c_647])).

tff(c_650,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_712,plain,(
    ! [C_114,D_115,A_116] :
      ( r2_hidden(C_114,D_115)
      | ~ r2_hidden(D_115,A_116)
      | ~ r2_hidden(C_114,k1_setfam_1(A_116))
      | k1_xboole_0 = A_116 ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_720,plain,(
    ! [C_114] :
      ( r2_hidden(C_114,'#skF_8')
      | ~ r2_hidden(C_114,k1_setfam_1('#skF_7'))
      | k1_xboole_0 = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_650,c_712])).

tff(c_722,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_720])).

tff(c_726,plain,(
    ! [A_1] : ~ r2_hidden(A_1,'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_722,c_99])).

tff(c_737,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_726,c_650])).

tff(c_739,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_720])).

tff(c_686,plain,(
    ! [A_111,B_112] :
      ( k6_setfam_1(A_111,B_112) = k1_setfam_1(B_112)
      | ~ m1_subset_1(B_112,k1_zfmisc_1(k1_zfmisc_1(A_111))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_694,plain,(
    k6_setfam_1('#skF_5','#skF_7') = k1_setfam_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_44,c_686])).

tff(c_805,plain,(
    ! [A_122,B_123] :
      ( k8_setfam_1(A_122,B_123) = k6_setfam_1(A_122,B_123)
      | k1_xboole_0 = B_123
      | ~ m1_subset_1(B_123,k1_zfmisc_1(k1_zfmisc_1(A_122))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_808,plain,
    ( k8_setfam_1('#skF_5','#skF_7') = k6_setfam_1('#skF_5','#skF_7')
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_44,c_805])).

tff(c_814,plain,
    ( k8_setfam_1('#skF_5','#skF_7') = k1_setfam_1('#skF_7')
    | k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_694,c_808])).

tff(c_815,plain,(
    k8_setfam_1('#skF_5','#skF_7') = k1_setfam_1('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_739,c_814])).

tff(c_651,plain,(
    r2_hidden('#skF_6',k8_setfam_1('#skF_5','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_822,plain,(
    r2_hidden('#skF_6',k1_setfam_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_815,c_651])).

tff(c_738,plain,(
    ! [C_114] :
      ( r2_hidden(C_114,'#skF_8')
      | ~ r2_hidden(C_114,k1_setfam_1('#skF_7')) ) ),
    inference(splitRight,[status(thm)],[c_720])).

tff(c_836,plain,(
    r2_hidden('#skF_6','#skF_8') ),
    inference(resolution,[status(thm)],[c_822,c_738])).

tff(c_844,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_645,c_836])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:28:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.56/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.56/1.43  
% 2.56/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.56/1.43  %$ r2_hidden > m1_subset_1 > k8_setfam_1 > k6_setfam_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_4
% 2.56/1.43  
% 2.56/1.43  %Foreground sorts:
% 2.56/1.43  
% 2.56/1.43  
% 2.56/1.43  %Background operators:
% 2.56/1.43  
% 2.56/1.43  
% 2.56/1.43  %Foreground operators:
% 2.56/1.43  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.56/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.56/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.56/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.56/1.43  tff(k8_setfam_1, type, k8_setfam_1: ($i * $i) > $i).
% 2.56/1.43  tff('#skF_7', type, '#skF_7': $i).
% 2.56/1.43  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.56/1.43  tff('#skF_5', type, '#skF_5': $i).
% 2.56/1.43  tff('#skF_6', type, '#skF_6': $i).
% 2.56/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.56/1.43  tff('#skF_8', type, '#skF_8': $i).
% 2.56/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.56/1.43  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.56/1.43  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 2.56/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.56/1.43  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.56/1.43  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.56/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.56/1.43  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.56/1.43  
% 2.91/1.45  tff(f_88, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => (r2_hidden(B, A) => (r2_hidden(B, k8_setfam_1(A, C)) <=> (![D]: (r2_hidden(D, C) => r2_hidden(B, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_setfam_1)).
% 2.91/1.45  tff(f_70, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k6_setfam_1(A, B) = k1_setfam_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_setfam_1)).
% 2.91/1.45  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ((~(B = k1_xboole_0) => (k8_setfam_1(A, B) = k6_setfam_1(A, B))) & ((B = k1_xboole_0) => (k8_setfam_1(A, B) = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_setfam_1)).
% 2.91/1.45  tff(f_36, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.91/1.45  tff(f_66, axiom, (![A, B]: ((~(A = k1_xboole_0) => ((B = k1_setfam_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (![D]: (r2_hidden(D, A) => r2_hidden(C, D))))))) & ((A = k1_xboole_0) => ((B = k1_setfam_1(A)) <=> (B = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_setfam_1)).
% 2.91/1.45  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.91/1.45  tff(f_34, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 2.91/1.45  tff(c_42, plain, (r2_hidden('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.91/1.45  tff(c_44, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k1_zfmisc_1('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.91/1.45  tff(c_379, plain, (![A_74, B_75]: (k6_setfam_1(A_74, B_75)=k1_setfam_1(B_75) | ~m1_subset_1(B_75, k1_zfmisc_1(k1_zfmisc_1(A_74))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.91/1.45  tff(c_387, plain, (k6_setfam_1('#skF_5', '#skF_7')=k1_setfam_1('#skF_7')), inference(resolution, [status(thm)], [c_44, c_379])).
% 2.91/1.45  tff(c_474, plain, (![A_91, B_92]: (k8_setfam_1(A_91, B_92)=k6_setfam_1(A_91, B_92) | k1_xboole_0=B_92 | ~m1_subset_1(B_92, k1_zfmisc_1(k1_zfmisc_1(A_91))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.91/1.45  tff(c_477, plain, (k8_setfam_1('#skF_5', '#skF_7')=k6_setfam_1('#skF_5', '#skF_7') | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_44, c_474])).
% 2.91/1.45  tff(c_483, plain, (k8_setfam_1('#skF_5', '#skF_7')=k1_setfam_1('#skF_7') | k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_387, c_477])).
% 2.91/1.45  tff(c_487, plain, (k1_xboole_0='#skF_7'), inference(splitLeft, [status(thm)], [c_483])).
% 2.91/1.45  tff(c_10, plain, (![A_5]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.91/1.45  tff(c_12, plain, (![A_6]: (k8_setfam_1(A_6, k1_xboole_0)=A_6 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_6))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.91/1.45  tff(c_59, plain, (![A_6]: (k8_setfam_1(A_6, k1_xboole_0)=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_12])).
% 2.91/1.45  tff(c_497, plain, (![A_6]: (k8_setfam_1(A_6, '#skF_7')=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_487, c_59])).
% 2.91/1.45  tff(c_46, plain, (~r2_hidden('#skF_6', '#skF_8') | ~r2_hidden('#skF_6', k8_setfam_1('#skF_5', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.91/1.45  tff(c_104, plain, (~r2_hidden('#skF_6', k8_setfam_1('#skF_5', '#skF_7'))), inference(splitLeft, [status(thm)], [c_46])).
% 2.91/1.45  tff(c_589, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_497, c_104])).
% 2.91/1.45  tff(c_592, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_589])).
% 2.91/1.45  tff(c_593, plain, (k8_setfam_1('#skF_5', '#skF_7')=k1_setfam_1('#skF_7')), inference(splitRight, [status(thm)], [c_483])).
% 2.91/1.45  tff(c_627, plain, (~r2_hidden('#skF_6', k1_setfam_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_593, c_104])).
% 2.91/1.45  tff(c_594, plain, (k1_xboole_0!='#skF_7'), inference(splitRight, [status(thm)], [c_483])).
% 2.91/1.45  tff(c_595, plain, (![A_100, C_101]: (r2_hidden('#skF_1'(A_100, k1_setfam_1(A_100), C_101), A_100) | r2_hidden(C_101, k1_setfam_1(A_100)) | k1_xboole_0=A_100)), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.91/1.45  tff(c_54, plain, (![D_34]: (r2_hidden('#skF_8', '#skF_7') | r2_hidden('#skF_6', D_34) | ~r2_hidden(D_34, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.91/1.45  tff(c_116, plain, (r2_hidden('#skF_8', '#skF_7')), inference(splitLeft, [status(thm)], [c_54])).
% 2.91/1.45  tff(c_188, plain, (![C_58, D_59, A_60]: (r2_hidden(C_58, D_59) | ~r2_hidden(D_59, A_60) | ~r2_hidden(C_58, k1_setfam_1(A_60)) | k1_xboole_0=A_60)), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.91/1.45  tff(c_196, plain, (![C_58]: (r2_hidden(C_58, '#skF_8') | ~r2_hidden(C_58, k1_setfam_1('#skF_7')) | k1_xboole_0='#skF_7')), inference(resolution, [status(thm)], [c_116, c_188])).
% 2.91/1.45  tff(c_243, plain, (k1_xboole_0='#skF_7'), inference(splitLeft, [status(thm)], [c_196])).
% 2.91/1.45  tff(c_4, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.91/1.45  tff(c_96, plain, (![A_39, B_40]: (~r2_hidden(A_39, k2_zfmisc_1(A_39, B_40)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.91/1.45  tff(c_99, plain, (![A_1]: (~r2_hidden(A_1, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_96])).
% 2.91/1.45  tff(c_248, plain, (![A_1]: (~r2_hidden(A_1, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_243, c_99])).
% 2.91/1.45  tff(c_264, plain, $false, inference(negUnitSimplification, [status(thm)], [c_248, c_116])).
% 2.91/1.45  tff(c_266, plain, (k1_xboole_0!='#skF_7'), inference(splitRight, [status(thm)], [c_196])).
% 2.91/1.45  tff(c_140, plain, (![A_49, B_50]: (k6_setfam_1(A_49, B_50)=k1_setfam_1(B_50) | ~m1_subset_1(B_50, k1_zfmisc_1(k1_zfmisc_1(A_49))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.91/1.45  tff(c_148, plain, (k6_setfam_1('#skF_5', '#skF_7')=k1_setfam_1('#skF_7')), inference(resolution, [status(thm)], [c_44, c_140])).
% 2.91/1.45  tff(c_301, plain, (![A_67, B_68]: (k8_setfam_1(A_67, B_68)=k6_setfam_1(A_67, B_68) | k1_xboole_0=B_68 | ~m1_subset_1(B_68, k1_zfmisc_1(k1_zfmisc_1(A_67))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.91/1.45  tff(c_304, plain, (k8_setfam_1('#skF_5', '#skF_7')=k6_setfam_1('#skF_5', '#skF_7') | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_44, c_301])).
% 2.91/1.45  tff(c_310, plain, (k8_setfam_1('#skF_5', '#skF_7')=k1_setfam_1('#skF_7') | k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_148, c_304])).
% 2.91/1.45  tff(c_311, plain, (k8_setfam_1('#skF_5', '#skF_7')=k1_setfam_1('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_266, c_310])).
% 2.91/1.45  tff(c_315, plain, (~r2_hidden('#skF_6', k1_setfam_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_311, c_104])).
% 2.91/1.45  tff(c_321, plain, (![A_70, C_71]: (r2_hidden('#skF_1'(A_70, k1_setfam_1(A_70), C_71), A_70) | r2_hidden(C_71, k1_setfam_1(A_70)) | k1_xboole_0=A_70)), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.91/1.45  tff(c_52, plain, (![D_34]: (~r2_hidden('#skF_6', '#skF_8') | r2_hidden('#skF_6', D_34) | ~r2_hidden(D_34, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.91/1.45  tff(c_117, plain, (~r2_hidden('#skF_6', '#skF_8')), inference(splitLeft, [status(thm)], [c_52])).
% 2.91/1.45  tff(c_56, plain, (![D_34]: (r2_hidden('#skF_6', k8_setfam_1('#skF_5', '#skF_7')) | r2_hidden('#skF_6', D_34) | ~r2_hidden(D_34, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.91/1.45  tff(c_126, plain, (![D_47]: (r2_hidden('#skF_6', D_47) | ~r2_hidden(D_47, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_104, c_56])).
% 2.91/1.45  tff(c_128, plain, (r2_hidden('#skF_6', '#skF_8')), inference(resolution, [status(thm)], [c_116, c_126])).
% 2.91/1.45  tff(c_132, plain, $false, inference(negUnitSimplification, [status(thm)], [c_117, c_128])).
% 2.91/1.45  tff(c_133, plain, (![D_34]: (r2_hidden('#skF_6', D_34) | ~r2_hidden(D_34, '#skF_7'))), inference(splitRight, [status(thm)], [c_52])).
% 2.91/1.45  tff(c_340, plain, (![C_71]: (r2_hidden('#skF_6', '#skF_1'('#skF_7', k1_setfam_1('#skF_7'), C_71)) | r2_hidden(C_71, k1_setfam_1('#skF_7')) | k1_xboole_0='#skF_7')), inference(resolution, [status(thm)], [c_321, c_133])).
% 2.91/1.45  tff(c_363, plain, (![C_72]: (r2_hidden('#skF_6', '#skF_1'('#skF_7', k1_setfam_1('#skF_7'), C_72)) | r2_hidden(C_72, k1_setfam_1('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_266, c_340])).
% 2.91/1.45  tff(c_30, plain, (![C_20, A_8]: (~r2_hidden(C_20, '#skF_1'(A_8, k1_setfam_1(A_8), C_20)) | r2_hidden(C_20, k1_setfam_1(A_8)) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.91/1.45  tff(c_367, plain, (k1_xboole_0='#skF_7' | r2_hidden('#skF_6', k1_setfam_1('#skF_7'))), inference(resolution, [status(thm)], [c_363, c_30])).
% 2.91/1.45  tff(c_375, plain, $false, inference(negUnitSimplification, [status(thm)], [c_315, c_266, c_315, c_367])).
% 2.91/1.45  tff(c_376, plain, (![D_34]: (r2_hidden('#skF_6', D_34) | ~r2_hidden(D_34, '#skF_7'))), inference(splitRight, [status(thm)], [c_54])).
% 2.91/1.45  tff(c_606, plain, (![C_101]: (r2_hidden('#skF_6', '#skF_1'('#skF_7', k1_setfam_1('#skF_7'), C_101)) | r2_hidden(C_101, k1_setfam_1('#skF_7')) | k1_xboole_0='#skF_7')), inference(resolution, [status(thm)], [c_595, c_376])).
% 2.91/1.45  tff(c_632, plain, (![C_102]: (r2_hidden('#skF_6', '#skF_1'('#skF_7', k1_setfam_1('#skF_7'), C_102)) | r2_hidden(C_102, k1_setfam_1('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_594, c_606])).
% 2.91/1.45  tff(c_636, plain, (k1_xboole_0='#skF_7' | r2_hidden('#skF_6', k1_setfam_1('#skF_7'))), inference(resolution, [status(thm)], [c_632, c_30])).
% 2.91/1.45  tff(c_644, plain, $false, inference(negUnitSimplification, [status(thm)], [c_627, c_594, c_627, c_636])).
% 2.91/1.45  tff(c_645, plain, (~r2_hidden('#skF_6', '#skF_8')), inference(splitRight, [status(thm)], [c_46])).
% 2.91/1.45  tff(c_646, plain, (r2_hidden('#skF_6', k8_setfam_1('#skF_5', '#skF_7'))), inference(splitRight, [status(thm)], [c_46])).
% 2.91/1.45  tff(c_48, plain, (r2_hidden('#skF_8', '#skF_7') | ~r2_hidden('#skF_6', k8_setfam_1('#skF_5', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.91/1.45  tff(c_647, plain, (~r2_hidden('#skF_6', k8_setfam_1('#skF_5', '#skF_7'))), inference(splitLeft, [status(thm)], [c_48])).
% 2.91/1.45  tff(c_649, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_646, c_647])).
% 2.91/1.45  tff(c_650, plain, (r2_hidden('#skF_8', '#skF_7')), inference(splitRight, [status(thm)], [c_48])).
% 2.91/1.45  tff(c_712, plain, (![C_114, D_115, A_116]: (r2_hidden(C_114, D_115) | ~r2_hidden(D_115, A_116) | ~r2_hidden(C_114, k1_setfam_1(A_116)) | k1_xboole_0=A_116)), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.91/1.45  tff(c_720, plain, (![C_114]: (r2_hidden(C_114, '#skF_8') | ~r2_hidden(C_114, k1_setfam_1('#skF_7')) | k1_xboole_0='#skF_7')), inference(resolution, [status(thm)], [c_650, c_712])).
% 2.91/1.45  tff(c_722, plain, (k1_xboole_0='#skF_7'), inference(splitLeft, [status(thm)], [c_720])).
% 2.91/1.45  tff(c_726, plain, (![A_1]: (~r2_hidden(A_1, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_722, c_99])).
% 2.91/1.45  tff(c_737, plain, $false, inference(negUnitSimplification, [status(thm)], [c_726, c_650])).
% 2.91/1.45  tff(c_739, plain, (k1_xboole_0!='#skF_7'), inference(splitRight, [status(thm)], [c_720])).
% 2.91/1.45  tff(c_686, plain, (![A_111, B_112]: (k6_setfam_1(A_111, B_112)=k1_setfam_1(B_112) | ~m1_subset_1(B_112, k1_zfmisc_1(k1_zfmisc_1(A_111))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.91/1.45  tff(c_694, plain, (k6_setfam_1('#skF_5', '#skF_7')=k1_setfam_1('#skF_7')), inference(resolution, [status(thm)], [c_44, c_686])).
% 2.91/1.45  tff(c_805, plain, (![A_122, B_123]: (k8_setfam_1(A_122, B_123)=k6_setfam_1(A_122, B_123) | k1_xboole_0=B_123 | ~m1_subset_1(B_123, k1_zfmisc_1(k1_zfmisc_1(A_122))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.91/1.45  tff(c_808, plain, (k8_setfam_1('#skF_5', '#skF_7')=k6_setfam_1('#skF_5', '#skF_7') | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_44, c_805])).
% 2.91/1.45  tff(c_814, plain, (k8_setfam_1('#skF_5', '#skF_7')=k1_setfam_1('#skF_7') | k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_694, c_808])).
% 2.91/1.45  tff(c_815, plain, (k8_setfam_1('#skF_5', '#skF_7')=k1_setfam_1('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_739, c_814])).
% 2.91/1.45  tff(c_651, plain, (r2_hidden('#skF_6', k8_setfam_1('#skF_5', '#skF_7'))), inference(splitRight, [status(thm)], [c_48])).
% 2.91/1.45  tff(c_822, plain, (r2_hidden('#skF_6', k1_setfam_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_815, c_651])).
% 2.91/1.45  tff(c_738, plain, (![C_114]: (r2_hidden(C_114, '#skF_8') | ~r2_hidden(C_114, k1_setfam_1('#skF_7')))), inference(splitRight, [status(thm)], [c_720])).
% 2.91/1.45  tff(c_836, plain, (r2_hidden('#skF_6', '#skF_8')), inference(resolution, [status(thm)], [c_822, c_738])).
% 2.91/1.45  tff(c_844, plain, $false, inference(negUnitSimplification, [status(thm)], [c_645, c_836])).
% 2.91/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.91/1.45  
% 2.91/1.45  Inference rules
% 2.91/1.45  ----------------------
% 2.91/1.45  #Ref     : 0
% 2.91/1.45  #Sup     : 155
% 2.91/1.45  #Fact    : 0
% 2.91/1.45  #Define  : 0
% 2.91/1.45  #Split   : 17
% 2.91/1.45  #Chain   : 0
% 2.91/1.45  #Close   : 0
% 2.91/1.45  
% 2.91/1.45  Ordering : KBO
% 2.91/1.45  
% 2.91/1.45  Simplification rules
% 2.91/1.45  ----------------------
% 2.91/1.45  #Subsume      : 29
% 2.91/1.45  #Demod        : 167
% 2.91/1.45  #Tautology    : 90
% 2.91/1.45  #SimpNegUnit  : 33
% 2.91/1.45  #BackRed      : 91
% 2.91/1.45  
% 2.91/1.45  #Partial instantiations: 0
% 2.91/1.45  #Strategies tried      : 1
% 2.91/1.45  
% 2.91/1.45  Timing (in seconds)
% 2.91/1.45  ----------------------
% 2.91/1.45  Preprocessing        : 0.31
% 2.91/1.45  Parsing              : 0.16
% 2.91/1.45  CNF conversion       : 0.02
% 2.91/1.45  Main loop            : 0.35
% 2.91/1.45  Inferencing          : 0.11
% 2.91/1.45  Reduction            : 0.12
% 2.91/1.45  Demodulation         : 0.07
% 2.91/1.45  BG Simplification    : 0.02
% 2.91/1.45  Subsumption          : 0.06
% 2.91/1.45  Abstraction          : 0.02
% 2.91/1.45  MUC search           : 0.00
% 2.91/1.45  Cooper               : 0.00
% 2.91/1.45  Total                : 0.70
% 2.91/1.45  Index Insertion      : 0.00
% 2.91/1.45  Index Deletion       : 0.00
% 2.91/1.45  Index Matching       : 0.00
% 2.91/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
