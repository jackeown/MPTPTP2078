%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:55 EST 2020

% Result     : Theorem 3.05s
% Output     : CNFRefutation 3.05s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 273 expanded)
%              Number of leaves         :   27 (  98 expanded)
%              Depth                    :    8
%              Number of atoms          :  147 ( 655 expanded)
%              Number of equality atoms :   59 ( 222 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > k8_setfam_1 > k6_setfam_1 > k4_xboole_0 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_4

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

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_setfam_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k6_setfam_1(A,B) = k1_setfam_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( ( B != k1_xboole_0
         => k8_setfam_1(A,B) = k6_setfam_1(A,B) )
        & ( B = k1_xboole_0
         => k8_setfam_1(A,B) = A ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).

tff(f_36,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_setfam_1)).

tff(f_27,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(c_42,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_44,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k1_zfmisc_1('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_627,plain,(
    ! [A_109,B_110] :
      ( k6_setfam_1(A_109,B_110) = k1_setfam_1(B_110)
      | ~ m1_subset_1(B_110,k1_zfmisc_1(k1_zfmisc_1(A_109))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_635,plain,(
    k6_setfam_1('#skF_5','#skF_7') = k1_setfam_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_44,c_627])).

tff(c_750,plain,(
    ! [A_127,B_128] :
      ( k8_setfam_1(A_127,B_128) = k6_setfam_1(A_127,B_128)
      | k1_xboole_0 = B_128
      | ~ m1_subset_1(B_128,k1_zfmisc_1(k1_zfmisc_1(A_127))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_753,plain,
    ( k8_setfam_1('#skF_5','#skF_7') = k6_setfam_1('#skF_5','#skF_7')
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_44,c_750])).

tff(c_759,plain,
    ( k8_setfam_1('#skF_5','#skF_7') = k1_setfam_1('#skF_7')
    | k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_635,c_753])).

tff(c_763,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_759])).

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

tff(c_771,plain,(
    ! [A_6] : k8_setfam_1(A_6,'#skF_7') = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_763,c_59])).

tff(c_48,plain,
    ( r2_hidden('#skF_8','#skF_7')
    | ~ r2_hidden('#skF_6',k8_setfam_1('#skF_5','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_86,plain,(
    ~ r2_hidden('#skF_6',k8_setfam_1('#skF_5','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_788,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_771,c_86])).

tff(c_791,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_788])).

tff(c_792,plain,(
    k8_setfam_1('#skF_5','#skF_7') = k1_setfam_1('#skF_7') ),
    inference(splitRight,[status(thm)],[c_759])).

tff(c_801,plain,(
    ~ r2_hidden('#skF_6',k1_setfam_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_792,c_86])).

tff(c_793,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_759])).

tff(c_807,plain,(
    ! [A_133,C_134] :
      ( r2_hidden('#skF_1'(A_133,k1_setfam_1(A_133),C_134),A_133)
      | r2_hidden(C_134,k1_setfam_1(A_133))
      | k1_xboole_0 = A_133 ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_125,plain,(
    ! [A_49,B_50] :
      ( k6_setfam_1(A_49,B_50) = k1_setfam_1(B_50)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(k1_zfmisc_1(A_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_133,plain,(
    k6_setfam_1('#skF_5','#skF_7') = k1_setfam_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_44,c_125])).

tff(c_232,plain,(
    ! [A_72,B_73] :
      ( k8_setfam_1(A_72,B_73) = k6_setfam_1(A_72,B_73)
      | k1_xboole_0 = B_73
      | ~ m1_subset_1(B_73,k1_zfmisc_1(k1_zfmisc_1(A_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_235,plain,
    ( k8_setfam_1('#skF_5','#skF_7') = k6_setfam_1('#skF_5','#skF_7')
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_44,c_232])).

tff(c_241,plain,
    ( k8_setfam_1('#skF_5','#skF_7') = k1_setfam_1('#skF_7')
    | k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_235])).

tff(c_245,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_241])).

tff(c_253,plain,(
    ! [A_6] : k8_setfam_1(A_6,'#skF_7') = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_245,c_59])).

tff(c_331,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_253,c_86])).

tff(c_334,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_331])).

tff(c_335,plain,(
    k8_setfam_1('#skF_5','#skF_7') = k1_setfam_1('#skF_7') ),
    inference(splitRight,[status(thm)],[c_241])).

tff(c_337,plain,(
    ~ r2_hidden('#skF_6',k1_setfam_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_335,c_86])).

tff(c_336,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_241])).

tff(c_342,plain,(
    ! [A_79,C_80] :
      ( r2_hidden('#skF_1'(A_79,k1_setfam_1(A_79),C_80),A_79)
      | r2_hidden(C_80,k1_setfam_1(A_79))
      | k1_xboole_0 = A_79 ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_52,plain,(
    ! [D_34] :
      ( ~ r2_hidden('#skF_6','#skF_8')
      | r2_hidden('#skF_6',D_34)
      | ~ r2_hidden(D_34,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_94,plain,(
    ~ r2_hidden('#skF_6','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_54,plain,(
    ! [D_34] :
      ( r2_hidden('#skF_8','#skF_7')
      | r2_hidden('#skF_6',D_34)
      | ~ r2_hidden(D_34,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_95,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_56,plain,(
    ! [D_34] :
      ( r2_hidden('#skF_6',k8_setfam_1('#skF_5','#skF_7'))
      | r2_hidden('#skF_6',D_34)
      | ~ r2_hidden(D_34,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_115,plain,(
    ! [D_47] :
      ( r2_hidden('#skF_6',D_47)
      | ~ r2_hidden(D_47,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_56])).

tff(c_117,plain,(
    r2_hidden('#skF_6','#skF_8') ),
    inference(resolution,[status(thm)],[c_95,c_115])).

tff(c_121,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_117])).

tff(c_122,plain,(
    ! [D_34] :
      ( r2_hidden('#skF_6',D_34)
      | ~ r2_hidden(D_34,'#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_353,plain,(
    ! [C_80] :
      ( r2_hidden('#skF_6','#skF_1'('#skF_7',k1_setfam_1('#skF_7'),C_80))
      | r2_hidden(C_80,k1_setfam_1('#skF_7'))
      | k1_xboole_0 = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_342,c_122])).

tff(c_379,plain,(
    ! [C_81] :
      ( r2_hidden('#skF_6','#skF_1'('#skF_7',k1_setfam_1('#skF_7'),C_81))
      | r2_hidden(C_81,k1_setfam_1('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_336,c_353])).

tff(c_30,plain,(
    ! [C_20,A_8] :
      ( ~ r2_hidden(C_20,'#skF_1'(A_8,k1_setfam_1(A_8),C_20))
      | r2_hidden(C_20,k1_setfam_1(A_8))
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_383,plain,
    ( k1_xboole_0 = '#skF_7'
    | r2_hidden('#skF_6',k1_setfam_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_379,c_30])).

tff(c_391,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_337,c_336,c_337,c_383])).

tff(c_392,plain,(
    ! [D_34] :
      ( r2_hidden('#skF_6',D_34)
      | ~ r2_hidden(D_34,'#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_822,plain,(
    ! [C_134] :
      ( r2_hidden('#skF_6','#skF_1'('#skF_7',k1_setfam_1('#skF_7'),C_134))
      | r2_hidden(C_134,k1_setfam_1('#skF_7'))
      | k1_xboole_0 = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_807,c_392])).

tff(c_849,plain,(
    ! [C_135] :
      ( r2_hidden('#skF_6','#skF_1'('#skF_7',k1_setfam_1('#skF_7'),C_135))
      | r2_hidden(C_135,k1_setfam_1('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_793,c_822])).

tff(c_853,plain,
    ( k1_xboole_0 = '#skF_7'
    | r2_hidden('#skF_6',k1_setfam_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_849,c_30])).

tff(c_861,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_801,c_793,c_801,c_853])).

tff(c_863,plain,(
    r2_hidden('#skF_6',k8_setfam_1('#skF_5','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_46,plain,
    ( ~ r2_hidden('#skF_6','#skF_8')
    | ~ r2_hidden('#skF_6',k8_setfam_1('#skF_5','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_865,plain,(
    ~ r2_hidden('#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_863,c_46])).

tff(c_862,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_939,plain,(
    ! [C_151,D_152,A_153] :
      ( r2_hidden(C_151,D_152)
      | ~ r2_hidden(D_152,A_153)
      | ~ r2_hidden(C_151,k1_setfam_1(A_153))
      | k1_xboole_0 = A_153 ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_950,plain,(
    ! [C_151] :
      ( r2_hidden(C_151,'#skF_8')
      | ~ r2_hidden(C_151,k1_setfam_1('#skF_7'))
      | k1_xboole_0 = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_862,c_939])).

tff(c_952,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_950])).

tff(c_2,plain,(
    ! [A_1] : k4_xboole_0(k1_xboole_0,A_1) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_81,plain,(
    ! [C_38,B_39] : ~ r2_hidden(C_38,k4_xboole_0(B_39,k1_tarski(C_38))) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_84,plain,(
    ! [C_38] : ~ r2_hidden(C_38,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_81])).

tff(c_955,plain,(
    ! [C_38] : ~ r2_hidden(C_38,'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_952,c_84])).

tff(c_973,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_955,c_862])).

tff(c_975,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_950])).

tff(c_897,plain,(
    ! [A_145,B_146] :
      ( k6_setfam_1(A_145,B_146) = k1_setfam_1(B_146)
      | ~ m1_subset_1(B_146,k1_zfmisc_1(k1_zfmisc_1(A_145))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_905,plain,(
    k6_setfam_1('#skF_5','#skF_7') = k1_setfam_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_44,c_897])).

tff(c_1038,plain,(
    ! [A_162,B_163] :
      ( k8_setfam_1(A_162,B_163) = k6_setfam_1(A_162,B_163)
      | k1_xboole_0 = B_163
      | ~ m1_subset_1(B_163,k1_zfmisc_1(k1_zfmisc_1(A_162))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1041,plain,
    ( k8_setfam_1('#skF_5','#skF_7') = k6_setfam_1('#skF_5','#skF_7')
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_44,c_1038])).

tff(c_1047,plain,
    ( k8_setfam_1('#skF_5','#skF_7') = k1_setfam_1('#skF_7')
    | k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_905,c_1041])).

tff(c_1048,plain,(
    k8_setfam_1('#skF_5','#skF_7') = k1_setfam_1('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_975,c_1047])).

tff(c_1053,plain,(
    r2_hidden('#skF_6',k1_setfam_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1048,c_863])).

tff(c_974,plain,(
    ! [C_151] :
      ( r2_hidden(C_151,'#skF_8')
      | ~ r2_hidden(C_151,k1_setfam_1('#skF_7')) ) ),
    inference(splitRight,[status(thm)],[c_950])).

tff(c_1060,plain,(
    r2_hidden('#skF_6','#skF_8') ),
    inference(resolution,[status(thm)],[c_1053,c_974])).

tff(c_1068,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_865,c_1060])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:06:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.05/1.53  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.05/1.54  
% 3.05/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.05/1.54  %$ r2_hidden > m1_subset_1 > k8_setfam_1 > k6_setfam_1 > k4_xboole_0 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_4
% 3.05/1.54  
% 3.05/1.54  %Foreground sorts:
% 3.05/1.54  
% 3.05/1.54  
% 3.05/1.54  %Background operators:
% 3.05/1.54  
% 3.05/1.54  
% 3.05/1.54  %Foreground operators:
% 3.05/1.54  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.05/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.05/1.54  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.05/1.54  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.05/1.54  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.05/1.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.05/1.54  tff(k8_setfam_1, type, k8_setfam_1: ($i * $i) > $i).
% 3.05/1.54  tff('#skF_7', type, '#skF_7': $i).
% 3.05/1.54  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.05/1.54  tff('#skF_5', type, '#skF_5': $i).
% 3.05/1.54  tff('#skF_6', type, '#skF_6': $i).
% 3.05/1.54  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.05/1.54  tff('#skF_8', type, '#skF_8': $i).
% 3.05/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.05/1.54  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 3.05/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.05/1.54  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.05/1.54  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.05/1.54  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.05/1.54  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.05/1.54  
% 3.05/1.56  tff(f_88, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => (r2_hidden(B, A) => (r2_hidden(B, k8_setfam_1(A, C)) <=> (![D]: (r2_hidden(D, C) => r2_hidden(B, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_setfam_1)).
% 3.05/1.56  tff(f_70, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k6_setfam_1(A, B) = k1_setfam_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_setfam_1)).
% 3.05/1.56  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ((~(B = k1_xboole_0) => (k8_setfam_1(A, B) = k6_setfam_1(A, B))) & ((B = k1_xboole_0) => (k8_setfam_1(A, B) = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_setfam_1)).
% 3.05/1.56  tff(f_36, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 3.05/1.56  tff(f_66, axiom, (![A, B]: ((~(A = k1_xboole_0) => ((B = k1_setfam_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (![D]: (r2_hidden(D, A) => r2_hidden(C, D))))))) & ((A = k1_xboole_0) => ((B = k1_setfam_1(A)) <=> (B = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_setfam_1)).
% 3.05/1.56  tff(f_27, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 3.05/1.56  tff(f_34, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 3.05/1.56  tff(c_42, plain, (r2_hidden('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.05/1.56  tff(c_44, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k1_zfmisc_1('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.05/1.56  tff(c_627, plain, (![A_109, B_110]: (k6_setfam_1(A_109, B_110)=k1_setfam_1(B_110) | ~m1_subset_1(B_110, k1_zfmisc_1(k1_zfmisc_1(A_109))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.05/1.56  tff(c_635, plain, (k6_setfam_1('#skF_5', '#skF_7')=k1_setfam_1('#skF_7')), inference(resolution, [status(thm)], [c_44, c_627])).
% 3.05/1.56  tff(c_750, plain, (![A_127, B_128]: (k8_setfam_1(A_127, B_128)=k6_setfam_1(A_127, B_128) | k1_xboole_0=B_128 | ~m1_subset_1(B_128, k1_zfmisc_1(k1_zfmisc_1(A_127))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.05/1.56  tff(c_753, plain, (k8_setfam_1('#skF_5', '#skF_7')=k6_setfam_1('#skF_5', '#skF_7') | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_44, c_750])).
% 3.05/1.56  tff(c_759, plain, (k8_setfam_1('#skF_5', '#skF_7')=k1_setfam_1('#skF_7') | k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_635, c_753])).
% 3.05/1.56  tff(c_763, plain, (k1_xboole_0='#skF_7'), inference(splitLeft, [status(thm)], [c_759])).
% 3.05/1.56  tff(c_10, plain, (![A_5]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.05/1.56  tff(c_12, plain, (![A_6]: (k8_setfam_1(A_6, k1_xboole_0)=A_6 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_6))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.05/1.56  tff(c_59, plain, (![A_6]: (k8_setfam_1(A_6, k1_xboole_0)=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_12])).
% 3.05/1.56  tff(c_771, plain, (![A_6]: (k8_setfam_1(A_6, '#skF_7')=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_763, c_59])).
% 3.05/1.56  tff(c_48, plain, (r2_hidden('#skF_8', '#skF_7') | ~r2_hidden('#skF_6', k8_setfam_1('#skF_5', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.05/1.56  tff(c_86, plain, (~r2_hidden('#skF_6', k8_setfam_1('#skF_5', '#skF_7'))), inference(splitLeft, [status(thm)], [c_48])).
% 3.05/1.56  tff(c_788, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_771, c_86])).
% 3.05/1.56  tff(c_791, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_788])).
% 3.05/1.56  tff(c_792, plain, (k8_setfam_1('#skF_5', '#skF_7')=k1_setfam_1('#skF_7')), inference(splitRight, [status(thm)], [c_759])).
% 3.05/1.56  tff(c_801, plain, (~r2_hidden('#skF_6', k1_setfam_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_792, c_86])).
% 3.05/1.56  tff(c_793, plain, (k1_xboole_0!='#skF_7'), inference(splitRight, [status(thm)], [c_759])).
% 3.05/1.56  tff(c_807, plain, (![A_133, C_134]: (r2_hidden('#skF_1'(A_133, k1_setfam_1(A_133), C_134), A_133) | r2_hidden(C_134, k1_setfam_1(A_133)) | k1_xboole_0=A_133)), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.05/1.56  tff(c_125, plain, (![A_49, B_50]: (k6_setfam_1(A_49, B_50)=k1_setfam_1(B_50) | ~m1_subset_1(B_50, k1_zfmisc_1(k1_zfmisc_1(A_49))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.05/1.56  tff(c_133, plain, (k6_setfam_1('#skF_5', '#skF_7')=k1_setfam_1('#skF_7')), inference(resolution, [status(thm)], [c_44, c_125])).
% 3.05/1.56  tff(c_232, plain, (![A_72, B_73]: (k8_setfam_1(A_72, B_73)=k6_setfam_1(A_72, B_73) | k1_xboole_0=B_73 | ~m1_subset_1(B_73, k1_zfmisc_1(k1_zfmisc_1(A_72))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.05/1.56  tff(c_235, plain, (k8_setfam_1('#skF_5', '#skF_7')=k6_setfam_1('#skF_5', '#skF_7') | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_44, c_232])).
% 3.05/1.56  tff(c_241, plain, (k8_setfam_1('#skF_5', '#skF_7')=k1_setfam_1('#skF_7') | k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_133, c_235])).
% 3.05/1.56  tff(c_245, plain, (k1_xboole_0='#skF_7'), inference(splitLeft, [status(thm)], [c_241])).
% 3.05/1.56  tff(c_253, plain, (![A_6]: (k8_setfam_1(A_6, '#skF_7')=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_245, c_59])).
% 3.05/1.56  tff(c_331, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_253, c_86])).
% 3.05/1.56  tff(c_334, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_331])).
% 3.05/1.56  tff(c_335, plain, (k8_setfam_1('#skF_5', '#skF_7')=k1_setfam_1('#skF_7')), inference(splitRight, [status(thm)], [c_241])).
% 3.05/1.56  tff(c_337, plain, (~r2_hidden('#skF_6', k1_setfam_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_335, c_86])).
% 3.05/1.56  tff(c_336, plain, (k1_xboole_0!='#skF_7'), inference(splitRight, [status(thm)], [c_241])).
% 3.05/1.56  tff(c_342, plain, (![A_79, C_80]: (r2_hidden('#skF_1'(A_79, k1_setfam_1(A_79), C_80), A_79) | r2_hidden(C_80, k1_setfam_1(A_79)) | k1_xboole_0=A_79)), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.05/1.56  tff(c_52, plain, (![D_34]: (~r2_hidden('#skF_6', '#skF_8') | r2_hidden('#skF_6', D_34) | ~r2_hidden(D_34, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.05/1.56  tff(c_94, plain, (~r2_hidden('#skF_6', '#skF_8')), inference(splitLeft, [status(thm)], [c_52])).
% 3.05/1.56  tff(c_54, plain, (![D_34]: (r2_hidden('#skF_8', '#skF_7') | r2_hidden('#skF_6', D_34) | ~r2_hidden(D_34, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.05/1.56  tff(c_95, plain, (r2_hidden('#skF_8', '#skF_7')), inference(splitLeft, [status(thm)], [c_54])).
% 3.05/1.56  tff(c_56, plain, (![D_34]: (r2_hidden('#skF_6', k8_setfam_1('#skF_5', '#skF_7')) | r2_hidden('#skF_6', D_34) | ~r2_hidden(D_34, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.05/1.56  tff(c_115, plain, (![D_47]: (r2_hidden('#skF_6', D_47) | ~r2_hidden(D_47, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_86, c_56])).
% 3.05/1.56  tff(c_117, plain, (r2_hidden('#skF_6', '#skF_8')), inference(resolution, [status(thm)], [c_95, c_115])).
% 3.05/1.56  tff(c_121, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_117])).
% 3.05/1.56  tff(c_122, plain, (![D_34]: (r2_hidden('#skF_6', D_34) | ~r2_hidden(D_34, '#skF_7'))), inference(splitRight, [status(thm)], [c_54])).
% 3.05/1.56  tff(c_353, plain, (![C_80]: (r2_hidden('#skF_6', '#skF_1'('#skF_7', k1_setfam_1('#skF_7'), C_80)) | r2_hidden(C_80, k1_setfam_1('#skF_7')) | k1_xboole_0='#skF_7')), inference(resolution, [status(thm)], [c_342, c_122])).
% 3.05/1.56  tff(c_379, plain, (![C_81]: (r2_hidden('#skF_6', '#skF_1'('#skF_7', k1_setfam_1('#skF_7'), C_81)) | r2_hidden(C_81, k1_setfam_1('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_336, c_353])).
% 3.05/1.56  tff(c_30, plain, (![C_20, A_8]: (~r2_hidden(C_20, '#skF_1'(A_8, k1_setfam_1(A_8), C_20)) | r2_hidden(C_20, k1_setfam_1(A_8)) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.05/1.56  tff(c_383, plain, (k1_xboole_0='#skF_7' | r2_hidden('#skF_6', k1_setfam_1('#skF_7'))), inference(resolution, [status(thm)], [c_379, c_30])).
% 3.05/1.56  tff(c_391, plain, $false, inference(negUnitSimplification, [status(thm)], [c_337, c_336, c_337, c_383])).
% 3.05/1.56  tff(c_392, plain, (![D_34]: (r2_hidden('#skF_6', D_34) | ~r2_hidden(D_34, '#skF_7'))), inference(splitRight, [status(thm)], [c_52])).
% 3.05/1.56  tff(c_822, plain, (![C_134]: (r2_hidden('#skF_6', '#skF_1'('#skF_7', k1_setfam_1('#skF_7'), C_134)) | r2_hidden(C_134, k1_setfam_1('#skF_7')) | k1_xboole_0='#skF_7')), inference(resolution, [status(thm)], [c_807, c_392])).
% 3.05/1.56  tff(c_849, plain, (![C_135]: (r2_hidden('#skF_6', '#skF_1'('#skF_7', k1_setfam_1('#skF_7'), C_135)) | r2_hidden(C_135, k1_setfam_1('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_793, c_822])).
% 3.05/1.56  tff(c_853, plain, (k1_xboole_0='#skF_7' | r2_hidden('#skF_6', k1_setfam_1('#skF_7'))), inference(resolution, [status(thm)], [c_849, c_30])).
% 3.05/1.56  tff(c_861, plain, $false, inference(negUnitSimplification, [status(thm)], [c_801, c_793, c_801, c_853])).
% 3.05/1.56  tff(c_863, plain, (r2_hidden('#skF_6', k8_setfam_1('#skF_5', '#skF_7'))), inference(splitRight, [status(thm)], [c_48])).
% 3.05/1.56  tff(c_46, plain, (~r2_hidden('#skF_6', '#skF_8') | ~r2_hidden('#skF_6', k8_setfam_1('#skF_5', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.05/1.56  tff(c_865, plain, (~r2_hidden('#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_863, c_46])).
% 3.05/1.56  tff(c_862, plain, (r2_hidden('#skF_8', '#skF_7')), inference(splitRight, [status(thm)], [c_48])).
% 3.05/1.56  tff(c_939, plain, (![C_151, D_152, A_153]: (r2_hidden(C_151, D_152) | ~r2_hidden(D_152, A_153) | ~r2_hidden(C_151, k1_setfam_1(A_153)) | k1_xboole_0=A_153)), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.05/1.56  tff(c_950, plain, (![C_151]: (r2_hidden(C_151, '#skF_8') | ~r2_hidden(C_151, k1_setfam_1('#skF_7')) | k1_xboole_0='#skF_7')), inference(resolution, [status(thm)], [c_862, c_939])).
% 3.05/1.56  tff(c_952, plain, (k1_xboole_0='#skF_7'), inference(splitLeft, [status(thm)], [c_950])).
% 3.05/1.56  tff(c_2, plain, (![A_1]: (k4_xboole_0(k1_xboole_0, A_1)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.05/1.56  tff(c_81, plain, (![C_38, B_39]: (~r2_hidden(C_38, k4_xboole_0(B_39, k1_tarski(C_38))))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.05/1.56  tff(c_84, plain, (![C_38]: (~r2_hidden(C_38, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2, c_81])).
% 3.05/1.56  tff(c_955, plain, (![C_38]: (~r2_hidden(C_38, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_952, c_84])).
% 3.05/1.56  tff(c_973, plain, $false, inference(negUnitSimplification, [status(thm)], [c_955, c_862])).
% 3.05/1.56  tff(c_975, plain, (k1_xboole_0!='#skF_7'), inference(splitRight, [status(thm)], [c_950])).
% 3.05/1.56  tff(c_897, plain, (![A_145, B_146]: (k6_setfam_1(A_145, B_146)=k1_setfam_1(B_146) | ~m1_subset_1(B_146, k1_zfmisc_1(k1_zfmisc_1(A_145))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.05/1.56  tff(c_905, plain, (k6_setfam_1('#skF_5', '#skF_7')=k1_setfam_1('#skF_7')), inference(resolution, [status(thm)], [c_44, c_897])).
% 3.05/1.56  tff(c_1038, plain, (![A_162, B_163]: (k8_setfam_1(A_162, B_163)=k6_setfam_1(A_162, B_163) | k1_xboole_0=B_163 | ~m1_subset_1(B_163, k1_zfmisc_1(k1_zfmisc_1(A_162))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.05/1.56  tff(c_1041, plain, (k8_setfam_1('#skF_5', '#skF_7')=k6_setfam_1('#skF_5', '#skF_7') | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_44, c_1038])).
% 3.05/1.56  tff(c_1047, plain, (k8_setfam_1('#skF_5', '#skF_7')=k1_setfam_1('#skF_7') | k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_905, c_1041])).
% 3.05/1.56  tff(c_1048, plain, (k8_setfam_1('#skF_5', '#skF_7')=k1_setfam_1('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_975, c_1047])).
% 3.05/1.56  tff(c_1053, plain, (r2_hidden('#skF_6', k1_setfam_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_1048, c_863])).
% 3.05/1.56  tff(c_974, plain, (![C_151]: (r2_hidden(C_151, '#skF_8') | ~r2_hidden(C_151, k1_setfam_1('#skF_7')))), inference(splitRight, [status(thm)], [c_950])).
% 3.05/1.56  tff(c_1060, plain, (r2_hidden('#skF_6', '#skF_8')), inference(resolution, [status(thm)], [c_1053, c_974])).
% 3.05/1.56  tff(c_1068, plain, $false, inference(negUnitSimplification, [status(thm)], [c_865, c_1060])).
% 3.05/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.05/1.56  
% 3.05/1.56  Inference rules
% 3.05/1.56  ----------------------
% 3.05/1.56  #Ref     : 0
% 3.05/1.56  #Sup     : 202
% 3.05/1.56  #Fact    : 0
% 3.05/1.56  #Define  : 0
% 3.05/1.56  #Split   : 21
% 3.05/1.56  #Chain   : 0
% 3.05/1.56  #Close   : 0
% 3.05/1.56  
% 3.05/1.56  Ordering : KBO
% 3.05/1.56  
% 3.05/1.56  Simplification rules
% 3.05/1.56  ----------------------
% 3.05/1.56  #Subsume      : 42
% 3.05/1.56  #Demod        : 174
% 3.05/1.56  #Tautology    : 102
% 3.05/1.56  #SimpNegUnit  : 43
% 3.05/1.56  #BackRed      : 103
% 3.05/1.56  
% 3.05/1.56  #Partial instantiations: 0
% 3.05/1.56  #Strategies tried      : 1
% 3.05/1.56  
% 3.05/1.56  Timing (in seconds)
% 3.05/1.56  ----------------------
% 3.05/1.56  Preprocessing        : 0.34
% 3.05/1.56  Parsing              : 0.17
% 3.05/1.56  CNF conversion       : 0.03
% 3.05/1.56  Main loop            : 0.40
% 3.05/1.56  Inferencing          : 0.13
% 3.05/1.56  Reduction            : 0.13
% 3.05/1.57  Demodulation         : 0.08
% 3.05/1.57  BG Simplification    : 0.02
% 3.05/1.57  Subsumption          : 0.08
% 3.05/1.57  Abstraction          : 0.02
% 3.05/1.57  MUC search           : 0.00
% 3.05/1.57  Cooper               : 0.00
% 3.05/1.57  Total                : 0.78
% 3.05/1.57  Index Insertion      : 0.00
% 3.05/1.57  Index Deletion       : 0.00
% 3.05/1.57  Index Matching       : 0.00
% 3.05/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
