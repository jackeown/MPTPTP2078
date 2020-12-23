%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:42 EST 2020

% Result     : Theorem 6.34s
% Output     : CNFRefutation 6.77s
% Verified   : 
% Statistics : Number of formulae       :  160 ( 822 expanded)
%              Number of leaves         :   30 ( 257 expanded)
%              Depth                    :   11
%              Number of atoms          :  208 (1580 expanded)
%              Number of equality atoms :  117 (1314 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_11 > #skF_4 > #skF_14 > #skF_13 > #skF_2 > #skF_6 > #skF_8 > #skF_5 > #skF_3 > #skF_7 > #skF_9 > #skF_12 > #skF_10

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_14',type,(
    '#skF_14': $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i * $i ) > $i )).

tff(f_51,axiom,(
    ! [A,B] :
      ( B = k3_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] :
              ( r2_hidden(C,D)
              & r2_hidden(D,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

tff(f_63,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_zfmisc_1(A,B) = k1_xboole_0
      <=> ( A = k1_xboole_0
          | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_27,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_56,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(c_4135,plain,(
    ! [A_400,B_401] :
      ( r2_hidden('#skF_8'(A_400,B_401),A_400)
      | r2_hidden('#skF_9'(A_400,B_401),B_401)
      | k3_tarski(A_400) = B_401 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_3740,plain,(
    ! [A_354,B_355] :
      ( r2_hidden('#skF_8'(A_354,B_355),A_354)
      | r2_hidden('#skF_9'(A_354,B_355),B_355)
      | k3_tarski(A_354) = B_355 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_3144,plain,(
    ! [A_309,B_310] :
      ( r2_hidden('#skF_8'(A_309,B_310),A_309)
      | r2_hidden('#skF_9'(A_309,B_310),B_310)
      | k3_tarski(A_309) = B_310 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_54,plain,
    ( k1_xboole_0 = '#skF_12'
    | k1_xboole_0 = '#skF_11'
    | k1_xboole_0 != '#skF_14' ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_80,plain,(
    k1_xboole_0 != '#skF_14' ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_517,plain,(
    ! [A_101,B_102] :
      ( r2_hidden('#skF_8'(A_101,B_102),A_101)
      | r2_hidden('#skF_9'(A_101,B_102),B_102)
      | k3_tarski(A_101) = B_102 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2,plain,(
    ! [A_1] : k4_xboole_0(k1_xboole_0,A_1) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_106,plain,(
    ! [B_62,A_63] :
      ( ~ r2_hidden(B_62,A_63)
      | k4_xboole_0(A_63,k1_tarski(B_62)) != A_63 ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_115,plain,(
    ! [B_62] : ~ r2_hidden(B_62,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_106])).

tff(c_648,plain,(
    ! [B_103] :
      ( r2_hidden('#skF_9'(k1_xboole_0,B_103),B_103)
      | k3_tarski(k1_xboole_0) = B_103 ) ),
    inference(resolution,[status(thm)],[c_517,c_115])).

tff(c_56,plain,
    ( k2_zfmisc_1('#skF_11','#skF_12') != k1_xboole_0
    | k1_xboole_0 != '#skF_13' ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_79,plain,(
    k1_xboole_0 != '#skF_13' ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_225,plain,(
    ! [A_92,B_93] :
      ( r2_hidden('#skF_8'(A_92,B_93),A_92)
      | r2_hidden('#skF_9'(A_92,B_93),B_93)
      | k3_tarski(A_92) = B_93 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_376,plain,(
    ! [B_94] :
      ( r2_hidden('#skF_9'(k1_xboole_0,B_94),B_94)
      | k3_tarski(k1_xboole_0) = B_94 ) ),
    inference(resolution,[status(thm)],[c_225,c_115])).

tff(c_62,plain,
    ( k1_xboole_0 = '#skF_12'
    | k1_xboole_0 = '#skF_11'
    | k2_zfmisc_1('#skF_13','#skF_14') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_81,plain,(
    k2_zfmisc_1('#skF_13','#skF_14') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_168,plain,(
    ! [E_80,F_81,A_82,B_83] :
      ( r2_hidden(k4_tarski(E_80,F_81),k2_zfmisc_1(A_82,B_83))
      | ~ r2_hidden(F_81,B_83)
      | ~ r2_hidden(E_80,A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_173,plain,(
    ! [E_80,F_81] :
      ( r2_hidden(k4_tarski(E_80,F_81),k1_xboole_0)
      | ~ r2_hidden(F_81,'#skF_14')
      | ~ r2_hidden(E_80,'#skF_13') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_168])).

tff(c_175,plain,(
    ! [F_81,E_80] :
      ( ~ r2_hidden(F_81,'#skF_14')
      | ~ r2_hidden(E_80,'#skF_13') ) ),
    inference(negUnitSimplification,[status(thm)],[c_115,c_173])).

tff(c_176,plain,(
    ! [E_80] : ~ r2_hidden(E_80,'#skF_13') ),
    inference(splitLeft,[status(thm)],[c_175])).

tff(c_446,plain,(
    k3_tarski(k1_xboole_0) = '#skF_13' ),
    inference(resolution,[status(thm)],[c_376,c_176])).

tff(c_455,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_376,c_115])).

tff(c_477,plain,(
    k1_xboole_0 = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_446,c_455])).

tff(c_479,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_477])).

tff(c_480,plain,(
    ! [F_81] : ~ r2_hidden(F_81,'#skF_14') ),
    inference(splitRight,[status(thm)],[c_175])).

tff(c_708,plain,(
    k3_tarski(k1_xboole_0) = '#skF_14' ),
    inference(resolution,[status(thm)],[c_648,c_480])).

tff(c_717,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_648,c_115])).

tff(c_738,plain,(
    k1_xboole_0 = '#skF_14' ),
    inference(demodulation,[status(thm),theory(equality)],[c_708,c_717])).

tff(c_740,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_738])).

tff(c_741,plain,
    ( k1_xboole_0 = '#skF_11'
    | k1_xboole_0 = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_2391,plain,(
    k1_xboole_0 = '#skF_12' ),
    inference(splitLeft,[status(thm)],[c_741])).

tff(c_742,plain,(
    k2_zfmisc_1('#skF_13','#skF_14') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_2406,plain,(
    k2_zfmisc_1('#skF_13','#skF_14') != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2391,c_742])).

tff(c_1209,plain,(
    ! [A_171,B_172] :
      ( r2_hidden('#skF_8'(A_171,B_172),A_171)
      | r2_hidden('#skF_9'(A_171,B_172),B_172)
      | k3_tarski(A_171) = B_172 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_811,plain,(
    ! [A_118,B_119] :
      ( r2_hidden('#skF_8'(A_118,B_119),A_118)
      | r2_hidden('#skF_9'(A_118,B_119),B_119)
      | k3_tarski(A_118) = B_119 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_744,plain,(
    k1_xboole_0 = '#skF_12' ),
    inference(splitLeft,[status(thm)],[c_741])).

tff(c_748,plain,(
    ! [A_1] : k4_xboole_0('#skF_12',A_1) = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_744,c_744,c_2])).

tff(c_761,plain,(
    ! [B_105,A_106] :
      ( ~ r2_hidden(B_105,A_106)
      | k4_xboole_0(A_106,k1_tarski(B_105)) != A_106 ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_766,plain,(
    ! [B_105] : ~ r2_hidden(B_105,'#skF_12') ),
    inference(superposition,[status(thm),theory(equality)],[c_748,c_761])).

tff(c_884,plain,(
    ! [B_125] :
      ( r2_hidden('#skF_9'('#skF_12',B_125),B_125)
      | k3_tarski('#skF_12') = B_125 ) ),
    inference(resolution,[status(thm)],[c_811,c_766])).

tff(c_913,plain,(
    k3_tarski('#skF_12') = '#skF_12' ),
    inference(resolution,[status(thm)],[c_884,c_766])).

tff(c_832,plain,(
    ! [B_119] :
      ( r2_hidden('#skF_9'('#skF_12',B_119),B_119)
      | k3_tarski('#skF_12') = B_119 ) ),
    inference(resolution,[status(thm)],[c_811,c_766])).

tff(c_914,plain,(
    ! [B_119] :
      ( r2_hidden('#skF_9'('#skF_12',B_119),B_119)
      | B_119 = '#skF_12' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_913,c_832])).

tff(c_1026,plain,(
    ! [A_138,B_139,D_140] :
      ( r2_hidden('#skF_6'(A_138,B_139,k2_zfmisc_1(A_138,B_139),D_140),B_139)
      | ~ r2_hidden(D_140,k2_zfmisc_1(A_138,B_139)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1039,plain,(
    ! [D_141,A_142] : ~ r2_hidden(D_141,k2_zfmisc_1(A_142,'#skF_12')) ),
    inference(resolution,[status(thm)],[c_1026,c_766])).

tff(c_1079,plain,(
    ! [A_142] : k2_zfmisc_1(A_142,'#skF_12') = '#skF_12' ),
    inference(resolution,[status(thm)],[c_914,c_1039])).

tff(c_60,plain,
    ( k2_zfmisc_1('#skF_11','#skF_12') != k1_xboole_0
    | k2_zfmisc_1('#skF_13','#skF_14') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_743,plain,(
    k2_zfmisc_1('#skF_11','#skF_12') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_745,plain,(
    k2_zfmisc_1('#skF_11','#skF_12') != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_744,c_743])).

tff(c_1086,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1079,c_745])).

tff(c_1087,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(splitRight,[status(thm)],[c_741])).

tff(c_1094,plain,(
    ! [A_1] : k4_xboole_0('#skF_11',A_1) = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1087,c_1087,c_2])).

tff(c_1125,plain,(
    ! [B_146,A_147] :
      ( ~ r2_hidden(B_146,A_147)
      | k4_xboole_0(A_147,k1_tarski(B_146)) != A_147 ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1134,plain,(
    ! [B_146] : ~ r2_hidden(B_146,'#skF_11') ),
    inference(superposition,[status(thm),theory(equality)],[c_1094,c_1125])).

tff(c_2156,plain,(
    ! [B_223] :
      ( r2_hidden('#skF_9'('#skF_11',B_223),B_223)
      | k3_tarski('#skF_11') = B_223 ) ),
    inference(resolution,[status(thm)],[c_1209,c_1134])).

tff(c_2289,plain,(
    k3_tarski('#skF_11') = '#skF_11' ),
    inference(resolution,[status(thm)],[c_2156,c_1134])).

tff(c_1440,plain,(
    ! [A_182,B_183,D_184] :
      ( r2_hidden('#skF_5'(A_182,B_183,k2_zfmisc_1(A_182,B_183),D_184),A_182)
      | ~ r2_hidden(D_184,k2_zfmisc_1(A_182,B_183)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1507,plain,(
    ! [D_184,B_183] : ~ r2_hidden(D_184,k2_zfmisc_1('#skF_11',B_183)) ),
    inference(resolution,[status(thm)],[c_1440,c_1134])).

tff(c_2275,plain,(
    ! [B_183] : k2_zfmisc_1('#skF_11',B_183) = k3_tarski('#skF_11') ),
    inference(resolution,[status(thm)],[c_2156,c_1507])).

tff(c_2377,plain,(
    ! [B_183] : k2_zfmisc_1('#skF_11',B_183) = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2289,c_2275])).

tff(c_1091,plain,(
    k2_zfmisc_1('#skF_11','#skF_12') != '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1087,c_743])).

tff(c_2388,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2377,c_1091])).

tff(c_2389,plain,(
    k2_zfmisc_1('#skF_13','#skF_14') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_2412,plain,(
    k2_zfmisc_1('#skF_13','#skF_14') = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2391,c_2389])).

tff(c_2413,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2406,c_2412])).

tff(c_2414,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(splitRight,[status(thm)],[c_741])).

tff(c_2420,plain,(
    k2_zfmisc_1('#skF_13','#skF_14') = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2414,c_2389])).

tff(c_2446,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2420,c_2414,c_742])).

tff(c_2448,plain,(
    k1_xboole_0 = '#skF_14' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_2450,plain,(
    ! [A_1] : k4_xboole_0('#skF_14',A_1) = '#skF_14' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2448,c_2448,c_2])).

tff(c_3060,plain,(
    ! [B_284,A_285] :
      ( ~ r2_hidden(B_284,A_285)
      | k4_xboole_0(A_285,k1_tarski(B_284)) != A_285 ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_3069,plain,(
    ! [B_284] : ~ r2_hidden(B_284,'#skF_14') ),
    inference(superposition,[status(thm),theory(equality)],[c_2450,c_3060])).

tff(c_3248,plain,(
    ! [B_311] :
      ( r2_hidden('#skF_9'('#skF_14',B_311),B_311)
      | k3_tarski('#skF_14') = B_311 ) ),
    inference(resolution,[status(thm)],[c_3144,c_3069])).

tff(c_3302,plain,(
    k3_tarski('#skF_14') = '#skF_14' ),
    inference(resolution,[status(thm)],[c_3248,c_3069])).

tff(c_3237,plain,(
    ! [B_310] :
      ( r2_hidden('#skF_9'('#skF_14',B_310),B_310)
      | k3_tarski('#skF_14') = B_310 ) ),
    inference(resolution,[status(thm)],[c_3144,c_3069])).

tff(c_3541,plain,(
    ! [B_331] :
      ( r2_hidden('#skF_9'('#skF_14',B_331),B_331)
      | B_331 = '#skF_14' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3302,c_3237])).

tff(c_3303,plain,(
    ! [A_312,B_313,D_314] :
      ( r2_hidden('#skF_5'(A_312,B_313,k2_zfmisc_1(A_312,B_313),D_314),A_312)
      | ~ r2_hidden(D_314,k2_zfmisc_1(A_312,B_313)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_3356,plain,(
    ! [D_314,B_313] : ~ r2_hidden(D_314,k2_zfmisc_1('#skF_14',B_313)) ),
    inference(resolution,[status(thm)],[c_3303,c_3069])).

tff(c_3572,plain,(
    ! [B_313] : k2_zfmisc_1('#skF_14',B_313) = '#skF_14' ),
    inference(resolution,[status(thm)],[c_3541,c_3356])).

tff(c_2584,plain,(
    ! [A_258,B_259] :
      ( r2_hidden('#skF_8'(A_258,B_259),A_258)
      | r2_hidden('#skF_9'(A_258,B_259),B_259)
      | k3_tarski(A_258) = B_259 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2447,plain,
    ( k1_xboole_0 = '#skF_11'
    | k1_xboole_0 = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_2457,plain,
    ( '#skF_11' = '#skF_14'
    | '#skF_14' = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2448,c_2448,c_2447])).

tff(c_2458,plain,(
    '#skF_14' = '#skF_12' ),
    inference(splitLeft,[status(thm)],[c_2457])).

tff(c_2470,plain,(
    ! [A_1] : k4_xboole_0('#skF_12',A_1) = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2458,c_2458,c_2450])).

tff(c_2500,plain,(
    ! [B_233,A_234] :
      ( ~ r2_hidden(B_233,A_234)
      | k4_xboole_0(A_234,k1_tarski(B_233)) != A_234 ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2509,plain,(
    ! [B_233] : ~ r2_hidden(B_233,'#skF_12') ),
    inference(superposition,[status(thm),theory(equality)],[c_2470,c_2500])).

tff(c_2688,plain,(
    ! [B_260] :
      ( r2_hidden('#skF_9'('#skF_12',B_260),B_260)
      | k3_tarski('#skF_12') = B_260 ) ),
    inference(resolution,[status(thm)],[c_2584,c_2509])).

tff(c_2742,plain,(
    k3_tarski('#skF_12') = '#skF_12' ),
    inference(resolution,[status(thm)],[c_2688,c_2509])).

tff(c_2677,plain,(
    ! [B_259] :
      ( r2_hidden('#skF_9'('#skF_12',B_259),B_259)
      | k3_tarski('#skF_12') = B_259 ) ),
    inference(resolution,[status(thm)],[c_2584,c_2509])).

tff(c_2981,plain,(
    ! [B_280] :
      ( r2_hidden('#skF_9'('#skF_12',B_280),B_280)
      | B_280 = '#skF_12' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2742,c_2677])).

tff(c_2869,plain,(
    ! [A_268,B_269,D_270] :
      ( r2_hidden('#skF_6'(A_268,B_269,k2_zfmisc_1(A_268,B_269),D_270),B_269)
      | ~ r2_hidden(D_270,k2_zfmisc_1(A_268,B_269)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2887,plain,(
    ! [D_270,A_268] : ~ r2_hidden(D_270,k2_zfmisc_1(A_268,'#skF_12')) ),
    inference(resolution,[status(thm)],[c_2869,c_2509])).

tff(c_3010,plain,(
    ! [A_268] : k2_zfmisc_1(A_268,'#skF_12') = '#skF_12' ),
    inference(resolution,[status(thm)],[c_2981,c_2887])).

tff(c_52,plain,
    ( k2_zfmisc_1('#skF_11','#skF_12') != k1_xboole_0
    | k1_xboole_0 != '#skF_14' ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2456,plain,(
    k2_zfmisc_1('#skF_11','#skF_12') != '#skF_14' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2448,c_2448,c_52])).

tff(c_2460,plain,(
    k2_zfmisc_1('#skF_11','#skF_12') != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2458,c_2456])).

tff(c_3021,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3010,c_2460])).

tff(c_3022,plain,(
    '#skF_11' = '#skF_14' ),
    inference(splitRight,[status(thm)],[c_2457])).

tff(c_3024,plain,(
    k2_zfmisc_1('#skF_14','#skF_12') != '#skF_14' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3022,c_2456])).

tff(c_3617,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3572,c_3024])).

tff(c_3619,plain,(
    k1_xboole_0 = '#skF_13' ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_3620,plain,(
    ! [A_1] : k4_xboole_0('#skF_13',A_1) = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3619,c_3619,c_2])).

tff(c_3644,plain,(
    ! [B_334,A_335] :
      ( ~ r2_hidden(B_334,A_335)
      | k4_xboole_0(A_335,k1_tarski(B_334)) != A_335 ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_3649,plain,(
    ! [B_334] : ~ r2_hidden(B_334,'#skF_13') ),
    inference(superposition,[status(thm),theory(equality)],[c_3620,c_3644])).

tff(c_3834,plain,(
    ! [B_356] :
      ( r2_hidden('#skF_9'('#skF_13',B_356),B_356)
      | k3_tarski('#skF_13') = B_356 ) ),
    inference(resolution,[status(thm)],[c_3740,c_3649])).

tff(c_3883,plain,(
    k3_tarski('#skF_13') = '#skF_13' ),
    inference(resolution,[status(thm)],[c_3834,c_3649])).

tff(c_3824,plain,(
    ! [B_355] :
      ( r2_hidden('#skF_9'('#skF_13',B_355),B_355)
      | k3_tarski('#skF_13') = B_355 ) ),
    inference(resolution,[status(thm)],[c_3740,c_3649])).

tff(c_3884,plain,(
    ! [B_355] :
      ( r2_hidden('#skF_9'('#skF_13',B_355),B_355)
      | B_355 = '#skF_13' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3883,c_3824])).

tff(c_3954,plain,(
    ! [A_367,B_368,D_369] :
      ( r2_hidden('#skF_5'(A_367,B_368,k2_zfmisc_1(A_367,B_368),D_369),A_367)
      | ~ r2_hidden(D_369,k2_zfmisc_1(A_367,B_368)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_3963,plain,(
    ! [D_370,B_371] : ~ r2_hidden(D_370,k2_zfmisc_1('#skF_13',B_371)) ),
    inference(resolution,[status(thm)],[c_3954,c_3649])).

tff(c_3995,plain,(
    ! [B_371] : k2_zfmisc_1('#skF_13',B_371) = '#skF_13' ),
    inference(resolution,[status(thm)],[c_3884,c_3963])).

tff(c_58,plain,
    ( k1_xboole_0 = '#skF_12'
    | k1_xboole_0 = '#skF_11'
    | k1_xboole_0 != '#skF_13' ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_3637,plain,
    ( '#skF_13' = '#skF_12'
    | '#skF_11' = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3619,c_3619,c_3619,c_58])).

tff(c_3638,plain,(
    '#skF_11' = '#skF_13' ),
    inference(splitLeft,[status(thm)],[c_3637])).

tff(c_3618,plain,(
    k2_zfmisc_1('#skF_11','#skF_12') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_3625,plain,(
    k2_zfmisc_1('#skF_11','#skF_12') != '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3619,c_3618])).

tff(c_3639,plain,(
    k2_zfmisc_1('#skF_13','#skF_12') != '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3638,c_3625])).

tff(c_4002,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3995,c_3639])).

tff(c_4003,plain,(
    '#skF_13' = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_3637])).

tff(c_4005,plain,(
    ! [A_1] : k4_xboole_0('#skF_12',A_1) = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4003,c_4003,c_3620])).

tff(c_4030,plain,(
    ! [B_373,A_374] :
      ( ~ r2_hidden(B_373,A_374)
      | k4_xboole_0(A_374,k1_tarski(B_373)) != A_374 ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_4035,plain,(
    ! [B_373] : ~ r2_hidden(B_373,'#skF_12') ),
    inference(superposition,[status(thm),theory(equality)],[c_4005,c_4030])).

tff(c_5082,plain,(
    ! [B_452] :
      ( r2_hidden('#skF_9'('#skF_12',B_452),B_452)
      | k3_tarski('#skF_12') = B_452 ) ),
    inference(resolution,[status(thm)],[c_4135,c_4035])).

tff(c_5216,plain,(
    k3_tarski('#skF_12') = '#skF_12' ),
    inference(resolution,[status(thm)],[c_5082,c_4035])).

tff(c_4366,plain,(
    ! [A_411,B_412,D_413] :
      ( r2_hidden('#skF_6'(A_411,B_412,k2_zfmisc_1(A_411,B_412),D_413),B_412)
      | ~ r2_hidden(D_413,k2_zfmisc_1(A_411,B_412)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4434,plain,(
    ! [D_413,A_411] : ~ r2_hidden(D_413,k2_zfmisc_1(A_411,'#skF_12')) ),
    inference(resolution,[status(thm)],[c_4366,c_4035])).

tff(c_5201,plain,(
    ! [A_411] : k2_zfmisc_1(A_411,'#skF_12') = k3_tarski('#skF_12') ),
    inference(resolution,[status(thm)],[c_5082,c_4434])).

tff(c_5303,plain,(
    ! [A_411] : k2_zfmisc_1(A_411,'#skF_12') = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5216,c_5201])).

tff(c_4006,plain,(
    k2_zfmisc_1('#skF_11','#skF_12') != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4003,c_3625])).

tff(c_5314,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5303,c_4006])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:05:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.34/2.75  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.34/2.77  
% 6.34/2.77  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.34/2.77  %$ r2_hidden > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_11 > #skF_4 > #skF_14 > #skF_13 > #skF_2 > #skF_6 > #skF_8 > #skF_5 > #skF_3 > #skF_7 > #skF_9 > #skF_12 > #skF_10
% 6.34/2.77  
% 6.34/2.77  %Foreground sorts:
% 6.34/2.77  
% 6.34/2.77  
% 6.34/2.77  %Background operators:
% 6.34/2.77  
% 6.34/2.77  
% 6.34/2.77  %Foreground operators:
% 6.34/2.77  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 6.34/2.77  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.34/2.77  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.34/2.77  tff('#skF_11', type, '#skF_11': $i).
% 6.34/2.77  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.34/2.77  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.34/2.77  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 6.34/2.77  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.34/2.77  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 6.34/2.77  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.34/2.77  tff('#skF_14', type, '#skF_14': $i).
% 6.34/2.77  tff('#skF_13', type, '#skF_13': $i).
% 6.34/2.77  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.34/2.77  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 6.34/2.77  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 6.34/2.77  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.34/2.78  tff(k3_tarski, type, k3_tarski: $i > $i).
% 6.34/2.78  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 6.34/2.78  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.34/2.78  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 6.34/2.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.34/2.78  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 6.34/2.78  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 6.34/2.78  tff('#skF_12', type, '#skF_12': $i).
% 6.34/2.78  tff('#skF_10', type, '#skF_10': ($i * $i * $i) > $i).
% 6.34/2.78  
% 6.77/2.81  tff(f_51, axiom, (![A, B]: ((B = k3_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(C, D) & r2_hidden(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tarski)).
% 6.77/2.81  tff(f_63, negated_conjecture, ~(![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 6.77/2.81  tff(f_27, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 6.77/2.81  tff(f_56, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 6.77/2.81  tff(f_41, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 6.77/2.81  tff(c_4135, plain, (![A_400, B_401]: (r2_hidden('#skF_8'(A_400, B_401), A_400) | r2_hidden('#skF_9'(A_400, B_401), B_401) | k3_tarski(A_400)=B_401)), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.77/2.81  tff(c_3740, plain, (![A_354, B_355]: (r2_hidden('#skF_8'(A_354, B_355), A_354) | r2_hidden('#skF_9'(A_354, B_355), B_355) | k3_tarski(A_354)=B_355)), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.77/2.81  tff(c_3144, plain, (![A_309, B_310]: (r2_hidden('#skF_8'(A_309, B_310), A_309) | r2_hidden('#skF_9'(A_309, B_310), B_310) | k3_tarski(A_309)=B_310)), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.77/2.81  tff(c_54, plain, (k1_xboole_0='#skF_12' | k1_xboole_0='#skF_11' | k1_xboole_0!='#skF_14'), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.77/2.81  tff(c_80, plain, (k1_xboole_0!='#skF_14'), inference(splitLeft, [status(thm)], [c_54])).
% 6.77/2.81  tff(c_517, plain, (![A_101, B_102]: (r2_hidden('#skF_8'(A_101, B_102), A_101) | r2_hidden('#skF_9'(A_101, B_102), B_102) | k3_tarski(A_101)=B_102)), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.77/2.81  tff(c_2, plain, (![A_1]: (k4_xboole_0(k1_xboole_0, A_1)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.77/2.81  tff(c_106, plain, (![B_62, A_63]: (~r2_hidden(B_62, A_63) | k4_xboole_0(A_63, k1_tarski(B_62))!=A_63)), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.77/2.81  tff(c_115, plain, (![B_62]: (~r2_hidden(B_62, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2, c_106])).
% 6.77/2.81  tff(c_648, plain, (![B_103]: (r2_hidden('#skF_9'(k1_xboole_0, B_103), B_103) | k3_tarski(k1_xboole_0)=B_103)), inference(resolution, [status(thm)], [c_517, c_115])).
% 6.77/2.81  tff(c_56, plain, (k2_zfmisc_1('#skF_11', '#skF_12')!=k1_xboole_0 | k1_xboole_0!='#skF_13'), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.77/2.81  tff(c_79, plain, (k1_xboole_0!='#skF_13'), inference(splitLeft, [status(thm)], [c_56])).
% 6.77/2.81  tff(c_225, plain, (![A_92, B_93]: (r2_hidden('#skF_8'(A_92, B_93), A_92) | r2_hidden('#skF_9'(A_92, B_93), B_93) | k3_tarski(A_92)=B_93)), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.77/2.81  tff(c_376, plain, (![B_94]: (r2_hidden('#skF_9'(k1_xboole_0, B_94), B_94) | k3_tarski(k1_xboole_0)=B_94)), inference(resolution, [status(thm)], [c_225, c_115])).
% 6.77/2.81  tff(c_62, plain, (k1_xboole_0='#skF_12' | k1_xboole_0='#skF_11' | k2_zfmisc_1('#skF_13', '#skF_14')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.77/2.81  tff(c_81, plain, (k2_zfmisc_1('#skF_13', '#skF_14')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_62])).
% 6.77/2.81  tff(c_168, plain, (![E_80, F_81, A_82, B_83]: (r2_hidden(k4_tarski(E_80, F_81), k2_zfmisc_1(A_82, B_83)) | ~r2_hidden(F_81, B_83) | ~r2_hidden(E_80, A_82))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.77/2.81  tff(c_173, plain, (![E_80, F_81]: (r2_hidden(k4_tarski(E_80, F_81), k1_xboole_0) | ~r2_hidden(F_81, '#skF_14') | ~r2_hidden(E_80, '#skF_13'))), inference(superposition, [status(thm), theory('equality')], [c_81, c_168])).
% 6.77/2.81  tff(c_175, plain, (![F_81, E_80]: (~r2_hidden(F_81, '#skF_14') | ~r2_hidden(E_80, '#skF_13'))), inference(negUnitSimplification, [status(thm)], [c_115, c_173])).
% 6.77/2.81  tff(c_176, plain, (![E_80]: (~r2_hidden(E_80, '#skF_13'))), inference(splitLeft, [status(thm)], [c_175])).
% 6.77/2.81  tff(c_446, plain, (k3_tarski(k1_xboole_0)='#skF_13'), inference(resolution, [status(thm)], [c_376, c_176])).
% 6.77/2.81  tff(c_455, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_376, c_115])).
% 6.77/2.81  tff(c_477, plain, (k1_xboole_0='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_446, c_455])).
% 6.77/2.81  tff(c_479, plain, $false, inference(negUnitSimplification, [status(thm)], [c_79, c_477])).
% 6.77/2.81  tff(c_480, plain, (![F_81]: (~r2_hidden(F_81, '#skF_14'))), inference(splitRight, [status(thm)], [c_175])).
% 6.77/2.81  tff(c_708, plain, (k3_tarski(k1_xboole_0)='#skF_14'), inference(resolution, [status(thm)], [c_648, c_480])).
% 6.77/2.81  tff(c_717, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_648, c_115])).
% 6.77/2.81  tff(c_738, plain, (k1_xboole_0='#skF_14'), inference(demodulation, [status(thm), theory('equality')], [c_708, c_717])).
% 6.77/2.81  tff(c_740, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_738])).
% 6.77/2.81  tff(c_741, plain, (k1_xboole_0='#skF_11' | k1_xboole_0='#skF_12'), inference(splitRight, [status(thm)], [c_62])).
% 6.77/2.81  tff(c_2391, plain, (k1_xboole_0='#skF_12'), inference(splitLeft, [status(thm)], [c_741])).
% 6.77/2.81  tff(c_742, plain, (k2_zfmisc_1('#skF_13', '#skF_14')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_62])).
% 6.77/2.81  tff(c_2406, plain, (k2_zfmisc_1('#skF_13', '#skF_14')!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_2391, c_742])).
% 6.77/2.81  tff(c_1209, plain, (![A_171, B_172]: (r2_hidden('#skF_8'(A_171, B_172), A_171) | r2_hidden('#skF_9'(A_171, B_172), B_172) | k3_tarski(A_171)=B_172)), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.77/2.81  tff(c_811, plain, (![A_118, B_119]: (r2_hidden('#skF_8'(A_118, B_119), A_118) | r2_hidden('#skF_9'(A_118, B_119), B_119) | k3_tarski(A_118)=B_119)), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.77/2.81  tff(c_744, plain, (k1_xboole_0='#skF_12'), inference(splitLeft, [status(thm)], [c_741])).
% 6.77/2.81  tff(c_748, plain, (![A_1]: (k4_xboole_0('#skF_12', A_1)='#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_744, c_744, c_2])).
% 6.77/2.81  tff(c_761, plain, (![B_105, A_106]: (~r2_hidden(B_105, A_106) | k4_xboole_0(A_106, k1_tarski(B_105))!=A_106)), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.77/2.81  tff(c_766, plain, (![B_105]: (~r2_hidden(B_105, '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_748, c_761])).
% 6.77/2.81  tff(c_884, plain, (![B_125]: (r2_hidden('#skF_9'('#skF_12', B_125), B_125) | k3_tarski('#skF_12')=B_125)), inference(resolution, [status(thm)], [c_811, c_766])).
% 6.77/2.81  tff(c_913, plain, (k3_tarski('#skF_12')='#skF_12'), inference(resolution, [status(thm)], [c_884, c_766])).
% 6.77/2.81  tff(c_832, plain, (![B_119]: (r2_hidden('#skF_9'('#skF_12', B_119), B_119) | k3_tarski('#skF_12')=B_119)), inference(resolution, [status(thm)], [c_811, c_766])).
% 6.77/2.81  tff(c_914, plain, (![B_119]: (r2_hidden('#skF_9'('#skF_12', B_119), B_119) | B_119='#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_913, c_832])).
% 6.77/2.81  tff(c_1026, plain, (![A_138, B_139, D_140]: (r2_hidden('#skF_6'(A_138, B_139, k2_zfmisc_1(A_138, B_139), D_140), B_139) | ~r2_hidden(D_140, k2_zfmisc_1(A_138, B_139)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.77/2.81  tff(c_1039, plain, (![D_141, A_142]: (~r2_hidden(D_141, k2_zfmisc_1(A_142, '#skF_12')))), inference(resolution, [status(thm)], [c_1026, c_766])).
% 6.77/2.81  tff(c_1079, plain, (![A_142]: (k2_zfmisc_1(A_142, '#skF_12')='#skF_12')), inference(resolution, [status(thm)], [c_914, c_1039])).
% 6.77/2.81  tff(c_60, plain, (k2_zfmisc_1('#skF_11', '#skF_12')!=k1_xboole_0 | k2_zfmisc_1('#skF_13', '#skF_14')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.77/2.81  tff(c_743, plain, (k2_zfmisc_1('#skF_11', '#skF_12')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_60])).
% 6.77/2.81  tff(c_745, plain, (k2_zfmisc_1('#skF_11', '#skF_12')!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_744, c_743])).
% 6.77/2.81  tff(c_1086, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1079, c_745])).
% 6.77/2.81  tff(c_1087, plain, (k1_xboole_0='#skF_11'), inference(splitRight, [status(thm)], [c_741])).
% 6.77/2.81  tff(c_1094, plain, (![A_1]: (k4_xboole_0('#skF_11', A_1)='#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_1087, c_1087, c_2])).
% 6.77/2.81  tff(c_1125, plain, (![B_146, A_147]: (~r2_hidden(B_146, A_147) | k4_xboole_0(A_147, k1_tarski(B_146))!=A_147)), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.77/2.81  tff(c_1134, plain, (![B_146]: (~r2_hidden(B_146, '#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_1094, c_1125])).
% 6.77/2.81  tff(c_2156, plain, (![B_223]: (r2_hidden('#skF_9'('#skF_11', B_223), B_223) | k3_tarski('#skF_11')=B_223)), inference(resolution, [status(thm)], [c_1209, c_1134])).
% 6.77/2.81  tff(c_2289, plain, (k3_tarski('#skF_11')='#skF_11'), inference(resolution, [status(thm)], [c_2156, c_1134])).
% 6.77/2.81  tff(c_1440, plain, (![A_182, B_183, D_184]: (r2_hidden('#skF_5'(A_182, B_183, k2_zfmisc_1(A_182, B_183), D_184), A_182) | ~r2_hidden(D_184, k2_zfmisc_1(A_182, B_183)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.77/2.81  tff(c_1507, plain, (![D_184, B_183]: (~r2_hidden(D_184, k2_zfmisc_1('#skF_11', B_183)))), inference(resolution, [status(thm)], [c_1440, c_1134])).
% 6.77/2.81  tff(c_2275, plain, (![B_183]: (k2_zfmisc_1('#skF_11', B_183)=k3_tarski('#skF_11'))), inference(resolution, [status(thm)], [c_2156, c_1507])).
% 6.77/2.81  tff(c_2377, plain, (![B_183]: (k2_zfmisc_1('#skF_11', B_183)='#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_2289, c_2275])).
% 6.77/2.81  tff(c_1091, plain, (k2_zfmisc_1('#skF_11', '#skF_12')!='#skF_11'), inference(demodulation, [status(thm), theory('equality')], [c_1087, c_743])).
% 6.77/2.81  tff(c_2388, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2377, c_1091])).
% 6.77/2.81  tff(c_2389, plain, (k2_zfmisc_1('#skF_13', '#skF_14')=k1_xboole_0), inference(splitRight, [status(thm)], [c_60])).
% 6.77/2.81  tff(c_2412, plain, (k2_zfmisc_1('#skF_13', '#skF_14')='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_2391, c_2389])).
% 6.77/2.81  tff(c_2413, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2406, c_2412])).
% 6.77/2.81  tff(c_2414, plain, (k1_xboole_0='#skF_11'), inference(splitRight, [status(thm)], [c_741])).
% 6.77/2.81  tff(c_2420, plain, (k2_zfmisc_1('#skF_13', '#skF_14')='#skF_11'), inference(demodulation, [status(thm), theory('equality')], [c_2414, c_2389])).
% 6.77/2.81  tff(c_2446, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2420, c_2414, c_742])).
% 6.77/2.81  tff(c_2448, plain, (k1_xboole_0='#skF_14'), inference(splitRight, [status(thm)], [c_54])).
% 6.77/2.81  tff(c_2450, plain, (![A_1]: (k4_xboole_0('#skF_14', A_1)='#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_2448, c_2448, c_2])).
% 6.77/2.81  tff(c_3060, plain, (![B_284, A_285]: (~r2_hidden(B_284, A_285) | k4_xboole_0(A_285, k1_tarski(B_284))!=A_285)), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.77/2.81  tff(c_3069, plain, (![B_284]: (~r2_hidden(B_284, '#skF_14'))), inference(superposition, [status(thm), theory('equality')], [c_2450, c_3060])).
% 6.77/2.81  tff(c_3248, plain, (![B_311]: (r2_hidden('#skF_9'('#skF_14', B_311), B_311) | k3_tarski('#skF_14')=B_311)), inference(resolution, [status(thm)], [c_3144, c_3069])).
% 6.77/2.81  tff(c_3302, plain, (k3_tarski('#skF_14')='#skF_14'), inference(resolution, [status(thm)], [c_3248, c_3069])).
% 6.77/2.81  tff(c_3237, plain, (![B_310]: (r2_hidden('#skF_9'('#skF_14', B_310), B_310) | k3_tarski('#skF_14')=B_310)), inference(resolution, [status(thm)], [c_3144, c_3069])).
% 6.77/2.81  tff(c_3541, plain, (![B_331]: (r2_hidden('#skF_9'('#skF_14', B_331), B_331) | B_331='#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_3302, c_3237])).
% 6.77/2.81  tff(c_3303, plain, (![A_312, B_313, D_314]: (r2_hidden('#skF_5'(A_312, B_313, k2_zfmisc_1(A_312, B_313), D_314), A_312) | ~r2_hidden(D_314, k2_zfmisc_1(A_312, B_313)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.77/2.81  tff(c_3356, plain, (![D_314, B_313]: (~r2_hidden(D_314, k2_zfmisc_1('#skF_14', B_313)))), inference(resolution, [status(thm)], [c_3303, c_3069])).
% 6.77/2.81  tff(c_3572, plain, (![B_313]: (k2_zfmisc_1('#skF_14', B_313)='#skF_14')), inference(resolution, [status(thm)], [c_3541, c_3356])).
% 6.77/2.81  tff(c_2584, plain, (![A_258, B_259]: (r2_hidden('#skF_8'(A_258, B_259), A_258) | r2_hidden('#skF_9'(A_258, B_259), B_259) | k3_tarski(A_258)=B_259)), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.77/2.81  tff(c_2447, plain, (k1_xboole_0='#skF_11' | k1_xboole_0='#skF_12'), inference(splitRight, [status(thm)], [c_54])).
% 6.77/2.81  tff(c_2457, plain, ('#skF_11'='#skF_14' | '#skF_14'='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_2448, c_2448, c_2447])).
% 6.77/2.81  tff(c_2458, plain, ('#skF_14'='#skF_12'), inference(splitLeft, [status(thm)], [c_2457])).
% 6.77/2.81  tff(c_2470, plain, (![A_1]: (k4_xboole_0('#skF_12', A_1)='#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_2458, c_2458, c_2450])).
% 6.77/2.81  tff(c_2500, plain, (![B_233, A_234]: (~r2_hidden(B_233, A_234) | k4_xboole_0(A_234, k1_tarski(B_233))!=A_234)), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.77/2.81  tff(c_2509, plain, (![B_233]: (~r2_hidden(B_233, '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_2470, c_2500])).
% 6.77/2.81  tff(c_2688, plain, (![B_260]: (r2_hidden('#skF_9'('#skF_12', B_260), B_260) | k3_tarski('#skF_12')=B_260)), inference(resolution, [status(thm)], [c_2584, c_2509])).
% 6.77/2.81  tff(c_2742, plain, (k3_tarski('#skF_12')='#skF_12'), inference(resolution, [status(thm)], [c_2688, c_2509])).
% 6.77/2.81  tff(c_2677, plain, (![B_259]: (r2_hidden('#skF_9'('#skF_12', B_259), B_259) | k3_tarski('#skF_12')=B_259)), inference(resolution, [status(thm)], [c_2584, c_2509])).
% 6.77/2.81  tff(c_2981, plain, (![B_280]: (r2_hidden('#skF_9'('#skF_12', B_280), B_280) | B_280='#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_2742, c_2677])).
% 6.77/2.81  tff(c_2869, plain, (![A_268, B_269, D_270]: (r2_hidden('#skF_6'(A_268, B_269, k2_zfmisc_1(A_268, B_269), D_270), B_269) | ~r2_hidden(D_270, k2_zfmisc_1(A_268, B_269)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.77/2.81  tff(c_2887, plain, (![D_270, A_268]: (~r2_hidden(D_270, k2_zfmisc_1(A_268, '#skF_12')))), inference(resolution, [status(thm)], [c_2869, c_2509])).
% 6.77/2.81  tff(c_3010, plain, (![A_268]: (k2_zfmisc_1(A_268, '#skF_12')='#skF_12')), inference(resolution, [status(thm)], [c_2981, c_2887])).
% 6.77/2.81  tff(c_52, plain, (k2_zfmisc_1('#skF_11', '#skF_12')!=k1_xboole_0 | k1_xboole_0!='#skF_14'), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.77/2.81  tff(c_2456, plain, (k2_zfmisc_1('#skF_11', '#skF_12')!='#skF_14'), inference(demodulation, [status(thm), theory('equality')], [c_2448, c_2448, c_52])).
% 6.77/2.81  tff(c_2460, plain, (k2_zfmisc_1('#skF_11', '#skF_12')!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_2458, c_2456])).
% 6.77/2.81  tff(c_3021, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3010, c_2460])).
% 6.77/2.81  tff(c_3022, plain, ('#skF_11'='#skF_14'), inference(splitRight, [status(thm)], [c_2457])).
% 6.77/2.81  tff(c_3024, plain, (k2_zfmisc_1('#skF_14', '#skF_12')!='#skF_14'), inference(demodulation, [status(thm), theory('equality')], [c_3022, c_2456])).
% 6.77/2.81  tff(c_3617, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3572, c_3024])).
% 6.77/2.81  tff(c_3619, plain, (k1_xboole_0='#skF_13'), inference(splitRight, [status(thm)], [c_56])).
% 6.77/2.81  tff(c_3620, plain, (![A_1]: (k4_xboole_0('#skF_13', A_1)='#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_3619, c_3619, c_2])).
% 6.77/2.81  tff(c_3644, plain, (![B_334, A_335]: (~r2_hidden(B_334, A_335) | k4_xboole_0(A_335, k1_tarski(B_334))!=A_335)), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.77/2.81  tff(c_3649, plain, (![B_334]: (~r2_hidden(B_334, '#skF_13'))), inference(superposition, [status(thm), theory('equality')], [c_3620, c_3644])).
% 6.77/2.81  tff(c_3834, plain, (![B_356]: (r2_hidden('#skF_9'('#skF_13', B_356), B_356) | k3_tarski('#skF_13')=B_356)), inference(resolution, [status(thm)], [c_3740, c_3649])).
% 6.77/2.81  tff(c_3883, plain, (k3_tarski('#skF_13')='#skF_13'), inference(resolution, [status(thm)], [c_3834, c_3649])).
% 6.77/2.81  tff(c_3824, plain, (![B_355]: (r2_hidden('#skF_9'('#skF_13', B_355), B_355) | k3_tarski('#skF_13')=B_355)), inference(resolution, [status(thm)], [c_3740, c_3649])).
% 6.77/2.81  tff(c_3884, plain, (![B_355]: (r2_hidden('#skF_9'('#skF_13', B_355), B_355) | B_355='#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_3883, c_3824])).
% 6.77/2.81  tff(c_3954, plain, (![A_367, B_368, D_369]: (r2_hidden('#skF_5'(A_367, B_368, k2_zfmisc_1(A_367, B_368), D_369), A_367) | ~r2_hidden(D_369, k2_zfmisc_1(A_367, B_368)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.77/2.81  tff(c_3963, plain, (![D_370, B_371]: (~r2_hidden(D_370, k2_zfmisc_1('#skF_13', B_371)))), inference(resolution, [status(thm)], [c_3954, c_3649])).
% 6.77/2.81  tff(c_3995, plain, (![B_371]: (k2_zfmisc_1('#skF_13', B_371)='#skF_13')), inference(resolution, [status(thm)], [c_3884, c_3963])).
% 6.77/2.81  tff(c_58, plain, (k1_xboole_0='#skF_12' | k1_xboole_0='#skF_11' | k1_xboole_0!='#skF_13'), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.77/2.81  tff(c_3637, plain, ('#skF_13'='#skF_12' | '#skF_11'='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_3619, c_3619, c_3619, c_58])).
% 6.77/2.81  tff(c_3638, plain, ('#skF_11'='#skF_13'), inference(splitLeft, [status(thm)], [c_3637])).
% 6.77/2.81  tff(c_3618, plain, (k2_zfmisc_1('#skF_11', '#skF_12')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_56])).
% 6.77/2.81  tff(c_3625, plain, (k2_zfmisc_1('#skF_11', '#skF_12')!='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_3619, c_3618])).
% 6.77/2.81  tff(c_3639, plain, (k2_zfmisc_1('#skF_13', '#skF_12')!='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_3638, c_3625])).
% 6.77/2.81  tff(c_4002, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3995, c_3639])).
% 6.77/2.81  tff(c_4003, plain, ('#skF_13'='#skF_12'), inference(splitRight, [status(thm)], [c_3637])).
% 6.77/2.81  tff(c_4005, plain, (![A_1]: (k4_xboole_0('#skF_12', A_1)='#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_4003, c_4003, c_3620])).
% 6.77/2.81  tff(c_4030, plain, (![B_373, A_374]: (~r2_hidden(B_373, A_374) | k4_xboole_0(A_374, k1_tarski(B_373))!=A_374)), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.77/2.81  tff(c_4035, plain, (![B_373]: (~r2_hidden(B_373, '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_4005, c_4030])).
% 6.77/2.81  tff(c_5082, plain, (![B_452]: (r2_hidden('#skF_9'('#skF_12', B_452), B_452) | k3_tarski('#skF_12')=B_452)), inference(resolution, [status(thm)], [c_4135, c_4035])).
% 6.77/2.81  tff(c_5216, plain, (k3_tarski('#skF_12')='#skF_12'), inference(resolution, [status(thm)], [c_5082, c_4035])).
% 6.77/2.81  tff(c_4366, plain, (![A_411, B_412, D_413]: (r2_hidden('#skF_6'(A_411, B_412, k2_zfmisc_1(A_411, B_412), D_413), B_412) | ~r2_hidden(D_413, k2_zfmisc_1(A_411, B_412)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.77/2.81  tff(c_4434, plain, (![D_413, A_411]: (~r2_hidden(D_413, k2_zfmisc_1(A_411, '#skF_12')))), inference(resolution, [status(thm)], [c_4366, c_4035])).
% 6.77/2.81  tff(c_5201, plain, (![A_411]: (k2_zfmisc_1(A_411, '#skF_12')=k3_tarski('#skF_12'))), inference(resolution, [status(thm)], [c_5082, c_4434])).
% 6.77/2.81  tff(c_5303, plain, (![A_411]: (k2_zfmisc_1(A_411, '#skF_12')='#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_5216, c_5201])).
% 6.77/2.81  tff(c_4006, plain, (k2_zfmisc_1('#skF_11', '#skF_12')!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_4003, c_3625])).
% 6.77/2.81  tff(c_5314, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5303, c_4006])).
% 6.77/2.81  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.77/2.81  
% 6.77/2.81  Inference rules
% 6.77/2.81  ----------------------
% 6.77/2.81  #Ref     : 0
% 6.77/2.81  #Sup     : 1026
% 6.77/2.81  #Fact    : 0
% 6.77/2.81  #Define  : 0
% 6.77/2.81  #Split   : 12
% 6.77/2.81  #Chain   : 0
% 6.77/2.81  #Close   : 0
% 6.77/2.81  
% 6.77/2.81  Ordering : KBO
% 6.77/2.81  
% 6.77/2.81  Simplification rules
% 6.77/2.81  ----------------------
% 6.77/2.81  #Subsume      : 191
% 6.77/2.81  #Demod        : 553
% 6.77/2.81  #Tautology    : 147
% 6.77/2.81  #SimpNegUnit  : 28
% 6.77/2.81  #BackRed      : 147
% 6.77/2.81  
% 6.77/2.81  #Partial instantiations: 0
% 6.77/2.81  #Strategies tried      : 1
% 6.77/2.81  
% 6.77/2.81  Timing (in seconds)
% 6.77/2.81  ----------------------
% 6.77/2.82  Preprocessing        : 0.50
% 6.88/2.82  Parsing              : 0.23
% 6.88/2.82  CNF conversion       : 0.05
% 6.88/2.82  Main loop            : 1.34
% 6.88/2.82  Inferencing          : 0.46
% 6.88/2.82  Reduction            : 0.40
% 6.88/2.82  Demodulation         : 0.22
% 6.88/2.82  BG Simplification    : 0.07
% 6.88/2.82  Subsumption          : 0.25
% 6.88/2.82  Abstraction          : 0.08
% 6.88/2.82  MUC search           : 0.00
% 6.88/2.82  Cooper               : 0.00
% 6.88/2.82  Total                : 1.92
% 6.88/2.82  Index Insertion      : 0.00
% 6.88/2.82  Index Deletion       : 0.00
% 6.88/2.82  Index Matching       : 0.00
% 6.88/2.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
