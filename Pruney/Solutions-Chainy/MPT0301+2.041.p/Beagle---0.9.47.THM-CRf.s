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
% DateTime   : Thu Dec  3 09:53:45 EST 2020

% Result     : Theorem 5.07s
% Output     : CNFRefutation 5.39s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 994 expanded)
%              Number of leaves         :   25 ( 297 expanded)
%              Depth                    :   11
%              Number of atoms          :  193 (1985 expanded)
%              Number of equality atoms :   95 (1606 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_11 > #skF_4 > #skF_10 > #skF_5 > #skF_2 > #skF_7 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(f_62,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_zfmisc_1(A,B) = k1_xboole_0
      <=> ( A = k1_xboole_0
          | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_43,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_41,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_7155,plain,(
    ! [A_742,B_743,C_744] :
      ( r2_hidden('#skF_4'(A_742,B_743,C_744),B_743)
      | r2_hidden('#skF_5'(A_742,B_743,C_744),C_744)
      | k2_zfmisc_1(A_742,B_743) = C_744 ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_6176,plain,(
    ! [A_653,B_654,C_655] :
      ( r2_hidden('#skF_4'(A_653,B_654,C_655),B_654)
      | r2_hidden('#skF_5'(A_653,B_654,C_655),C_655)
      | k2_zfmisc_1(A_653,B_654) = C_655 ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_5001,plain,(
    ! [A_540,B_541,C_542] :
      ( r2_hidden('#skF_3'(A_540,B_541,C_542),A_540)
      | r2_hidden('#skF_5'(A_540,B_541,C_542),C_542)
      | k2_zfmisc_1(A_540,B_541) = C_542 ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_4029,plain,(
    ! [A_444,B_445,C_446] :
      ( r2_hidden('#skF_4'(A_444,B_445,C_446),B_445)
      | r2_hidden('#skF_5'(A_444,B_445,C_446),C_446)
      | k2_zfmisc_1(A_444,B_445) = C_446 ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_3480,plain,(
    ! [A_391,B_392,C_393] :
      ( r2_hidden('#skF_3'(A_391,B_392,C_393),A_391)
      | r2_hidden('#skF_5'(A_391,B_392,C_393),C_393)
      | k2_zfmisc_1(A_391,B_392) = C_393 ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2182,plain,(
    ! [A_274,B_275,C_276] :
      ( r2_hidden('#skF_4'(A_274,B_275,C_276),B_275)
      | r2_hidden('#skF_5'(A_274,B_275,C_276),C_276)
      | k2_zfmisc_1(A_274,B_275) = C_276 ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_36,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 != '#skF_11' ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_54,plain,(
    k1_xboole_0 != '#skF_11' ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_1274,plain,(
    ! [A_193,B_194,C_195] :
      ( r2_hidden('#skF_4'(A_193,B_194,C_195),B_194)
      | r2_hidden('#skF_5'(A_193,B_194,C_195),C_195)
      | k2_zfmisc_1(A_193,B_194) = C_195 ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_38,plain,
    ( k2_zfmisc_1('#skF_8','#skF_9') != k1_xboole_0
    | k1_xboole_0 != '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_53,plain,(
    k1_xboole_0 != '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_372,plain,(
    ! [A_105,B_106,C_107] :
      ( r2_hidden('#skF_4'(A_105,B_106,C_107),B_106)
      | r2_hidden('#skF_5'(A_105,B_106,C_107),C_107)
      | k2_zfmisc_1(A_105,B_106) = C_107 ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_8,plain,(
    ! [A_7] : r1_xboole_0(A_7,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [A_6] : k3_xboole_0(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_61,plain,(
    ! [A_44,B_45,C_46] :
      ( ~ r1_xboole_0(A_44,B_45)
      | ~ r2_hidden(C_46,k3_xboole_0(A_44,B_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_64,plain,(
    ! [A_6,C_46] :
      ( ~ r1_xboole_0(A_6,k1_xboole_0)
      | ~ r2_hidden(C_46,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_61])).

tff(c_66,plain,(
    ! [C_46] : ~ r2_hidden(C_46,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_64])).

tff(c_44,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k2_zfmisc_1('#skF_10','#skF_11') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_55,plain,(
    k2_zfmisc_1('#skF_10','#skF_11') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_78,plain,(
    ! [E_50,F_51,A_52,B_53] :
      ( r2_hidden(k4_tarski(E_50,F_51),k2_zfmisc_1(A_52,B_53))
      | ~ r2_hidden(F_51,B_53)
      | ~ r2_hidden(E_50,A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_81,plain,(
    ! [E_50,F_51] :
      ( r2_hidden(k4_tarski(E_50,F_51),k1_xboole_0)
      | ~ r2_hidden(F_51,'#skF_11')
      | ~ r2_hidden(E_50,'#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_78])).

tff(c_82,plain,(
    ! [F_51,E_50] :
      ( ~ r2_hidden(F_51,'#skF_11')
      | ~ r2_hidden(E_50,'#skF_10') ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_81])).

tff(c_83,plain,(
    ! [E_50] : ~ r2_hidden(E_50,'#skF_10') ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_625,plain,(
    ! [A_120,C_121] :
      ( r2_hidden('#skF_5'(A_120,'#skF_10',C_121),C_121)
      | k2_zfmisc_1(A_120,'#skF_10') = C_121 ) ),
    inference(resolution,[status(thm)],[c_372,c_83])).

tff(c_728,plain,(
    ! [A_120] : k2_zfmisc_1(A_120,'#skF_10') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_625,c_83])).

tff(c_729,plain,(
    ! [A_120] : k2_zfmisc_1(A_120,'#skF_10') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_625,c_66])).

tff(c_806,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_728,c_729])).

tff(c_807,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_806])).

tff(c_808,plain,(
    ! [F_51] : ~ r2_hidden(F_51,'#skF_11') ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_1584,plain,(
    ! [A_208,C_209] :
      ( r2_hidden('#skF_5'(A_208,'#skF_11',C_209),C_209)
      | k2_zfmisc_1(A_208,'#skF_11') = C_209 ) ),
    inference(resolution,[status(thm)],[c_1274,c_808])).

tff(c_1707,plain,(
    ! [A_208] : k2_zfmisc_1(A_208,'#skF_11') = '#skF_11' ),
    inference(resolution,[status(thm)],[c_1584,c_808])).

tff(c_1716,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1707,c_55])).

tff(c_1718,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1716])).

tff(c_1719,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1721,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_1719])).

tff(c_1725,plain,(
    ! [A_7] : r1_xboole_0(A_7,'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1721,c_8])).

tff(c_1724,plain,(
    ! [A_6] : k3_xboole_0(A_6,'#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1721,c_1721,c_6])).

tff(c_1739,plain,(
    ! [A_212,B_213,C_214] :
      ( ~ r1_xboole_0(A_212,B_213)
      | ~ r2_hidden(C_214,k3_xboole_0(A_212,B_213)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1742,plain,(
    ! [A_6,C_214] :
      ( ~ r1_xboole_0(A_6,'#skF_9')
      | ~ r2_hidden(C_214,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1724,c_1739])).

tff(c_1744,plain,(
    ! [C_214] : ~ r2_hidden(C_214,'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1725,c_1742])).

tff(c_2908,plain,(
    ! [A_317,C_318] :
      ( r2_hidden('#skF_5'(A_317,'#skF_9',C_318),C_318)
      | k2_zfmisc_1(A_317,'#skF_9') = C_318 ) ),
    inference(resolution,[status(thm)],[c_2182,c_1744])).

tff(c_2942,plain,(
    ! [A_317] : k2_zfmisc_1(A_317,'#skF_9') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_2908,c_1744])).

tff(c_1720,plain,(
    k2_zfmisc_1('#skF_10','#skF_11') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1738,plain,(
    k2_zfmisc_1('#skF_10','#skF_11') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1721,c_1720])).

tff(c_42,plain,
    ( k2_zfmisc_1('#skF_8','#skF_9') != k1_xboole_0
    | k2_zfmisc_1('#skF_10','#skF_11') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1745,plain,
    ( k2_zfmisc_1('#skF_8','#skF_9') != '#skF_9'
    | k2_zfmisc_1('#skF_10','#skF_11') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1721,c_1721,c_42])).

tff(c_1746,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') != '#skF_9' ),
    inference(negUnitSimplification,[status(thm)],[c_1738,c_1745])).

tff(c_2954,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2942,c_1746])).

tff(c_2955,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_1719])).

tff(c_2960,plain,(
    ! [A_7] : r1_xboole_0(A_7,'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2955,c_8])).

tff(c_2959,plain,(
    ! [A_6] : k3_xboole_0(A_6,'#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2955,c_2955,c_6])).

tff(c_2977,plain,(
    ! [A_321,B_322,C_323] :
      ( ~ r1_xboole_0(A_321,B_322)
      | ~ r2_hidden(C_323,k3_xboole_0(A_321,B_322)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2980,plain,(
    ! [A_6,C_323] :
      ( ~ r1_xboole_0(A_6,'#skF_8')
      | ~ r2_hidden(C_323,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2959,c_2977])).

tff(c_2982,plain,(
    ! [C_323] : ~ r2_hidden(C_323,'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2960,c_2980])).

tff(c_3730,plain,(
    ! [A_402,B_403] :
      ( r2_hidden('#skF_3'(A_402,B_403,'#skF_8'),A_402)
      | k2_zfmisc_1(A_402,B_403) = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_3480,c_2982])).

tff(c_3819,plain,(
    ! [B_403] : k2_zfmisc_1('#skF_8',B_403) = '#skF_8' ),
    inference(resolution,[status(thm)],[c_3730,c_2982])).

tff(c_2965,plain,
    ( k2_zfmisc_1('#skF_8','#skF_9') != '#skF_8'
    | k2_zfmisc_1('#skF_10','#skF_11') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2955,c_2955,c_42])).

tff(c_2966,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_2965])).

tff(c_3830,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3819,c_2966])).

tff(c_3831,plain,(
    k2_zfmisc_1('#skF_10','#skF_11') = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_2965])).

tff(c_3840,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3831,c_2955,c_1720])).

tff(c_3842,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_3841,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_3851,plain,
    ( '#skF_11' = '#skF_8'
    | '#skF_11' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3842,c_3842,c_3841])).

tff(c_3852,plain,(
    '#skF_11' = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_3851])).

tff(c_3845,plain,(
    ! [A_7] : r1_xboole_0(A_7,'#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3842,c_8])).

tff(c_3853,plain,(
    ! [A_7] : r1_xboole_0(A_7,'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3852,c_3845])).

tff(c_3844,plain,(
    ! [A_6] : k3_xboole_0(A_6,'#skF_11') = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3842,c_3842,c_6])).

tff(c_3865,plain,(
    ! [A_6] : k3_xboole_0(A_6,'#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3852,c_3852,c_3844])).

tff(c_3877,plain,(
    ! [A_408,B_409,C_410] :
      ( ~ r1_xboole_0(A_408,B_409)
      | ~ r2_hidden(C_410,k3_xboole_0(A_408,B_409)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_3880,plain,(
    ! [A_6,C_410] :
      ( ~ r1_xboole_0(A_6,'#skF_9')
      | ~ r2_hidden(C_410,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3865,c_3877])).

tff(c_3882,plain,(
    ! [C_410] : ~ r2_hidden(C_410,'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3853,c_3880])).

tff(c_4630,plain,(
    ! [A_489,C_490] :
      ( r2_hidden('#skF_5'(A_489,'#skF_9',C_490),C_490)
      | k2_zfmisc_1(A_489,'#skF_9') = C_490 ) ),
    inference(resolution,[status(thm)],[c_4029,c_3882])).

tff(c_4719,plain,(
    ! [A_489] : k2_zfmisc_1(A_489,'#skF_9') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_4630,c_3882])).

tff(c_3855,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3852,c_3842])).

tff(c_34,plain,
    ( k2_zfmisc_1('#skF_8','#skF_9') != k1_xboole_0
    | k1_xboole_0 != '#skF_11' ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_3874,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3855,c_3852,c_3855,c_34])).

tff(c_4731,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4719,c_3874])).

tff(c_4732,plain,(
    '#skF_11' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_3851])).

tff(c_4737,plain,(
    ! [A_7] : r1_xboole_0(A_7,'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4732,c_3845])).

tff(c_4750,plain,(
    ! [A_6] : k3_xboole_0(A_6,'#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4732,c_4732,c_3844])).

tff(c_4761,plain,(
    ! [A_493,B_494,C_495] :
      ( ~ r1_xboole_0(A_493,B_494)
      | ~ r2_hidden(C_495,k3_xboole_0(A_493,B_494)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4764,plain,(
    ! [A_6,C_495] :
      ( ~ r1_xboole_0(A_6,'#skF_8')
      | ~ r2_hidden(C_495,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4750,c_4761])).

tff(c_4766,plain,(
    ! [C_495] : ~ r2_hidden(C_495,'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4737,c_4764])).

tff(c_5514,plain,(
    ! [A_574,B_575] :
      ( r2_hidden('#skF_3'(A_574,B_575,'#skF_8'),A_574)
      | k2_zfmisc_1(A_574,B_575) = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_5001,c_4766])).

tff(c_5603,plain,(
    ! [B_575] : k2_zfmisc_1('#skF_8',B_575) = '#skF_8' ),
    inference(resolution,[status(thm)],[c_5514,c_4766])).

tff(c_4735,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') != '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3842,c_3842,c_34])).

tff(c_4736,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4732,c_4735])).

tff(c_5626,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5603,c_4736])).

tff(c_5628,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_40,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 != '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_5647,plain,
    ( '#skF_10' = '#skF_9'
    | '#skF_10' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5628,c_5628,c_5628,c_40])).

tff(c_5648,plain,(
    '#skF_10' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_5647])).

tff(c_5630,plain,(
    ! [A_7] : r1_xboole_0(A_7,'#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5628,c_8])).

tff(c_5652,plain,(
    ! [A_7] : r1_xboole_0(A_7,'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5648,c_5630])).

tff(c_5629,plain,(
    ! [A_6] : k3_xboole_0(A_6,'#skF_10') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5628,c_5628,c_6])).

tff(c_5649,plain,(
    ! [A_6] : k3_xboole_0(A_6,'#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5648,c_5648,c_5629])).

tff(c_5673,plain,(
    ! [A_583,B_584,C_585] :
      ( ~ r1_xboole_0(A_583,B_584)
      | ~ r2_hidden(C_585,k3_xboole_0(A_583,B_584)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_5676,plain,(
    ! [A_6,C_585] :
      ( ~ r1_xboole_0(A_6,'#skF_8')
      | ~ r2_hidden(C_585,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5649,c_5673])).

tff(c_5678,plain,(
    ! [C_585] : ~ r2_hidden(C_585,'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5652,c_5676])).

tff(c_6426,plain,(
    ! [A_664,C_665] :
      ( r2_hidden('#skF_5'(A_664,'#skF_8',C_665),C_665)
      | k2_zfmisc_1(A_664,'#skF_8') = C_665 ) ),
    inference(resolution,[status(thm)],[c_6176,c_5678])).

tff(c_6515,plain,(
    ! [A_664] : k2_zfmisc_1(A_664,'#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_6426,c_5678])).

tff(c_5713,plain,(
    ! [A_598,B_599,D_600] :
      ( r2_hidden('#skF_6'(A_598,B_599,k2_zfmisc_1(A_598,B_599),D_600),A_598)
      | ~ r2_hidden(D_600,k2_zfmisc_1(A_598,B_599)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_5727,plain,(
    ! [D_600,B_599] : ~ r2_hidden(D_600,k2_zfmisc_1('#skF_8',B_599)) ),
    inference(resolution,[status(thm)],[c_5713,c_5678])).

tff(c_6513,plain,(
    ! [A_664,B_599] : k2_zfmisc_1(A_664,'#skF_8') = k2_zfmisc_1('#skF_8',B_599) ),
    inference(resolution,[status(thm)],[c_6426,c_5727])).

tff(c_6609,plain,(
    ! [B_599] : k2_zfmisc_1('#skF_8',B_599) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6515,c_6513])).

tff(c_5627,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_5638,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5628,c_5627])).

tff(c_5650,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5648,c_5638])).

tff(c_6623,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6609,c_5650])).

tff(c_6624,plain,(
    '#skF_10' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_5647])).

tff(c_6629,plain,(
    ! [A_7] : r1_xboole_0(A_7,'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6624,c_5630])).

tff(c_6626,plain,(
    ! [A_6] : k3_xboole_0(A_6,'#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6624,c_6624,c_5629])).

tff(c_6652,plain,(
    ! [A_672,B_673,C_674] :
      ( ~ r1_xboole_0(A_672,B_673)
      | ~ r2_hidden(C_674,k3_xboole_0(A_672,B_673)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6655,plain,(
    ! [A_6,C_674] :
      ( ~ r1_xboole_0(A_6,'#skF_9')
      | ~ r2_hidden(C_674,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6626,c_6652])).

tff(c_6657,plain,(
    ! [C_674] : ~ r2_hidden(C_674,'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6629,c_6655])).

tff(c_7405,plain,(
    ! [A_753,C_754] :
      ( r2_hidden('#skF_5'(A_753,'#skF_9',C_754),C_754)
      | k2_zfmisc_1(A_753,'#skF_9') = C_754 ) ),
    inference(resolution,[status(thm)],[c_7155,c_6657])).

tff(c_7494,plain,(
    ! [A_753] : k2_zfmisc_1(A_753,'#skF_9') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_7405,c_6657])).

tff(c_6627,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6624,c_5638])).

tff(c_7518,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7494,c_6627])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:06:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.07/1.98  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.07/1.99  
% 5.07/1.99  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.39/1.99  %$ r2_hidden > r1_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_11 > #skF_4 > #skF_10 > #skF_5 > #skF_2 > #skF_7 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_1
% 5.39/1.99  
% 5.39/1.99  %Foreground sorts:
% 5.39/1.99  
% 5.39/1.99  
% 5.39/1.99  %Background operators:
% 5.39/1.99  
% 5.39/1.99  
% 5.39/1.99  %Foreground operators:
% 5.39/1.99  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.39/1.99  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.39/1.99  tff('#skF_11', type, '#skF_11': $i).
% 5.39/1.99  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.39/1.99  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.39/1.99  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 5.39/1.99  tff('#skF_10', type, '#skF_10': $i).
% 5.39/1.99  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 5.39/1.99  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.39/1.99  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.39/1.99  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 5.39/1.99  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 5.39/1.99  tff('#skF_9', type, '#skF_9': $i).
% 5.39/1.99  tff('#skF_8', type, '#skF_8': $i).
% 5.39/1.99  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.39/1.99  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.39/1.99  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 5.39/1.99  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.39/1.99  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.39/1.99  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.39/1.99  
% 5.39/2.01  tff(f_55, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 5.39/2.01  tff(f_62, negated_conjecture, ~(![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.39/2.01  tff(f_43, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 5.39/2.01  tff(f_41, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 5.39/2.01  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 5.39/2.01  tff(c_7155, plain, (![A_742, B_743, C_744]: (r2_hidden('#skF_4'(A_742, B_743, C_744), B_743) | r2_hidden('#skF_5'(A_742, B_743, C_744), C_744) | k2_zfmisc_1(A_742, B_743)=C_744)), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.39/2.01  tff(c_6176, plain, (![A_653, B_654, C_655]: (r2_hidden('#skF_4'(A_653, B_654, C_655), B_654) | r2_hidden('#skF_5'(A_653, B_654, C_655), C_655) | k2_zfmisc_1(A_653, B_654)=C_655)), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.39/2.01  tff(c_5001, plain, (![A_540, B_541, C_542]: (r2_hidden('#skF_3'(A_540, B_541, C_542), A_540) | r2_hidden('#skF_5'(A_540, B_541, C_542), C_542) | k2_zfmisc_1(A_540, B_541)=C_542)), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.39/2.01  tff(c_4029, plain, (![A_444, B_445, C_446]: (r2_hidden('#skF_4'(A_444, B_445, C_446), B_445) | r2_hidden('#skF_5'(A_444, B_445, C_446), C_446) | k2_zfmisc_1(A_444, B_445)=C_446)), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.39/2.01  tff(c_3480, plain, (![A_391, B_392, C_393]: (r2_hidden('#skF_3'(A_391, B_392, C_393), A_391) | r2_hidden('#skF_5'(A_391, B_392, C_393), C_393) | k2_zfmisc_1(A_391, B_392)=C_393)), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.39/2.01  tff(c_2182, plain, (![A_274, B_275, C_276]: (r2_hidden('#skF_4'(A_274, B_275, C_276), B_275) | r2_hidden('#skF_5'(A_274, B_275, C_276), C_276) | k2_zfmisc_1(A_274, B_275)=C_276)), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.39/2.01  tff(c_36, plain, (k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0!='#skF_11'), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.39/2.01  tff(c_54, plain, (k1_xboole_0!='#skF_11'), inference(splitLeft, [status(thm)], [c_36])).
% 5.39/2.01  tff(c_1274, plain, (![A_193, B_194, C_195]: (r2_hidden('#skF_4'(A_193, B_194, C_195), B_194) | r2_hidden('#skF_5'(A_193, B_194, C_195), C_195) | k2_zfmisc_1(A_193, B_194)=C_195)), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.39/2.01  tff(c_38, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!=k1_xboole_0 | k1_xboole_0!='#skF_10'), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.39/2.01  tff(c_53, plain, (k1_xboole_0!='#skF_10'), inference(splitLeft, [status(thm)], [c_38])).
% 5.39/2.01  tff(c_372, plain, (![A_105, B_106, C_107]: (r2_hidden('#skF_4'(A_105, B_106, C_107), B_106) | r2_hidden('#skF_5'(A_105, B_106, C_107), C_107) | k2_zfmisc_1(A_105, B_106)=C_107)), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.39/2.01  tff(c_8, plain, (![A_7]: (r1_xboole_0(A_7, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.39/2.01  tff(c_6, plain, (![A_6]: (k3_xboole_0(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.39/2.01  tff(c_61, plain, (![A_44, B_45, C_46]: (~r1_xboole_0(A_44, B_45) | ~r2_hidden(C_46, k3_xboole_0(A_44, B_45)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.39/2.01  tff(c_64, plain, (![A_6, C_46]: (~r1_xboole_0(A_6, k1_xboole_0) | ~r2_hidden(C_46, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_61])).
% 5.39/2.01  tff(c_66, plain, (![C_46]: (~r2_hidden(C_46, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_64])).
% 5.39/2.01  tff(c_44, plain, (k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8' | k2_zfmisc_1('#skF_10', '#skF_11')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.39/2.01  tff(c_55, plain, (k2_zfmisc_1('#skF_10', '#skF_11')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_44])).
% 5.39/2.01  tff(c_78, plain, (![E_50, F_51, A_52, B_53]: (r2_hidden(k4_tarski(E_50, F_51), k2_zfmisc_1(A_52, B_53)) | ~r2_hidden(F_51, B_53) | ~r2_hidden(E_50, A_52))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.39/2.01  tff(c_81, plain, (![E_50, F_51]: (r2_hidden(k4_tarski(E_50, F_51), k1_xboole_0) | ~r2_hidden(F_51, '#skF_11') | ~r2_hidden(E_50, '#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_55, c_78])).
% 5.39/2.01  tff(c_82, plain, (![F_51, E_50]: (~r2_hidden(F_51, '#skF_11') | ~r2_hidden(E_50, '#skF_10'))), inference(negUnitSimplification, [status(thm)], [c_66, c_81])).
% 5.39/2.01  tff(c_83, plain, (![E_50]: (~r2_hidden(E_50, '#skF_10'))), inference(splitLeft, [status(thm)], [c_82])).
% 5.39/2.01  tff(c_625, plain, (![A_120, C_121]: (r2_hidden('#skF_5'(A_120, '#skF_10', C_121), C_121) | k2_zfmisc_1(A_120, '#skF_10')=C_121)), inference(resolution, [status(thm)], [c_372, c_83])).
% 5.39/2.01  tff(c_728, plain, (![A_120]: (k2_zfmisc_1(A_120, '#skF_10')='#skF_10')), inference(resolution, [status(thm)], [c_625, c_83])).
% 5.39/2.01  tff(c_729, plain, (![A_120]: (k2_zfmisc_1(A_120, '#skF_10')=k1_xboole_0)), inference(resolution, [status(thm)], [c_625, c_66])).
% 5.39/2.01  tff(c_806, plain, (k1_xboole_0='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_728, c_729])).
% 5.39/2.01  tff(c_807, plain, $false, inference(negUnitSimplification, [status(thm)], [c_53, c_806])).
% 5.39/2.01  tff(c_808, plain, (![F_51]: (~r2_hidden(F_51, '#skF_11'))), inference(splitRight, [status(thm)], [c_82])).
% 5.39/2.01  tff(c_1584, plain, (![A_208, C_209]: (r2_hidden('#skF_5'(A_208, '#skF_11', C_209), C_209) | k2_zfmisc_1(A_208, '#skF_11')=C_209)), inference(resolution, [status(thm)], [c_1274, c_808])).
% 5.39/2.01  tff(c_1707, plain, (![A_208]: (k2_zfmisc_1(A_208, '#skF_11')='#skF_11')), inference(resolution, [status(thm)], [c_1584, c_808])).
% 5.39/2.01  tff(c_1716, plain, (k1_xboole_0='#skF_11'), inference(demodulation, [status(thm), theory('equality')], [c_1707, c_55])).
% 5.39/2.01  tff(c_1718, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_1716])).
% 5.39/2.01  tff(c_1719, plain, (k1_xboole_0='#skF_8' | k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_44])).
% 5.39/2.01  tff(c_1721, plain, (k1_xboole_0='#skF_9'), inference(splitLeft, [status(thm)], [c_1719])).
% 5.39/2.01  tff(c_1725, plain, (![A_7]: (r1_xboole_0(A_7, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_1721, c_8])).
% 5.39/2.01  tff(c_1724, plain, (![A_6]: (k3_xboole_0(A_6, '#skF_9')='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_1721, c_1721, c_6])).
% 5.39/2.01  tff(c_1739, plain, (![A_212, B_213, C_214]: (~r1_xboole_0(A_212, B_213) | ~r2_hidden(C_214, k3_xboole_0(A_212, B_213)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.39/2.01  tff(c_1742, plain, (![A_6, C_214]: (~r1_xboole_0(A_6, '#skF_9') | ~r2_hidden(C_214, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_1724, c_1739])).
% 5.39/2.01  tff(c_1744, plain, (![C_214]: (~r2_hidden(C_214, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_1725, c_1742])).
% 5.39/2.01  tff(c_2908, plain, (![A_317, C_318]: (r2_hidden('#skF_5'(A_317, '#skF_9', C_318), C_318) | k2_zfmisc_1(A_317, '#skF_9')=C_318)), inference(resolution, [status(thm)], [c_2182, c_1744])).
% 5.39/2.01  tff(c_2942, plain, (![A_317]: (k2_zfmisc_1(A_317, '#skF_9')='#skF_9')), inference(resolution, [status(thm)], [c_2908, c_1744])).
% 5.39/2.01  tff(c_1720, plain, (k2_zfmisc_1('#skF_10', '#skF_11')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_44])).
% 5.39/2.01  tff(c_1738, plain, (k2_zfmisc_1('#skF_10', '#skF_11')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_1721, c_1720])).
% 5.39/2.01  tff(c_42, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!=k1_xboole_0 | k2_zfmisc_1('#skF_10', '#skF_11')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.39/2.01  tff(c_1745, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!='#skF_9' | k2_zfmisc_1('#skF_10', '#skF_11')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_1721, c_1721, c_42])).
% 5.39/2.01  tff(c_1746, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!='#skF_9'), inference(negUnitSimplification, [status(thm)], [c_1738, c_1745])).
% 5.39/2.01  tff(c_2954, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2942, c_1746])).
% 5.39/2.01  tff(c_2955, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_1719])).
% 5.39/2.01  tff(c_2960, plain, (![A_7]: (r1_xboole_0(A_7, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_2955, c_8])).
% 5.39/2.01  tff(c_2959, plain, (![A_6]: (k3_xboole_0(A_6, '#skF_8')='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2955, c_2955, c_6])).
% 5.39/2.01  tff(c_2977, plain, (![A_321, B_322, C_323]: (~r1_xboole_0(A_321, B_322) | ~r2_hidden(C_323, k3_xboole_0(A_321, B_322)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.39/2.01  tff(c_2980, plain, (![A_6, C_323]: (~r1_xboole_0(A_6, '#skF_8') | ~r2_hidden(C_323, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_2959, c_2977])).
% 5.39/2.01  tff(c_2982, plain, (![C_323]: (~r2_hidden(C_323, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_2960, c_2980])).
% 5.39/2.01  tff(c_3730, plain, (![A_402, B_403]: (r2_hidden('#skF_3'(A_402, B_403, '#skF_8'), A_402) | k2_zfmisc_1(A_402, B_403)='#skF_8')), inference(resolution, [status(thm)], [c_3480, c_2982])).
% 5.39/2.01  tff(c_3819, plain, (![B_403]: (k2_zfmisc_1('#skF_8', B_403)='#skF_8')), inference(resolution, [status(thm)], [c_3730, c_2982])).
% 5.39/2.01  tff(c_2965, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!='#skF_8' | k2_zfmisc_1('#skF_10', '#skF_11')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_2955, c_2955, c_42])).
% 5.39/2.01  tff(c_2966, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!='#skF_8'), inference(splitLeft, [status(thm)], [c_2965])).
% 5.39/2.01  tff(c_3830, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3819, c_2966])).
% 5.39/2.01  tff(c_3831, plain, (k2_zfmisc_1('#skF_10', '#skF_11')='#skF_8'), inference(splitRight, [status(thm)], [c_2965])).
% 5.39/2.01  tff(c_3840, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3831, c_2955, c_1720])).
% 5.39/2.01  tff(c_3842, plain, (k1_xboole_0='#skF_11'), inference(splitRight, [status(thm)], [c_36])).
% 5.39/2.01  tff(c_3841, plain, (k1_xboole_0='#skF_8' | k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_36])).
% 5.39/2.01  tff(c_3851, plain, ('#skF_11'='#skF_8' | '#skF_11'='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_3842, c_3842, c_3841])).
% 5.39/2.01  tff(c_3852, plain, ('#skF_11'='#skF_9'), inference(splitLeft, [status(thm)], [c_3851])).
% 5.39/2.01  tff(c_3845, plain, (![A_7]: (r1_xboole_0(A_7, '#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_3842, c_8])).
% 5.39/2.01  tff(c_3853, plain, (![A_7]: (r1_xboole_0(A_7, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_3852, c_3845])).
% 5.39/2.01  tff(c_3844, plain, (![A_6]: (k3_xboole_0(A_6, '#skF_11')='#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_3842, c_3842, c_6])).
% 5.39/2.01  tff(c_3865, plain, (![A_6]: (k3_xboole_0(A_6, '#skF_9')='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_3852, c_3852, c_3844])).
% 5.39/2.01  tff(c_3877, plain, (![A_408, B_409, C_410]: (~r1_xboole_0(A_408, B_409) | ~r2_hidden(C_410, k3_xboole_0(A_408, B_409)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.39/2.01  tff(c_3880, plain, (![A_6, C_410]: (~r1_xboole_0(A_6, '#skF_9') | ~r2_hidden(C_410, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_3865, c_3877])).
% 5.39/2.01  tff(c_3882, plain, (![C_410]: (~r2_hidden(C_410, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_3853, c_3880])).
% 5.39/2.01  tff(c_4630, plain, (![A_489, C_490]: (r2_hidden('#skF_5'(A_489, '#skF_9', C_490), C_490) | k2_zfmisc_1(A_489, '#skF_9')=C_490)), inference(resolution, [status(thm)], [c_4029, c_3882])).
% 5.39/2.01  tff(c_4719, plain, (![A_489]: (k2_zfmisc_1(A_489, '#skF_9')='#skF_9')), inference(resolution, [status(thm)], [c_4630, c_3882])).
% 5.39/2.01  tff(c_3855, plain, (k1_xboole_0='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_3852, c_3842])).
% 5.39/2.01  tff(c_34, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!=k1_xboole_0 | k1_xboole_0!='#skF_11'), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.39/2.01  tff(c_3874, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_3855, c_3852, c_3855, c_34])).
% 5.39/2.01  tff(c_4731, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4719, c_3874])).
% 5.39/2.01  tff(c_4732, plain, ('#skF_11'='#skF_8'), inference(splitRight, [status(thm)], [c_3851])).
% 5.39/2.01  tff(c_4737, plain, (![A_7]: (r1_xboole_0(A_7, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_4732, c_3845])).
% 5.39/2.01  tff(c_4750, plain, (![A_6]: (k3_xboole_0(A_6, '#skF_8')='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_4732, c_4732, c_3844])).
% 5.39/2.01  tff(c_4761, plain, (![A_493, B_494, C_495]: (~r1_xboole_0(A_493, B_494) | ~r2_hidden(C_495, k3_xboole_0(A_493, B_494)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.39/2.01  tff(c_4764, plain, (![A_6, C_495]: (~r1_xboole_0(A_6, '#skF_8') | ~r2_hidden(C_495, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_4750, c_4761])).
% 5.39/2.01  tff(c_4766, plain, (![C_495]: (~r2_hidden(C_495, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_4737, c_4764])).
% 5.39/2.01  tff(c_5514, plain, (![A_574, B_575]: (r2_hidden('#skF_3'(A_574, B_575, '#skF_8'), A_574) | k2_zfmisc_1(A_574, B_575)='#skF_8')), inference(resolution, [status(thm)], [c_5001, c_4766])).
% 5.39/2.01  tff(c_5603, plain, (![B_575]: (k2_zfmisc_1('#skF_8', B_575)='#skF_8')), inference(resolution, [status(thm)], [c_5514, c_4766])).
% 5.39/2.01  tff(c_4735, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!='#skF_11'), inference(demodulation, [status(thm), theory('equality')], [c_3842, c_3842, c_34])).
% 5.39/2.01  tff(c_4736, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_4732, c_4735])).
% 5.39/2.01  tff(c_5626, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5603, c_4736])).
% 5.39/2.01  tff(c_5628, plain, (k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_38])).
% 5.39/2.01  tff(c_40, plain, (k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0!='#skF_10'), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.39/2.01  tff(c_5647, plain, ('#skF_10'='#skF_9' | '#skF_10'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_5628, c_5628, c_5628, c_40])).
% 5.39/2.01  tff(c_5648, plain, ('#skF_10'='#skF_8'), inference(splitLeft, [status(thm)], [c_5647])).
% 5.39/2.01  tff(c_5630, plain, (![A_7]: (r1_xboole_0(A_7, '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_5628, c_8])).
% 5.39/2.01  tff(c_5652, plain, (![A_7]: (r1_xboole_0(A_7, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_5648, c_5630])).
% 5.39/2.01  tff(c_5629, plain, (![A_6]: (k3_xboole_0(A_6, '#skF_10')='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_5628, c_5628, c_6])).
% 5.39/2.01  tff(c_5649, plain, (![A_6]: (k3_xboole_0(A_6, '#skF_8')='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_5648, c_5648, c_5629])).
% 5.39/2.01  tff(c_5673, plain, (![A_583, B_584, C_585]: (~r1_xboole_0(A_583, B_584) | ~r2_hidden(C_585, k3_xboole_0(A_583, B_584)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.39/2.01  tff(c_5676, plain, (![A_6, C_585]: (~r1_xboole_0(A_6, '#skF_8') | ~r2_hidden(C_585, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_5649, c_5673])).
% 5.39/2.01  tff(c_5678, plain, (![C_585]: (~r2_hidden(C_585, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_5652, c_5676])).
% 5.39/2.01  tff(c_6426, plain, (![A_664, C_665]: (r2_hidden('#skF_5'(A_664, '#skF_8', C_665), C_665) | k2_zfmisc_1(A_664, '#skF_8')=C_665)), inference(resolution, [status(thm)], [c_6176, c_5678])).
% 5.39/2.01  tff(c_6515, plain, (![A_664]: (k2_zfmisc_1(A_664, '#skF_8')='#skF_8')), inference(resolution, [status(thm)], [c_6426, c_5678])).
% 5.39/2.01  tff(c_5713, plain, (![A_598, B_599, D_600]: (r2_hidden('#skF_6'(A_598, B_599, k2_zfmisc_1(A_598, B_599), D_600), A_598) | ~r2_hidden(D_600, k2_zfmisc_1(A_598, B_599)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.39/2.01  tff(c_5727, plain, (![D_600, B_599]: (~r2_hidden(D_600, k2_zfmisc_1('#skF_8', B_599)))), inference(resolution, [status(thm)], [c_5713, c_5678])).
% 5.39/2.01  tff(c_6513, plain, (![A_664, B_599]: (k2_zfmisc_1(A_664, '#skF_8')=k2_zfmisc_1('#skF_8', B_599))), inference(resolution, [status(thm)], [c_6426, c_5727])).
% 5.39/2.01  tff(c_6609, plain, (![B_599]: (k2_zfmisc_1('#skF_8', B_599)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_6515, c_6513])).
% 5.39/2.01  tff(c_5627, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_38])).
% 5.39/2.01  tff(c_5638, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_5628, c_5627])).
% 5.39/2.01  tff(c_5650, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_5648, c_5638])).
% 5.39/2.01  tff(c_6623, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6609, c_5650])).
% 5.39/2.01  tff(c_6624, plain, ('#skF_10'='#skF_9'), inference(splitRight, [status(thm)], [c_5647])).
% 5.39/2.01  tff(c_6629, plain, (![A_7]: (r1_xboole_0(A_7, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_6624, c_5630])).
% 5.39/2.01  tff(c_6626, plain, (![A_6]: (k3_xboole_0(A_6, '#skF_9')='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_6624, c_6624, c_5629])).
% 5.39/2.01  tff(c_6652, plain, (![A_672, B_673, C_674]: (~r1_xboole_0(A_672, B_673) | ~r2_hidden(C_674, k3_xboole_0(A_672, B_673)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.39/2.01  tff(c_6655, plain, (![A_6, C_674]: (~r1_xboole_0(A_6, '#skF_9') | ~r2_hidden(C_674, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_6626, c_6652])).
% 5.39/2.01  tff(c_6657, plain, (![C_674]: (~r2_hidden(C_674, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_6629, c_6655])).
% 5.39/2.01  tff(c_7405, plain, (![A_753, C_754]: (r2_hidden('#skF_5'(A_753, '#skF_9', C_754), C_754) | k2_zfmisc_1(A_753, '#skF_9')=C_754)), inference(resolution, [status(thm)], [c_7155, c_6657])).
% 5.39/2.01  tff(c_7494, plain, (![A_753]: (k2_zfmisc_1(A_753, '#skF_9')='#skF_9')), inference(resolution, [status(thm)], [c_7405, c_6657])).
% 5.39/2.01  tff(c_6627, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_6624, c_5638])).
% 5.39/2.01  tff(c_7518, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7494, c_6627])).
% 5.39/2.01  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.39/2.01  
% 5.39/2.01  Inference rules
% 5.39/2.01  ----------------------
% 5.39/2.01  #Ref     : 0
% 5.39/2.01  #Sup     : 1470
% 5.39/2.01  #Fact    : 0
% 5.39/2.01  #Define  : 0
% 5.39/2.01  #Split   : 10
% 5.39/2.01  #Chain   : 0
% 5.39/2.01  #Close   : 0
% 5.39/2.01  
% 5.39/2.01  Ordering : KBO
% 5.39/2.01  
% 5.39/2.01  Simplification rules
% 5.39/2.01  ----------------------
% 5.39/2.01  #Subsume      : 459
% 5.39/2.01  #Demod        : 329
% 5.39/2.01  #Tautology    : 105
% 5.39/2.01  #SimpNegUnit  : 26
% 5.39/2.01  #BackRed      : 110
% 5.39/2.01  
% 5.39/2.01  #Partial instantiations: 0
% 5.39/2.01  #Strategies tried      : 1
% 5.39/2.01  
% 5.39/2.01  Timing (in seconds)
% 5.39/2.01  ----------------------
% 5.39/2.02  Preprocessing        : 0.29
% 5.39/2.02  Parsing              : 0.15
% 5.39/2.02  CNF conversion       : 0.02
% 5.39/2.02  Main loop            : 0.95
% 5.39/2.02  Inferencing          : 0.39
% 5.39/2.02  Reduction            : 0.25
% 5.39/2.02  Demodulation         : 0.14
% 5.39/2.02  BG Simplification    : 0.05
% 5.39/2.02  Subsumption          : 0.18
% 5.39/2.02  Abstraction          : 0.06
% 5.39/2.02  MUC search           : 0.00
% 5.39/2.02  Cooper               : 0.00
% 5.39/2.02  Total                : 1.29
% 5.39/2.02  Index Insertion      : 0.00
% 5.39/2.02  Index Deletion       : 0.00
% 5.39/2.02  Index Matching       : 0.00
% 5.39/2.02  BG Taut test         : 0.00
%------------------------------------------------------------------------------
