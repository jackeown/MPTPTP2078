%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:46 EST 2020

% Result     : Theorem 5.14s
% Output     : CNFRefutation 5.56s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 482 expanded)
%              Number of leaves         :   23 ( 150 expanded)
%              Depth                    :    9
%              Number of atoms          :  145 ( 944 expanded)
%              Number of equality atoms :   87 ( 765 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_10 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_5 > #skF_3

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(f_53,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_zfmisc_1(A,B) = k1_xboole_0
      <=> ( A = k1_xboole_0
          | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_27,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(c_6536,plain,(
    ! [A_742,B_743,C_744] :
      ( r2_hidden('#skF_2'(A_742,B_743,C_744),A_742)
      | r2_hidden('#skF_4'(A_742,B_743,C_744),C_744)
      | k2_zfmisc_1(A_742,B_743) = C_744 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4893,plain,(
    ! [A_581,B_582,C_583] :
      ( r2_hidden('#skF_3'(A_581,B_582,C_583),B_582)
      | r2_hidden('#skF_4'(A_581,B_582,C_583),C_583)
      | k2_zfmisc_1(A_581,B_582) = C_583 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_3587,plain,(
    ! [A_463,B_464,C_465] :
      ( r2_hidden('#skF_2'(A_463,B_464,C_465),A_463)
      | r2_hidden('#skF_4'(A_463,B_464,C_465),C_465)
      | k2_zfmisc_1(A_463,B_464) = C_465 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2339,plain,(
    ! [A_323,B_324,C_325] :
      ( r2_hidden('#skF_3'(A_323,B_324,C_325),B_324)
      | r2_hidden('#skF_4'(A_323,B_324,C_325),C_325)
      | k2_zfmisc_1(A_323,B_324) = C_325 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_34,plain,
    ( k2_zfmisc_1('#skF_7','#skF_8') != k1_xboole_0
    | k1_xboole_0 != '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_58,plain,(
    k1_xboole_0 != '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_1456,plain,(
    ! [A_242,B_243,C_244] :
      ( r2_hidden('#skF_3'(A_242,B_243,C_244),B_243)
      | r2_hidden('#skF_4'(A_242,B_243,C_244),C_244)
      | k2_zfmisc_1(A_242,B_243) = C_244 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_40,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_551,plain,(
    ! [A_148,B_149,C_150] :
      ( r2_hidden('#skF_2'(A_148,B_149,C_150),A_148)
      | r2_hidden('#skF_4'(A_148,B_149,C_150),C_150)
      | k2_zfmisc_1(A_148,B_149) = C_150 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2,plain,(
    ! [A_1] : k4_xboole_0(k1_xboole_0,A_1) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_53,plain,(
    ! [C_40,B_41] : ~ r2_hidden(C_40,k4_xboole_0(B_41,k1_tarski(C_40))) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_56,plain,(
    ! [C_40] : ~ r2_hidden(C_40,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_53])).

tff(c_44,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k2_zfmisc_1('#skF_9','#skF_10') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_59,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_87,plain,(
    ! [E_49,F_50,A_51,B_52] :
      ( r2_hidden(k4_tarski(E_49,F_50),k2_zfmisc_1(A_51,B_52))
      | ~ r2_hidden(F_50,B_52)
      | ~ r2_hidden(E_49,A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_90,plain,(
    ! [E_49,F_50] :
      ( r2_hidden(k4_tarski(E_49,F_50),k1_xboole_0)
      | ~ r2_hidden(F_50,'#skF_10')
      | ~ r2_hidden(E_49,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_87])).

tff(c_91,plain,(
    ! [F_50,E_49] :
      ( ~ r2_hidden(F_50,'#skF_10')
      | ~ r2_hidden(E_49,'#skF_9') ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_90])).

tff(c_118,plain,(
    ! [E_49] : ~ r2_hidden(E_49,'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_91])).

tff(c_908,plain,(
    ! [A_163,B_164] :
      ( r2_hidden('#skF_2'(A_163,B_164,'#skF_9'),A_163)
      | k2_zfmisc_1(A_163,B_164) = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_551,c_118])).

tff(c_1060,plain,(
    ! [B_164] : k2_zfmisc_1('#skF_9',B_164) = '#skF_9' ),
    inference(resolution,[status(thm)],[c_908,c_118])).

tff(c_1071,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1060,c_59])).

tff(c_1073,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1071])).

tff(c_1074,plain,(
    ! [F_50] : ~ r2_hidden(F_50,'#skF_10') ),
    inference(splitRight,[status(thm)],[c_91])).

tff(c_1783,plain,(
    ! [A_257,B_258] :
      ( r2_hidden('#skF_3'(A_257,B_258,'#skF_10'),B_258)
      | k2_zfmisc_1(A_257,B_258) = '#skF_10' ) ),
    inference(resolution,[status(thm)],[c_1456,c_1074])).

tff(c_1920,plain,(
    ! [A_257] : k2_zfmisc_1(A_257,'#skF_10') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_1783,c_1074])).

tff(c_1930,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1920,c_59])).

tff(c_1932,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1930])).

tff(c_1933,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1935,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_1933])).

tff(c_1937,plain,(
    ! [C_40] : ~ r2_hidden(C_40,'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1935,c_56])).

tff(c_2549,plain,(
    ! [A_334,B_335] :
      ( r2_hidden('#skF_3'(A_334,B_335,'#skF_8'),B_335)
      | k2_zfmisc_1(A_334,B_335) = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_2339,c_1937])).

tff(c_2629,plain,(
    ! [A_334] : k2_zfmisc_1(A_334,'#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_2549,c_1937])).

tff(c_1934,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1955,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1935,c_1934])).

tff(c_42,plain,
    ( k2_zfmisc_1('#skF_7','#skF_8') != k1_xboole_0
    | k2_zfmisc_1('#skF_9','#skF_10') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1956,plain,
    ( k2_zfmisc_1('#skF_7','#skF_8') != '#skF_8'
    | k2_zfmisc_1('#skF_9','#skF_10') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1935,c_1935,c_42])).

tff(c_1957,plain,(
    k2_zfmisc_1('#skF_7','#skF_8') != '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_1955,c_1956])).

tff(c_2639,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2629,c_1957])).

tff(c_2640,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_1933])).

tff(c_3349,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2640,c_1934])).

tff(c_2876,plain,(
    ! [A_389,B_390,C_391] :
      ( r2_hidden('#skF_2'(A_389,B_390,C_391),A_389)
      | r2_hidden('#skF_4'(A_389,B_390,C_391),C_391)
      | k2_zfmisc_1(A_389,B_390) = C_391 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2643,plain,(
    ! [C_40] : ~ r2_hidden(C_40,'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2640,c_56])).

tff(c_3098,plain,(
    ! [A_408,B_409] :
      ( r2_hidden('#skF_2'(A_408,B_409,'#skF_7'),A_408)
      | k2_zfmisc_1(A_408,B_409) = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_2876,c_2643])).

tff(c_3178,plain,(
    ! [B_409] : k2_zfmisc_1('#skF_7',B_409) = '#skF_7' ),
    inference(resolution,[status(thm)],[c_3098,c_2643])).

tff(c_2652,plain,
    ( k2_zfmisc_1('#skF_7','#skF_8') != '#skF_7'
    | k2_zfmisc_1('#skF_9','#skF_10') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2640,c_2640,c_42])).

tff(c_2653,plain,(
    k2_zfmisc_1('#skF_7','#skF_8') != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_2652])).

tff(c_3346,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3178,c_2653])).

tff(c_3347,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_2652])).

tff(c_3360,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3349,c_3347])).

tff(c_3362,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_3363,plain,(
    ! [C_40] : ~ r2_hidden(C_40,'#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3362,c_56])).

tff(c_4313,plain,(
    ! [A_505,B_506] :
      ( r2_hidden('#skF_2'(A_505,B_506,'#skF_10'),A_505)
      | k2_zfmisc_1(A_505,B_506) = '#skF_10' ) ),
    inference(resolution,[status(thm)],[c_3587,c_3363])).

tff(c_4338,plain,(
    ! [B_506] : k2_zfmisc_1('#skF_10',B_506) = '#skF_10' ),
    inference(resolution,[status(thm)],[c_4313,c_3363])).

tff(c_36,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 != '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_3383,plain,
    ( '#skF_10' = '#skF_8'
    | '#skF_7' = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3362,c_3362,c_3362,c_36])).

tff(c_3384,plain,(
    '#skF_7' = '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_3383])).

tff(c_3361,plain,(
    k2_zfmisc_1('#skF_7','#skF_8') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_3371,plain,(
    k2_zfmisc_1('#skF_7','#skF_8') != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3362,c_3361])).

tff(c_3385,plain,(
    k2_zfmisc_1('#skF_10','#skF_8') != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3384,c_3371])).

tff(c_4348,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4338,c_3385])).

tff(c_4349,plain,(
    '#skF_10' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_3383])).

tff(c_4353,plain,(
    ! [C_40] : ~ r2_hidden(C_40,'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4349,c_3363])).

tff(c_5295,plain,(
    ! [A_593,B_594] :
      ( r2_hidden('#skF_3'(A_593,B_594,'#skF_8'),B_594)
      | k2_zfmisc_1(A_593,B_594) = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_4893,c_4353])).

tff(c_5320,plain,(
    ! [A_593] : k2_zfmisc_1(A_593,'#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_5295,c_4353])).

tff(c_4352,plain,(
    k2_zfmisc_1('#skF_7','#skF_8') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4349,c_3371])).

tff(c_5333,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5320,c_4352])).

tff(c_5335,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_5336,plain,(
    ! [A_1] : k4_xboole_0('#skF_9',A_1) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5335,c_5335,c_2])).

tff(c_6349,plain,(
    ! [C_696,B_697] : ~ r2_hidden(C_696,k4_xboole_0(B_697,k1_tarski(C_696))) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_6352,plain,(
    ! [C_696] : ~ r2_hidden(C_696,'#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_5336,c_6349])).

tff(c_7276,plain,(
    ! [A_788,B_789] :
      ( r2_hidden('#skF_2'(A_788,B_789,'#skF_9'),A_788)
      | k2_zfmisc_1(A_788,B_789) = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_6536,c_6352])).

tff(c_7301,plain,(
    ! [B_789] : k2_zfmisc_1('#skF_9',B_789) = '#skF_9' ),
    inference(resolution,[status(thm)],[c_7276,c_6352])).

tff(c_5482,plain,(
    ! [A_630,B_631,C_632] :
      ( r2_hidden('#skF_3'(A_630,B_631,C_632),B_631)
      | r2_hidden('#skF_4'(A_630,B_631,C_632),C_632)
      | k2_zfmisc_1(A_630,B_631) = C_632 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_5334,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_5341,plain,
    ( '#skF_7' = '#skF_9'
    | '#skF_9' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5335,c_5335,c_5334])).

tff(c_5342,plain,(
    '#skF_9' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_5341])).

tff(c_5355,plain,(
    ! [A_1] : k4_xboole_0('#skF_8',A_1) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5342,c_5342,c_5336])).

tff(c_5366,plain,(
    ! [C_601,B_602] : ~ r2_hidden(C_601,k4_xboole_0(B_602,k1_tarski(C_601))) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_5369,plain,(
    ! [C_601] : ~ r2_hidden(C_601,'#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_5355,c_5366])).

tff(c_6294,plain,(
    ! [A_693,B_694] :
      ( r2_hidden('#skF_3'(A_693,B_694,'#skF_8'),B_694)
      | k2_zfmisc_1(A_693,B_694) = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_5482,c_5369])).

tff(c_6319,plain,(
    ! [A_693] : k2_zfmisc_1(A_693,'#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_6294,c_5369])).

tff(c_5345,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5342,c_5335])).

tff(c_38,plain,
    ( k2_zfmisc_1('#skF_7','#skF_8') != k1_xboole_0
    | k1_xboole_0 != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_5364,plain,(
    k2_zfmisc_1('#skF_7','#skF_8') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5345,c_5342,c_5345,c_38])).

tff(c_6329,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6319,c_5364])).

tff(c_6330,plain,(
    '#skF_7' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_5341])).

tff(c_6346,plain,(
    k2_zfmisc_1('#skF_9','#skF_8') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5335,c_6330,c_5335,c_38])).

tff(c_7311,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7301,c_6346])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 20:21:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.14/2.05  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.14/2.06  
% 5.14/2.06  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.14/2.06  %$ r2_hidden > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_10 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_5 > #skF_3
% 5.14/2.06  
% 5.14/2.06  %Foreground sorts:
% 5.14/2.06  
% 5.14/2.06  
% 5.14/2.06  %Background operators:
% 5.14/2.06  
% 5.14/2.06  
% 5.14/2.06  %Foreground operators:
% 5.14/2.06  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.14/2.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.14/2.06  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.14/2.06  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.14/2.06  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.14/2.06  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.14/2.06  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.14/2.06  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 5.14/2.06  tff('#skF_7', type, '#skF_7': $i).
% 5.14/2.06  tff('#skF_10', type, '#skF_10': $i).
% 5.14/2.06  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.14/2.06  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 5.14/2.06  tff('#skF_9', type, '#skF_9': $i).
% 5.14/2.06  tff('#skF_8', type, '#skF_8': $i).
% 5.14/2.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.14/2.06  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 5.14/2.06  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.14/2.06  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 5.14/2.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.14/2.06  
% 5.56/2.08  tff(f_39, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 5.56/2.08  tff(f_53, negated_conjecture, ~(![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.56/2.08  tff(f_27, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 5.56/2.08  tff(f_46, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 5.56/2.08  tff(c_6536, plain, (![A_742, B_743, C_744]: (r2_hidden('#skF_2'(A_742, B_743, C_744), A_742) | r2_hidden('#skF_4'(A_742, B_743, C_744), C_744) | k2_zfmisc_1(A_742, B_743)=C_744)), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.56/2.08  tff(c_4893, plain, (![A_581, B_582, C_583]: (r2_hidden('#skF_3'(A_581, B_582, C_583), B_582) | r2_hidden('#skF_4'(A_581, B_582, C_583), C_583) | k2_zfmisc_1(A_581, B_582)=C_583)), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.56/2.08  tff(c_3587, plain, (![A_463, B_464, C_465]: (r2_hidden('#skF_2'(A_463, B_464, C_465), A_463) | r2_hidden('#skF_4'(A_463, B_464, C_465), C_465) | k2_zfmisc_1(A_463, B_464)=C_465)), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.56/2.08  tff(c_2339, plain, (![A_323, B_324, C_325]: (r2_hidden('#skF_3'(A_323, B_324, C_325), B_324) | r2_hidden('#skF_4'(A_323, B_324, C_325), C_325) | k2_zfmisc_1(A_323, B_324)=C_325)), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.56/2.08  tff(c_34, plain, (k2_zfmisc_1('#skF_7', '#skF_8')!=k1_xboole_0 | k1_xboole_0!='#skF_10'), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.56/2.08  tff(c_58, plain, (k1_xboole_0!='#skF_10'), inference(splitLeft, [status(thm)], [c_34])).
% 5.56/2.08  tff(c_1456, plain, (![A_242, B_243, C_244]: (r2_hidden('#skF_3'(A_242, B_243, C_244), B_243) | r2_hidden('#skF_4'(A_242, B_243, C_244), C_244) | k2_zfmisc_1(A_242, B_243)=C_244)), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.56/2.08  tff(c_40, plain, (k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.56/2.08  tff(c_52, plain, (k1_xboole_0!='#skF_9'), inference(splitLeft, [status(thm)], [c_40])).
% 5.56/2.08  tff(c_551, plain, (![A_148, B_149, C_150]: (r2_hidden('#skF_2'(A_148, B_149, C_150), A_148) | r2_hidden('#skF_4'(A_148, B_149, C_150), C_150) | k2_zfmisc_1(A_148, B_149)=C_150)), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.56/2.08  tff(c_2, plain, (![A_1]: (k4_xboole_0(k1_xboole_0, A_1)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.56/2.08  tff(c_53, plain, (![C_40, B_41]: (~r2_hidden(C_40, k4_xboole_0(B_41, k1_tarski(C_40))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.56/2.08  tff(c_56, plain, (![C_40]: (~r2_hidden(C_40, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2, c_53])).
% 5.56/2.08  tff(c_44, plain, (k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k2_zfmisc_1('#skF_9', '#skF_10')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.56/2.08  tff(c_59, plain, (k2_zfmisc_1('#skF_9', '#skF_10')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_44])).
% 5.56/2.08  tff(c_87, plain, (![E_49, F_50, A_51, B_52]: (r2_hidden(k4_tarski(E_49, F_50), k2_zfmisc_1(A_51, B_52)) | ~r2_hidden(F_50, B_52) | ~r2_hidden(E_49, A_51))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.56/2.08  tff(c_90, plain, (![E_49, F_50]: (r2_hidden(k4_tarski(E_49, F_50), k1_xboole_0) | ~r2_hidden(F_50, '#skF_10') | ~r2_hidden(E_49, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_59, c_87])).
% 5.56/2.08  tff(c_91, plain, (![F_50, E_49]: (~r2_hidden(F_50, '#skF_10') | ~r2_hidden(E_49, '#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_56, c_90])).
% 5.56/2.08  tff(c_118, plain, (![E_49]: (~r2_hidden(E_49, '#skF_9'))), inference(splitLeft, [status(thm)], [c_91])).
% 5.56/2.08  tff(c_908, plain, (![A_163, B_164]: (r2_hidden('#skF_2'(A_163, B_164, '#skF_9'), A_163) | k2_zfmisc_1(A_163, B_164)='#skF_9')), inference(resolution, [status(thm)], [c_551, c_118])).
% 5.56/2.08  tff(c_1060, plain, (![B_164]: (k2_zfmisc_1('#skF_9', B_164)='#skF_9')), inference(resolution, [status(thm)], [c_908, c_118])).
% 5.56/2.08  tff(c_1071, plain, (k1_xboole_0='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_1060, c_59])).
% 5.56/2.08  tff(c_1073, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_1071])).
% 5.56/2.08  tff(c_1074, plain, (![F_50]: (~r2_hidden(F_50, '#skF_10'))), inference(splitRight, [status(thm)], [c_91])).
% 5.56/2.08  tff(c_1783, plain, (![A_257, B_258]: (r2_hidden('#skF_3'(A_257, B_258, '#skF_10'), B_258) | k2_zfmisc_1(A_257, B_258)='#skF_10')), inference(resolution, [status(thm)], [c_1456, c_1074])).
% 5.56/2.08  tff(c_1920, plain, (![A_257]: (k2_zfmisc_1(A_257, '#skF_10')='#skF_10')), inference(resolution, [status(thm)], [c_1783, c_1074])).
% 5.56/2.08  tff(c_1930, plain, (k1_xboole_0='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_1920, c_59])).
% 5.56/2.08  tff(c_1932, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_1930])).
% 5.56/2.08  tff(c_1933, plain, (k1_xboole_0='#skF_7' | k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_44])).
% 5.56/2.08  tff(c_1935, plain, (k1_xboole_0='#skF_8'), inference(splitLeft, [status(thm)], [c_1933])).
% 5.56/2.08  tff(c_1937, plain, (![C_40]: (~r2_hidden(C_40, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_1935, c_56])).
% 5.56/2.08  tff(c_2549, plain, (![A_334, B_335]: (r2_hidden('#skF_3'(A_334, B_335, '#skF_8'), B_335) | k2_zfmisc_1(A_334, B_335)='#skF_8')), inference(resolution, [status(thm)], [c_2339, c_1937])).
% 5.56/2.08  tff(c_2629, plain, (![A_334]: (k2_zfmisc_1(A_334, '#skF_8')='#skF_8')), inference(resolution, [status(thm)], [c_2549, c_1937])).
% 5.56/2.08  tff(c_1934, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_44])).
% 5.56/2.08  tff(c_1955, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_1935, c_1934])).
% 5.56/2.08  tff(c_42, plain, (k2_zfmisc_1('#skF_7', '#skF_8')!=k1_xboole_0 | k2_zfmisc_1('#skF_9', '#skF_10')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.56/2.08  tff(c_1956, plain, (k2_zfmisc_1('#skF_7', '#skF_8')!='#skF_8' | k2_zfmisc_1('#skF_9', '#skF_10')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_1935, c_1935, c_42])).
% 5.56/2.08  tff(c_1957, plain, (k2_zfmisc_1('#skF_7', '#skF_8')!='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_1955, c_1956])).
% 5.56/2.08  tff(c_2639, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2629, c_1957])).
% 5.56/2.08  tff(c_2640, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_1933])).
% 5.56/2.08  tff(c_3349, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_2640, c_1934])).
% 5.56/2.08  tff(c_2876, plain, (![A_389, B_390, C_391]: (r2_hidden('#skF_2'(A_389, B_390, C_391), A_389) | r2_hidden('#skF_4'(A_389, B_390, C_391), C_391) | k2_zfmisc_1(A_389, B_390)=C_391)), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.56/2.08  tff(c_2643, plain, (![C_40]: (~r2_hidden(C_40, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_2640, c_56])).
% 5.56/2.08  tff(c_3098, plain, (![A_408, B_409]: (r2_hidden('#skF_2'(A_408, B_409, '#skF_7'), A_408) | k2_zfmisc_1(A_408, B_409)='#skF_7')), inference(resolution, [status(thm)], [c_2876, c_2643])).
% 5.56/2.08  tff(c_3178, plain, (![B_409]: (k2_zfmisc_1('#skF_7', B_409)='#skF_7')), inference(resolution, [status(thm)], [c_3098, c_2643])).
% 5.56/2.08  tff(c_2652, plain, (k2_zfmisc_1('#skF_7', '#skF_8')!='#skF_7' | k2_zfmisc_1('#skF_9', '#skF_10')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_2640, c_2640, c_42])).
% 5.56/2.08  tff(c_2653, plain, (k2_zfmisc_1('#skF_7', '#skF_8')!='#skF_7'), inference(splitLeft, [status(thm)], [c_2652])).
% 5.56/2.08  tff(c_3346, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3178, c_2653])).
% 5.56/2.08  tff(c_3347, plain, (k2_zfmisc_1('#skF_9', '#skF_10')='#skF_7'), inference(splitRight, [status(thm)], [c_2652])).
% 5.56/2.08  tff(c_3360, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3349, c_3347])).
% 5.56/2.08  tff(c_3362, plain, (k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_34])).
% 5.56/2.08  tff(c_3363, plain, (![C_40]: (~r2_hidden(C_40, '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_3362, c_56])).
% 5.56/2.08  tff(c_4313, plain, (![A_505, B_506]: (r2_hidden('#skF_2'(A_505, B_506, '#skF_10'), A_505) | k2_zfmisc_1(A_505, B_506)='#skF_10')), inference(resolution, [status(thm)], [c_3587, c_3363])).
% 5.56/2.08  tff(c_4338, plain, (![B_506]: (k2_zfmisc_1('#skF_10', B_506)='#skF_10')), inference(resolution, [status(thm)], [c_4313, c_3363])).
% 5.56/2.08  tff(c_36, plain, (k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0!='#skF_10'), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.56/2.08  tff(c_3383, plain, ('#skF_10'='#skF_8' | '#skF_7'='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_3362, c_3362, c_3362, c_36])).
% 5.56/2.08  tff(c_3384, plain, ('#skF_7'='#skF_10'), inference(splitLeft, [status(thm)], [c_3383])).
% 5.56/2.08  tff(c_3361, plain, (k2_zfmisc_1('#skF_7', '#skF_8')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_34])).
% 5.56/2.08  tff(c_3371, plain, (k2_zfmisc_1('#skF_7', '#skF_8')!='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_3362, c_3361])).
% 5.56/2.08  tff(c_3385, plain, (k2_zfmisc_1('#skF_10', '#skF_8')!='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_3384, c_3371])).
% 5.56/2.08  tff(c_4348, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4338, c_3385])).
% 5.56/2.08  tff(c_4349, plain, ('#skF_10'='#skF_8'), inference(splitRight, [status(thm)], [c_3383])).
% 5.56/2.08  tff(c_4353, plain, (![C_40]: (~r2_hidden(C_40, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_4349, c_3363])).
% 5.56/2.08  tff(c_5295, plain, (![A_593, B_594]: (r2_hidden('#skF_3'(A_593, B_594, '#skF_8'), B_594) | k2_zfmisc_1(A_593, B_594)='#skF_8')), inference(resolution, [status(thm)], [c_4893, c_4353])).
% 5.56/2.08  tff(c_5320, plain, (![A_593]: (k2_zfmisc_1(A_593, '#skF_8')='#skF_8')), inference(resolution, [status(thm)], [c_5295, c_4353])).
% 5.56/2.08  tff(c_4352, plain, (k2_zfmisc_1('#skF_7', '#skF_8')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_4349, c_3371])).
% 5.56/2.08  tff(c_5333, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5320, c_4352])).
% 5.56/2.08  tff(c_5335, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_40])).
% 5.56/2.08  tff(c_5336, plain, (![A_1]: (k4_xboole_0('#skF_9', A_1)='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_5335, c_5335, c_2])).
% 5.56/2.08  tff(c_6349, plain, (![C_696, B_697]: (~r2_hidden(C_696, k4_xboole_0(B_697, k1_tarski(C_696))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.56/2.08  tff(c_6352, plain, (![C_696]: (~r2_hidden(C_696, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_5336, c_6349])).
% 5.56/2.08  tff(c_7276, plain, (![A_788, B_789]: (r2_hidden('#skF_2'(A_788, B_789, '#skF_9'), A_788) | k2_zfmisc_1(A_788, B_789)='#skF_9')), inference(resolution, [status(thm)], [c_6536, c_6352])).
% 5.56/2.08  tff(c_7301, plain, (![B_789]: (k2_zfmisc_1('#skF_9', B_789)='#skF_9')), inference(resolution, [status(thm)], [c_7276, c_6352])).
% 5.56/2.08  tff(c_5482, plain, (![A_630, B_631, C_632]: (r2_hidden('#skF_3'(A_630, B_631, C_632), B_631) | r2_hidden('#skF_4'(A_630, B_631, C_632), C_632) | k2_zfmisc_1(A_630, B_631)=C_632)), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.56/2.08  tff(c_5334, plain, (k1_xboole_0='#skF_7' | k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_40])).
% 5.56/2.08  tff(c_5341, plain, ('#skF_7'='#skF_9' | '#skF_9'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_5335, c_5335, c_5334])).
% 5.56/2.08  tff(c_5342, plain, ('#skF_9'='#skF_8'), inference(splitLeft, [status(thm)], [c_5341])).
% 5.56/2.08  tff(c_5355, plain, (![A_1]: (k4_xboole_0('#skF_8', A_1)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_5342, c_5342, c_5336])).
% 5.56/2.08  tff(c_5366, plain, (![C_601, B_602]: (~r2_hidden(C_601, k4_xboole_0(B_602, k1_tarski(C_601))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.56/2.08  tff(c_5369, plain, (![C_601]: (~r2_hidden(C_601, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_5355, c_5366])).
% 5.56/2.08  tff(c_6294, plain, (![A_693, B_694]: (r2_hidden('#skF_3'(A_693, B_694, '#skF_8'), B_694) | k2_zfmisc_1(A_693, B_694)='#skF_8')), inference(resolution, [status(thm)], [c_5482, c_5369])).
% 5.56/2.08  tff(c_6319, plain, (![A_693]: (k2_zfmisc_1(A_693, '#skF_8')='#skF_8')), inference(resolution, [status(thm)], [c_6294, c_5369])).
% 5.56/2.08  tff(c_5345, plain, (k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_5342, c_5335])).
% 5.56/2.08  tff(c_38, plain, (k2_zfmisc_1('#skF_7', '#skF_8')!=k1_xboole_0 | k1_xboole_0!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.56/2.08  tff(c_5364, plain, (k2_zfmisc_1('#skF_7', '#skF_8')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_5345, c_5342, c_5345, c_38])).
% 5.56/2.08  tff(c_6329, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6319, c_5364])).
% 5.56/2.08  tff(c_6330, plain, ('#skF_7'='#skF_9'), inference(splitRight, [status(thm)], [c_5341])).
% 5.56/2.08  tff(c_6346, plain, (k2_zfmisc_1('#skF_9', '#skF_8')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_5335, c_6330, c_5335, c_38])).
% 5.56/2.08  tff(c_7311, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7301, c_6346])).
% 5.56/2.08  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.56/2.08  
% 5.56/2.08  Inference rules
% 5.56/2.08  ----------------------
% 5.56/2.08  #Ref     : 0
% 5.56/2.08  #Sup     : 1455
% 5.56/2.08  #Fact    : 0
% 5.56/2.08  #Define  : 0
% 5.56/2.08  #Split   : 10
% 5.56/2.08  #Chain   : 0
% 5.56/2.08  #Close   : 0
% 5.56/2.08  
% 5.56/2.08  Ordering : KBO
% 5.56/2.08  
% 5.56/2.08  Simplification rules
% 5.56/2.08  ----------------------
% 5.56/2.08  #Subsume      : 426
% 5.56/2.08  #Demod        : 435
% 5.56/2.08  #Tautology    : 161
% 5.56/2.08  #SimpNegUnit  : 47
% 5.56/2.08  #BackRed      : 118
% 5.56/2.08  
% 5.56/2.08  #Partial instantiations: 0
% 5.56/2.08  #Strategies tried      : 1
% 5.56/2.08  
% 5.56/2.08  Timing (in seconds)
% 5.56/2.08  ----------------------
% 5.56/2.09  Preprocessing        : 0.33
% 5.56/2.09  Parsing              : 0.16
% 5.56/2.09  CNF conversion       : 0.03
% 5.56/2.09  Main loop            : 0.97
% 5.56/2.09  Inferencing          : 0.39
% 5.56/2.09  Reduction            : 0.26
% 5.56/2.09  Demodulation         : 0.15
% 5.56/2.09  BG Simplification    : 0.05
% 5.56/2.09  Subsumption          : 0.18
% 5.56/2.09  Abstraction          : 0.06
% 5.56/2.09  MUC search           : 0.00
% 5.56/2.09  Cooper               : 0.00
% 5.56/2.09  Total                : 1.34
% 5.56/2.09  Index Insertion      : 0.00
% 5.56/2.09  Index Deletion       : 0.00
% 5.56/2.09  Index Matching       : 0.00
% 5.56/2.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
