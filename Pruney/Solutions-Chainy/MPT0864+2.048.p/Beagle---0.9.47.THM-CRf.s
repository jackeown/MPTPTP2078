%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:15 EST 2020

% Result     : Theorem 5.66s
% Output     : CNFRefutation 5.73s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 483 expanded)
%              Number of leaves         :   38 ( 180 expanded)
%              Depth                    :   15
%              Number of atoms          :  160 ( 721 expanded)
%              Number of equality atoms :   97 ( 587 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_7 > #skF_1 > #skF_4 > #skF_10 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_5 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_7',type,(
    '#skF_7': $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

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

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_31,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_60,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_80,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).

tff(f_90,negated_conjecture,(
    ~ ! [A] :
        ( ? [B,C] : A = k4_tarski(B,C)
       => ( A != k1_mcart_1(A)
          & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k1_tarski(A),k2_tarski(B,C)) = k2_tarski(k4_tarski(A,B),k4_tarski(A,C))
      & k2_zfmisc_1(k2_tarski(A,B),k1_tarski(C)) = k2_tarski(k4_tarski(A,C),k4_tarski(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(c_4,plain,(
    ! [A_5] : k2_tarski(A_5,A_5) = k1_tarski(A_5) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_6,B_7] : k1_enumset1(A_6,A_6,B_7) = k2_tarski(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_8,B_9,C_10] : k2_enumset1(A_8,A_8,B_9,C_10) = k1_enumset1(A_8,B_9,C_10) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2185,plain,(
    ! [A_485,B_486,C_487,D_488] : k2_xboole_0(k1_enumset1(A_485,B_486,C_487),k1_tarski(D_488)) = k2_enumset1(A_485,B_486,C_487,D_488) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_2194,plain,(
    ! [A_6,B_7,D_488] : k2_xboole_0(k2_tarski(A_6,B_7),k1_tarski(D_488)) = k2_enumset1(A_6,A_6,B_7,D_488) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_2185])).

tff(c_2198,plain,(
    ! [A_489,B_490,D_491] : k2_xboole_0(k2_tarski(A_489,B_490),k1_tarski(D_491)) = k1_enumset1(A_489,B_490,D_491) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_2194])).

tff(c_2207,plain,(
    ! [A_5,D_491] : k2_xboole_0(k1_tarski(A_5),k1_tarski(D_491)) = k1_enumset1(A_5,A_5,D_491) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_2198])).

tff(c_2254,plain,(
    ! [A_495,D_496] : k2_xboole_0(k1_tarski(A_495),k1_tarski(D_496)) = k2_tarski(A_495,D_496) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_2207])).

tff(c_46,plain,(
    ! [A_65,B_66] : k2_xboole_0(k1_tarski(A_65),B_66) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2275,plain,(
    ! [A_497,D_498] : k2_tarski(A_497,D_498) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2254,c_46])).

tff(c_2279,plain,(
    ! [A_5] : k1_tarski(A_5) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_2275])).

tff(c_52,plain,(
    ! [A_69] :
      ( r2_hidden('#skF_7'(A_69),A_69)
      | k1_xboole_0 = A_69 ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_60,plain,(
    k4_tarski('#skF_9','#skF_10') = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_82,plain,(
    ! [A_85,B_86] : k1_mcart_1(k4_tarski(A_85,B_86)) = A_85 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_91,plain,(
    k1_mcart_1('#skF_8') = '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_82])).

tff(c_66,plain,(
    ! [A_83,B_84] : k2_mcart_1(k4_tarski(A_83,B_84)) = B_84 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_75,plain,(
    k2_mcart_1('#skF_8') = '#skF_10' ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_66])).

tff(c_58,plain,
    ( k2_mcart_1('#skF_8') = '#skF_8'
    | k1_mcart_1('#skF_8') = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_108,plain,
    ( '#skF_10' = '#skF_8'
    | '#skF_9' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_75,c_58])).

tff(c_109,plain,(
    '#skF_9' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_108])).

tff(c_111,plain,(
    k4_tarski('#skF_8','#skF_10') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_60])).

tff(c_203,plain,(
    ! [A_112,B_113,C_114,D_115] : k2_xboole_0(k1_enumset1(A_112,B_113,C_114),k1_tarski(D_115)) = k2_enumset1(A_112,B_113,C_114,D_115) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_212,plain,(
    ! [A_6,B_7,D_115] : k2_xboole_0(k2_tarski(A_6,B_7),k1_tarski(D_115)) = k2_enumset1(A_6,A_6,B_7,D_115) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_203])).

tff(c_216,plain,(
    ! [A_116,B_117,D_118] : k2_xboole_0(k2_tarski(A_116,B_117),k1_tarski(D_118)) = k1_enumset1(A_116,B_117,D_118) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_212])).

tff(c_225,plain,(
    ! [A_5,D_118] : k2_xboole_0(k1_tarski(A_5),k1_tarski(D_118)) = k1_enumset1(A_5,A_5,D_118) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_216])).

tff(c_229,plain,(
    ! [A_119,D_120] : k2_xboole_0(k1_tarski(A_119),k1_tarski(D_120)) = k2_tarski(A_119,D_120) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_225])).

tff(c_293,plain,(
    ! [A_124,D_125] : k2_tarski(A_124,D_125) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_229,c_46])).

tff(c_297,plain,(
    ! [A_5] : k1_tarski(A_5) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_293])).

tff(c_250,plain,(
    ! [A_121,B_122,C_123] : k2_zfmisc_1(k1_tarski(A_121),k2_tarski(B_122,C_123)) = k2_tarski(k4_tarski(A_121,B_122),k4_tarski(A_121,C_123)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_269,plain,(
    ! [A_121,C_123] : k2_zfmisc_1(k1_tarski(A_121),k2_tarski(C_123,C_123)) = k1_tarski(k4_tarski(A_121,C_123)) ),
    inference(superposition,[status(thm),theory(equality)],[c_250,c_4])).

tff(c_288,plain,(
    ! [A_121,C_123] : k2_zfmisc_1(k1_tarski(A_121),k1_tarski(C_123)) = k1_tarski(k4_tarski(A_121,C_123)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_269])).

tff(c_18,plain,(
    ! [A_26,B_27,D_53] :
      ( k4_tarski('#skF_5'(A_26,B_27,k2_zfmisc_1(A_26,B_27),D_53),'#skF_6'(A_26,B_27,k2_zfmisc_1(A_26,B_27),D_53)) = D_53
      | ~ r2_hidden(D_53,k2_zfmisc_1(A_26,B_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_501,plain,(
    ! [A_170,B_171,D_172] :
      ( r2_hidden('#skF_5'(A_170,B_171,k2_zfmisc_1(A_170,B_171),D_172),A_170)
      | ~ r2_hidden(D_172,k2_zfmisc_1(A_170,B_171)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_56,plain,(
    ! [C_77,A_69,D_78] :
      ( ~ r2_hidden(C_77,A_69)
      | k4_tarski(C_77,D_78) != '#skF_7'(A_69)
      | k1_xboole_0 = A_69 ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1953,plain,(
    ! [A_447,B_448,D_449,D_450] :
      ( k4_tarski('#skF_5'(A_447,B_448,k2_zfmisc_1(A_447,B_448),D_449),D_450) != '#skF_7'(A_447)
      | k1_xboole_0 = A_447
      | ~ r2_hidden(D_449,k2_zfmisc_1(A_447,B_448)) ) ),
    inference(resolution,[status(thm)],[c_501,c_56])).

tff(c_1983,plain,(
    ! [D_452,A_453,B_454] :
      ( D_452 != '#skF_7'(A_453)
      | k1_xboole_0 = A_453
      | ~ r2_hidden(D_452,k2_zfmisc_1(A_453,B_454))
      | ~ r2_hidden(D_452,k2_zfmisc_1(A_453,B_454)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_1953])).

tff(c_2007,plain,(
    ! [D_452,A_121,C_123] :
      ( D_452 != '#skF_7'(k1_tarski(A_121))
      | k1_tarski(A_121) = k1_xboole_0
      | ~ r2_hidden(D_452,k1_tarski(k4_tarski(A_121,C_123)))
      | ~ r2_hidden(D_452,k2_zfmisc_1(k1_tarski(A_121),k1_tarski(C_123))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_288,c_1983])).

tff(c_2021,plain,(
    ! [D_452,A_121,C_123] :
      ( D_452 != '#skF_7'(k1_tarski(A_121))
      | k1_tarski(A_121) = k1_xboole_0
      | ~ r2_hidden(D_452,k1_tarski(k4_tarski(A_121,C_123)))
      | ~ r2_hidden(D_452,k1_tarski(k4_tarski(A_121,C_123))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_288,c_2007])).

tff(c_2046,plain,(
    ! [D_459,A_460,C_461] :
      ( D_459 != '#skF_7'(k1_tarski(A_460))
      | ~ r2_hidden(D_459,k1_tarski(k4_tarski(A_460,C_461)))
      | ~ r2_hidden(D_459,k1_tarski(k4_tarski(A_460,C_461))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_297,c_2021])).

tff(c_2072,plain,(
    ! [D_459] :
      ( D_459 != '#skF_7'(k1_tarski('#skF_8'))
      | ~ r2_hidden(D_459,k1_tarski('#skF_8'))
      | ~ r2_hidden(D_459,k1_tarski(k4_tarski('#skF_8','#skF_10'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_2046])).

tff(c_2087,plain,(
    ~ r2_hidden('#skF_7'(k1_tarski('#skF_8')),k1_tarski('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_2072])).

tff(c_612,plain,(
    ! [A_216,B_217,D_218] :
      ( r2_hidden('#skF_6'(A_216,B_217,k2_zfmisc_1(A_216,B_217),D_218),B_217)
      | ~ r2_hidden(D_218,k2_zfmisc_1(A_216,B_217)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_54,plain,(
    ! [D_78,A_69,C_77] :
      ( ~ r2_hidden(D_78,A_69)
      | k4_tarski(C_77,D_78) != '#skF_7'(A_69)
      | k1_xboole_0 = A_69 ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1619,plain,(
    ! [C_424,A_425,B_426,D_427] :
      ( k4_tarski(C_424,'#skF_6'(A_425,B_426,k2_zfmisc_1(A_425,B_426),D_427)) != '#skF_7'(B_426)
      | k1_xboole_0 = B_426
      | ~ r2_hidden(D_427,k2_zfmisc_1(A_425,B_426)) ) ),
    inference(resolution,[status(thm)],[c_612,c_54])).

tff(c_1643,plain,(
    ! [D_428,B_429,A_430] :
      ( D_428 != '#skF_7'(B_429)
      | k1_xboole_0 = B_429
      | ~ r2_hidden(D_428,k2_zfmisc_1(A_430,B_429))
      | ~ r2_hidden(D_428,k2_zfmisc_1(A_430,B_429)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_1619])).

tff(c_1675,plain,(
    ! [D_428,C_123,A_121] :
      ( D_428 != '#skF_7'(k1_tarski(C_123))
      | k1_tarski(C_123) = k1_xboole_0
      | ~ r2_hidden(D_428,k1_tarski(k4_tarski(A_121,C_123)))
      | ~ r2_hidden(D_428,k2_zfmisc_1(k1_tarski(A_121),k1_tarski(C_123))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_288,c_1643])).

tff(c_1692,plain,(
    ! [D_428,C_123,A_121] :
      ( D_428 != '#skF_7'(k1_tarski(C_123))
      | k1_tarski(C_123) = k1_xboole_0
      | ~ r2_hidden(D_428,k1_tarski(k4_tarski(A_121,C_123)))
      | ~ r2_hidden(D_428,k1_tarski(k4_tarski(A_121,C_123))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_288,c_1675])).

tff(c_1697,plain,(
    ! [D_431,C_432,A_433] :
      ( D_431 != '#skF_7'(k1_tarski(C_432))
      | ~ r2_hidden(D_431,k1_tarski(k4_tarski(A_433,C_432)))
      | ~ r2_hidden(D_431,k1_tarski(k4_tarski(A_433,C_432))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_297,c_1692])).

tff(c_1731,plain,(
    ! [D_431] :
      ( D_431 != '#skF_7'(k1_tarski('#skF_10'))
      | ~ r2_hidden(D_431,k1_tarski('#skF_8'))
      | ~ r2_hidden(D_431,k1_tarski(k4_tarski('#skF_8','#skF_10'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_1697])).

tff(c_1750,plain,(
    ! [D_434] :
      ( D_434 != '#skF_7'(k1_tarski('#skF_10'))
      | ~ r2_hidden(D_434,k1_tarski('#skF_8'))
      | ~ r2_hidden(D_434,k1_tarski('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_1731])).

tff(c_1779,plain,
    ( '#skF_7'(k1_tarski('#skF_10')) != '#skF_7'(k1_tarski('#skF_8'))
    | ~ r2_hidden('#skF_7'(k1_tarski('#skF_8')),k1_tarski('#skF_8'))
    | k1_tarski('#skF_8') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_52,c_1750])).

tff(c_1791,plain,
    ( '#skF_7'(k1_tarski('#skF_10')) != '#skF_7'(k1_tarski('#skF_8'))
    | ~ r2_hidden('#skF_7'(k1_tarski('#skF_8')),k1_tarski('#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_297,c_1779])).

tff(c_1799,plain,(
    ~ r2_hidden('#skF_7'(k1_tarski('#skF_8')),k1_tarski('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_1791])).

tff(c_1802,plain,(
    k1_tarski('#skF_8') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_52,c_1799])).

tff(c_1806,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_297,c_1802])).

tff(c_1808,plain,(
    r2_hidden('#skF_7'(k1_tarski('#skF_8')),k1_tarski('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_1791])).

tff(c_2089,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2087,c_1808])).

tff(c_2090,plain,(
    '#skF_10' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_108])).

tff(c_2093,plain,(
    k4_tarski('#skF_9','#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2090,c_60])).

tff(c_2211,plain,(
    ! [A_492,B_493,C_494] : k2_zfmisc_1(k1_tarski(A_492),k2_tarski(B_493,C_494)) = k2_tarski(k4_tarski(A_492,B_493),k4_tarski(A_492,C_494)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2230,plain,(
    ! [A_492,C_494] : k2_zfmisc_1(k1_tarski(A_492),k2_tarski(C_494,C_494)) = k1_tarski(k4_tarski(A_492,C_494)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2211,c_4])).

tff(c_2249,plain,(
    ! [A_492,C_494] : k2_zfmisc_1(k1_tarski(A_492),k1_tarski(C_494)) = k1_tarski(k4_tarski(A_492,C_494)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_2230])).

tff(c_2501,plain,(
    ! [A_556,B_557,D_558] :
      ( r2_hidden('#skF_6'(A_556,B_557,k2_zfmisc_1(A_556,B_557),D_558),B_557)
      | ~ r2_hidden(D_558,k2_zfmisc_1(A_556,B_557)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_3541,plain,(
    ! [C_790,A_791,B_792,D_793] :
      ( k4_tarski(C_790,'#skF_6'(A_791,B_792,k2_zfmisc_1(A_791,B_792),D_793)) != '#skF_7'(B_792)
      | k1_xboole_0 = B_792
      | ~ r2_hidden(D_793,k2_zfmisc_1(A_791,B_792)) ) ),
    inference(resolution,[status(thm)],[c_2501,c_54])).

tff(c_3565,plain,(
    ! [D_794,B_795,A_796] :
      ( D_794 != '#skF_7'(B_795)
      | k1_xboole_0 = B_795
      | ~ r2_hidden(D_794,k2_zfmisc_1(A_796,B_795))
      | ~ r2_hidden(D_794,k2_zfmisc_1(A_796,B_795)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_3541])).

tff(c_3593,plain,(
    ! [D_794,C_494,A_492] :
      ( D_794 != '#skF_7'(k1_tarski(C_494))
      | k1_tarski(C_494) = k1_xboole_0
      | ~ r2_hidden(D_794,k1_tarski(k4_tarski(A_492,C_494)))
      | ~ r2_hidden(D_794,k2_zfmisc_1(k1_tarski(A_492),k1_tarski(C_494))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2249,c_3565])).

tff(c_3612,plain,(
    ! [D_794,C_494,A_492] :
      ( D_794 != '#skF_7'(k1_tarski(C_494))
      | k1_tarski(C_494) = k1_xboole_0
      | ~ r2_hidden(D_794,k1_tarski(k4_tarski(A_492,C_494)))
      | ~ r2_hidden(D_794,k1_tarski(k4_tarski(A_492,C_494))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2249,c_3593])).

tff(c_3638,plain,(
    ! [D_800,C_801,A_802] :
      ( D_800 != '#skF_7'(k1_tarski(C_801))
      | ~ r2_hidden(D_800,k1_tarski(k4_tarski(A_802,C_801)))
      | ~ r2_hidden(D_800,k1_tarski(k4_tarski(A_802,C_801))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_2279,c_3612])).

tff(c_3664,plain,(
    ! [D_800] :
      ( D_800 != '#skF_7'(k1_tarski('#skF_8'))
      | ~ r2_hidden(D_800,k1_tarski('#skF_8'))
      | ~ r2_hidden(D_800,k1_tarski(k4_tarski('#skF_9','#skF_8'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2093,c_3638])).

tff(c_3680,plain,(
    ! [D_803] :
      ( D_803 != '#skF_7'(k1_tarski('#skF_8'))
      | ~ r2_hidden(D_803,k1_tarski('#skF_8'))
      | ~ r2_hidden(D_803,k1_tarski('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2093,c_3664])).

tff(c_3703,plain,
    ( ~ r2_hidden('#skF_7'(k1_tarski('#skF_8')),k1_tarski('#skF_8'))
    | k1_tarski('#skF_8') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_52,c_3680])).

tff(c_3713,plain,(
    ~ r2_hidden('#skF_7'(k1_tarski('#skF_8')),k1_tarski('#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_2279,c_3703])).

tff(c_3716,plain,(
    k1_tarski('#skF_8') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_52,c_3713])).

tff(c_3720,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2279,c_3716])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:31:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.66/2.05  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.73/2.06  
% 5.73/2.06  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.73/2.07  %$ r2_hidden > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_7 > #skF_1 > #skF_4 > #skF_10 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_5 > #skF_3
% 5.73/2.07  
% 5.73/2.07  %Foreground sorts:
% 5.73/2.07  
% 5.73/2.07  
% 5.73/2.07  %Background operators:
% 5.73/2.07  
% 5.73/2.07  
% 5.73/2.07  %Foreground operators:
% 5.73/2.07  tff('#skF_7', type, '#skF_7': $i > $i).
% 5.73/2.07  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.73/2.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.73/2.07  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.73/2.07  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.73/2.07  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.73/2.07  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.73/2.07  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.73/2.07  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 5.73/2.07  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.73/2.07  tff('#skF_10', type, '#skF_10': $i).
% 5.73/2.07  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.73/2.07  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.73/2.07  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.73/2.07  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 5.73/2.07  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.73/2.07  tff('#skF_9', type, '#skF_9': $i).
% 5.73/2.07  tff('#skF_8', type, '#skF_8': $i).
% 5.73/2.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.73/2.07  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 5.73/2.07  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.73/2.07  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 5.73/2.07  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.73/2.07  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 5.73/2.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.73/2.07  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 5.73/2.07  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.73/2.07  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.73/2.07  
% 5.73/2.08  tff(f_29, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 5.73/2.08  tff(f_31, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 5.73/2.08  tff(f_33, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 5.73/2.08  tff(f_27, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 5.73/2.08  tff(f_60, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 5.73/2.08  tff(f_80, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_mcart_1)).
% 5.73/2.08  tff(f_90, negated_conjecture, ~(![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_mcart_1)).
% 5.73/2.08  tff(f_64, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 5.73/2.08  tff(f_57, axiom, (![A, B, C]: ((k2_zfmisc_1(k1_tarski(A), k2_tarski(B, C)) = k2_tarski(k4_tarski(A, B), k4_tarski(A, C))) & (k2_zfmisc_1(k2_tarski(A, B), k1_tarski(C)) = k2_tarski(k4_tarski(A, C), k4_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_zfmisc_1)).
% 5.73/2.08  tff(f_51, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 5.73/2.08  tff(c_4, plain, (![A_5]: (k2_tarski(A_5, A_5)=k1_tarski(A_5))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.73/2.08  tff(c_6, plain, (![A_6, B_7]: (k1_enumset1(A_6, A_6, B_7)=k2_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.73/2.08  tff(c_8, plain, (![A_8, B_9, C_10]: (k2_enumset1(A_8, A_8, B_9, C_10)=k1_enumset1(A_8, B_9, C_10))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.73/2.08  tff(c_2185, plain, (![A_485, B_486, C_487, D_488]: (k2_xboole_0(k1_enumset1(A_485, B_486, C_487), k1_tarski(D_488))=k2_enumset1(A_485, B_486, C_487, D_488))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.73/2.08  tff(c_2194, plain, (![A_6, B_7, D_488]: (k2_xboole_0(k2_tarski(A_6, B_7), k1_tarski(D_488))=k2_enumset1(A_6, A_6, B_7, D_488))), inference(superposition, [status(thm), theory('equality')], [c_6, c_2185])).
% 5.73/2.08  tff(c_2198, plain, (![A_489, B_490, D_491]: (k2_xboole_0(k2_tarski(A_489, B_490), k1_tarski(D_491))=k1_enumset1(A_489, B_490, D_491))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_2194])).
% 5.73/2.08  tff(c_2207, plain, (![A_5, D_491]: (k2_xboole_0(k1_tarski(A_5), k1_tarski(D_491))=k1_enumset1(A_5, A_5, D_491))), inference(superposition, [status(thm), theory('equality')], [c_4, c_2198])).
% 5.73/2.08  tff(c_2254, plain, (![A_495, D_496]: (k2_xboole_0(k1_tarski(A_495), k1_tarski(D_496))=k2_tarski(A_495, D_496))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_2207])).
% 5.73/2.08  tff(c_46, plain, (![A_65, B_66]: (k2_xboole_0(k1_tarski(A_65), B_66)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.73/2.08  tff(c_2275, plain, (![A_497, D_498]: (k2_tarski(A_497, D_498)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2254, c_46])).
% 5.73/2.08  tff(c_2279, plain, (![A_5]: (k1_tarski(A_5)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4, c_2275])).
% 5.73/2.08  tff(c_52, plain, (![A_69]: (r2_hidden('#skF_7'(A_69), A_69) | k1_xboole_0=A_69)), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.73/2.08  tff(c_60, plain, (k4_tarski('#skF_9', '#skF_10')='#skF_8'), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.73/2.08  tff(c_82, plain, (![A_85, B_86]: (k1_mcart_1(k4_tarski(A_85, B_86))=A_85)), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.73/2.08  tff(c_91, plain, (k1_mcart_1('#skF_8')='#skF_9'), inference(superposition, [status(thm), theory('equality')], [c_60, c_82])).
% 5.73/2.08  tff(c_66, plain, (![A_83, B_84]: (k2_mcart_1(k4_tarski(A_83, B_84))=B_84)), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.73/2.08  tff(c_75, plain, (k2_mcart_1('#skF_8')='#skF_10'), inference(superposition, [status(thm), theory('equality')], [c_60, c_66])).
% 5.73/2.08  tff(c_58, plain, (k2_mcart_1('#skF_8')='#skF_8' | k1_mcart_1('#skF_8')='#skF_8'), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.73/2.08  tff(c_108, plain, ('#skF_10'='#skF_8' | '#skF_9'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_91, c_75, c_58])).
% 5.73/2.08  tff(c_109, plain, ('#skF_9'='#skF_8'), inference(splitLeft, [status(thm)], [c_108])).
% 5.73/2.08  tff(c_111, plain, (k4_tarski('#skF_8', '#skF_10')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_109, c_60])).
% 5.73/2.08  tff(c_203, plain, (![A_112, B_113, C_114, D_115]: (k2_xboole_0(k1_enumset1(A_112, B_113, C_114), k1_tarski(D_115))=k2_enumset1(A_112, B_113, C_114, D_115))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.73/2.08  tff(c_212, plain, (![A_6, B_7, D_115]: (k2_xboole_0(k2_tarski(A_6, B_7), k1_tarski(D_115))=k2_enumset1(A_6, A_6, B_7, D_115))), inference(superposition, [status(thm), theory('equality')], [c_6, c_203])).
% 5.73/2.08  tff(c_216, plain, (![A_116, B_117, D_118]: (k2_xboole_0(k2_tarski(A_116, B_117), k1_tarski(D_118))=k1_enumset1(A_116, B_117, D_118))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_212])).
% 5.73/2.08  tff(c_225, plain, (![A_5, D_118]: (k2_xboole_0(k1_tarski(A_5), k1_tarski(D_118))=k1_enumset1(A_5, A_5, D_118))), inference(superposition, [status(thm), theory('equality')], [c_4, c_216])).
% 5.73/2.08  tff(c_229, plain, (![A_119, D_120]: (k2_xboole_0(k1_tarski(A_119), k1_tarski(D_120))=k2_tarski(A_119, D_120))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_225])).
% 5.73/2.08  tff(c_293, plain, (![A_124, D_125]: (k2_tarski(A_124, D_125)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_229, c_46])).
% 5.73/2.08  tff(c_297, plain, (![A_5]: (k1_tarski(A_5)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4, c_293])).
% 5.73/2.08  tff(c_250, plain, (![A_121, B_122, C_123]: (k2_zfmisc_1(k1_tarski(A_121), k2_tarski(B_122, C_123))=k2_tarski(k4_tarski(A_121, B_122), k4_tarski(A_121, C_123)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.73/2.08  tff(c_269, plain, (![A_121, C_123]: (k2_zfmisc_1(k1_tarski(A_121), k2_tarski(C_123, C_123))=k1_tarski(k4_tarski(A_121, C_123)))), inference(superposition, [status(thm), theory('equality')], [c_250, c_4])).
% 5.73/2.08  tff(c_288, plain, (![A_121, C_123]: (k2_zfmisc_1(k1_tarski(A_121), k1_tarski(C_123))=k1_tarski(k4_tarski(A_121, C_123)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_269])).
% 5.73/2.08  tff(c_18, plain, (![A_26, B_27, D_53]: (k4_tarski('#skF_5'(A_26, B_27, k2_zfmisc_1(A_26, B_27), D_53), '#skF_6'(A_26, B_27, k2_zfmisc_1(A_26, B_27), D_53))=D_53 | ~r2_hidden(D_53, k2_zfmisc_1(A_26, B_27)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.73/2.08  tff(c_501, plain, (![A_170, B_171, D_172]: (r2_hidden('#skF_5'(A_170, B_171, k2_zfmisc_1(A_170, B_171), D_172), A_170) | ~r2_hidden(D_172, k2_zfmisc_1(A_170, B_171)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.73/2.08  tff(c_56, plain, (![C_77, A_69, D_78]: (~r2_hidden(C_77, A_69) | k4_tarski(C_77, D_78)!='#skF_7'(A_69) | k1_xboole_0=A_69)), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.73/2.08  tff(c_1953, plain, (![A_447, B_448, D_449, D_450]: (k4_tarski('#skF_5'(A_447, B_448, k2_zfmisc_1(A_447, B_448), D_449), D_450)!='#skF_7'(A_447) | k1_xboole_0=A_447 | ~r2_hidden(D_449, k2_zfmisc_1(A_447, B_448)))), inference(resolution, [status(thm)], [c_501, c_56])).
% 5.73/2.08  tff(c_1983, plain, (![D_452, A_453, B_454]: (D_452!='#skF_7'(A_453) | k1_xboole_0=A_453 | ~r2_hidden(D_452, k2_zfmisc_1(A_453, B_454)) | ~r2_hidden(D_452, k2_zfmisc_1(A_453, B_454)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_1953])).
% 5.73/2.08  tff(c_2007, plain, (![D_452, A_121, C_123]: (D_452!='#skF_7'(k1_tarski(A_121)) | k1_tarski(A_121)=k1_xboole_0 | ~r2_hidden(D_452, k1_tarski(k4_tarski(A_121, C_123))) | ~r2_hidden(D_452, k2_zfmisc_1(k1_tarski(A_121), k1_tarski(C_123))))), inference(superposition, [status(thm), theory('equality')], [c_288, c_1983])).
% 5.73/2.08  tff(c_2021, plain, (![D_452, A_121, C_123]: (D_452!='#skF_7'(k1_tarski(A_121)) | k1_tarski(A_121)=k1_xboole_0 | ~r2_hidden(D_452, k1_tarski(k4_tarski(A_121, C_123))) | ~r2_hidden(D_452, k1_tarski(k4_tarski(A_121, C_123))))), inference(demodulation, [status(thm), theory('equality')], [c_288, c_2007])).
% 5.73/2.08  tff(c_2046, plain, (![D_459, A_460, C_461]: (D_459!='#skF_7'(k1_tarski(A_460)) | ~r2_hidden(D_459, k1_tarski(k4_tarski(A_460, C_461))) | ~r2_hidden(D_459, k1_tarski(k4_tarski(A_460, C_461))))), inference(negUnitSimplification, [status(thm)], [c_297, c_2021])).
% 5.73/2.08  tff(c_2072, plain, (![D_459]: (D_459!='#skF_7'(k1_tarski('#skF_8')) | ~r2_hidden(D_459, k1_tarski('#skF_8')) | ~r2_hidden(D_459, k1_tarski(k4_tarski('#skF_8', '#skF_10'))))), inference(superposition, [status(thm), theory('equality')], [c_111, c_2046])).
% 5.73/2.08  tff(c_2087, plain, (~r2_hidden('#skF_7'(k1_tarski('#skF_8')), k1_tarski('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_2072])).
% 5.73/2.08  tff(c_612, plain, (![A_216, B_217, D_218]: (r2_hidden('#skF_6'(A_216, B_217, k2_zfmisc_1(A_216, B_217), D_218), B_217) | ~r2_hidden(D_218, k2_zfmisc_1(A_216, B_217)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.73/2.08  tff(c_54, plain, (![D_78, A_69, C_77]: (~r2_hidden(D_78, A_69) | k4_tarski(C_77, D_78)!='#skF_7'(A_69) | k1_xboole_0=A_69)), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.73/2.08  tff(c_1619, plain, (![C_424, A_425, B_426, D_427]: (k4_tarski(C_424, '#skF_6'(A_425, B_426, k2_zfmisc_1(A_425, B_426), D_427))!='#skF_7'(B_426) | k1_xboole_0=B_426 | ~r2_hidden(D_427, k2_zfmisc_1(A_425, B_426)))), inference(resolution, [status(thm)], [c_612, c_54])).
% 5.73/2.08  tff(c_1643, plain, (![D_428, B_429, A_430]: (D_428!='#skF_7'(B_429) | k1_xboole_0=B_429 | ~r2_hidden(D_428, k2_zfmisc_1(A_430, B_429)) | ~r2_hidden(D_428, k2_zfmisc_1(A_430, B_429)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_1619])).
% 5.73/2.08  tff(c_1675, plain, (![D_428, C_123, A_121]: (D_428!='#skF_7'(k1_tarski(C_123)) | k1_tarski(C_123)=k1_xboole_0 | ~r2_hidden(D_428, k1_tarski(k4_tarski(A_121, C_123))) | ~r2_hidden(D_428, k2_zfmisc_1(k1_tarski(A_121), k1_tarski(C_123))))), inference(superposition, [status(thm), theory('equality')], [c_288, c_1643])).
% 5.73/2.08  tff(c_1692, plain, (![D_428, C_123, A_121]: (D_428!='#skF_7'(k1_tarski(C_123)) | k1_tarski(C_123)=k1_xboole_0 | ~r2_hidden(D_428, k1_tarski(k4_tarski(A_121, C_123))) | ~r2_hidden(D_428, k1_tarski(k4_tarski(A_121, C_123))))), inference(demodulation, [status(thm), theory('equality')], [c_288, c_1675])).
% 5.73/2.08  tff(c_1697, plain, (![D_431, C_432, A_433]: (D_431!='#skF_7'(k1_tarski(C_432)) | ~r2_hidden(D_431, k1_tarski(k4_tarski(A_433, C_432))) | ~r2_hidden(D_431, k1_tarski(k4_tarski(A_433, C_432))))), inference(negUnitSimplification, [status(thm)], [c_297, c_1692])).
% 5.73/2.08  tff(c_1731, plain, (![D_431]: (D_431!='#skF_7'(k1_tarski('#skF_10')) | ~r2_hidden(D_431, k1_tarski('#skF_8')) | ~r2_hidden(D_431, k1_tarski(k4_tarski('#skF_8', '#skF_10'))))), inference(superposition, [status(thm), theory('equality')], [c_111, c_1697])).
% 5.73/2.08  tff(c_1750, plain, (![D_434]: (D_434!='#skF_7'(k1_tarski('#skF_10')) | ~r2_hidden(D_434, k1_tarski('#skF_8')) | ~r2_hidden(D_434, k1_tarski('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_1731])).
% 5.73/2.08  tff(c_1779, plain, ('#skF_7'(k1_tarski('#skF_10'))!='#skF_7'(k1_tarski('#skF_8')) | ~r2_hidden('#skF_7'(k1_tarski('#skF_8')), k1_tarski('#skF_8')) | k1_tarski('#skF_8')=k1_xboole_0), inference(resolution, [status(thm)], [c_52, c_1750])).
% 5.73/2.08  tff(c_1791, plain, ('#skF_7'(k1_tarski('#skF_10'))!='#skF_7'(k1_tarski('#skF_8')) | ~r2_hidden('#skF_7'(k1_tarski('#skF_8')), k1_tarski('#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_297, c_1779])).
% 5.73/2.08  tff(c_1799, plain, (~r2_hidden('#skF_7'(k1_tarski('#skF_8')), k1_tarski('#skF_8'))), inference(splitLeft, [status(thm)], [c_1791])).
% 5.73/2.08  tff(c_1802, plain, (k1_tarski('#skF_8')=k1_xboole_0), inference(resolution, [status(thm)], [c_52, c_1799])).
% 5.73/2.08  tff(c_1806, plain, $false, inference(negUnitSimplification, [status(thm)], [c_297, c_1802])).
% 5.73/2.08  tff(c_1808, plain, (r2_hidden('#skF_7'(k1_tarski('#skF_8')), k1_tarski('#skF_8'))), inference(splitRight, [status(thm)], [c_1791])).
% 5.73/2.08  tff(c_2089, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2087, c_1808])).
% 5.73/2.08  tff(c_2090, plain, ('#skF_10'='#skF_8'), inference(splitRight, [status(thm)], [c_108])).
% 5.73/2.08  tff(c_2093, plain, (k4_tarski('#skF_9', '#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_2090, c_60])).
% 5.73/2.08  tff(c_2211, plain, (![A_492, B_493, C_494]: (k2_zfmisc_1(k1_tarski(A_492), k2_tarski(B_493, C_494))=k2_tarski(k4_tarski(A_492, B_493), k4_tarski(A_492, C_494)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.73/2.08  tff(c_2230, plain, (![A_492, C_494]: (k2_zfmisc_1(k1_tarski(A_492), k2_tarski(C_494, C_494))=k1_tarski(k4_tarski(A_492, C_494)))), inference(superposition, [status(thm), theory('equality')], [c_2211, c_4])).
% 5.73/2.08  tff(c_2249, plain, (![A_492, C_494]: (k2_zfmisc_1(k1_tarski(A_492), k1_tarski(C_494))=k1_tarski(k4_tarski(A_492, C_494)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_2230])).
% 5.73/2.08  tff(c_2501, plain, (![A_556, B_557, D_558]: (r2_hidden('#skF_6'(A_556, B_557, k2_zfmisc_1(A_556, B_557), D_558), B_557) | ~r2_hidden(D_558, k2_zfmisc_1(A_556, B_557)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.73/2.08  tff(c_3541, plain, (![C_790, A_791, B_792, D_793]: (k4_tarski(C_790, '#skF_6'(A_791, B_792, k2_zfmisc_1(A_791, B_792), D_793))!='#skF_7'(B_792) | k1_xboole_0=B_792 | ~r2_hidden(D_793, k2_zfmisc_1(A_791, B_792)))), inference(resolution, [status(thm)], [c_2501, c_54])).
% 5.73/2.08  tff(c_3565, plain, (![D_794, B_795, A_796]: (D_794!='#skF_7'(B_795) | k1_xboole_0=B_795 | ~r2_hidden(D_794, k2_zfmisc_1(A_796, B_795)) | ~r2_hidden(D_794, k2_zfmisc_1(A_796, B_795)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_3541])).
% 5.73/2.08  tff(c_3593, plain, (![D_794, C_494, A_492]: (D_794!='#skF_7'(k1_tarski(C_494)) | k1_tarski(C_494)=k1_xboole_0 | ~r2_hidden(D_794, k1_tarski(k4_tarski(A_492, C_494))) | ~r2_hidden(D_794, k2_zfmisc_1(k1_tarski(A_492), k1_tarski(C_494))))), inference(superposition, [status(thm), theory('equality')], [c_2249, c_3565])).
% 5.73/2.08  tff(c_3612, plain, (![D_794, C_494, A_492]: (D_794!='#skF_7'(k1_tarski(C_494)) | k1_tarski(C_494)=k1_xboole_0 | ~r2_hidden(D_794, k1_tarski(k4_tarski(A_492, C_494))) | ~r2_hidden(D_794, k1_tarski(k4_tarski(A_492, C_494))))), inference(demodulation, [status(thm), theory('equality')], [c_2249, c_3593])).
% 5.73/2.08  tff(c_3638, plain, (![D_800, C_801, A_802]: (D_800!='#skF_7'(k1_tarski(C_801)) | ~r2_hidden(D_800, k1_tarski(k4_tarski(A_802, C_801))) | ~r2_hidden(D_800, k1_tarski(k4_tarski(A_802, C_801))))), inference(negUnitSimplification, [status(thm)], [c_2279, c_3612])).
% 5.73/2.08  tff(c_3664, plain, (![D_800]: (D_800!='#skF_7'(k1_tarski('#skF_8')) | ~r2_hidden(D_800, k1_tarski('#skF_8')) | ~r2_hidden(D_800, k1_tarski(k4_tarski('#skF_9', '#skF_8'))))), inference(superposition, [status(thm), theory('equality')], [c_2093, c_3638])).
% 5.73/2.08  tff(c_3680, plain, (![D_803]: (D_803!='#skF_7'(k1_tarski('#skF_8')) | ~r2_hidden(D_803, k1_tarski('#skF_8')) | ~r2_hidden(D_803, k1_tarski('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_2093, c_3664])).
% 5.73/2.08  tff(c_3703, plain, (~r2_hidden('#skF_7'(k1_tarski('#skF_8')), k1_tarski('#skF_8')) | k1_tarski('#skF_8')=k1_xboole_0), inference(resolution, [status(thm)], [c_52, c_3680])).
% 5.73/2.08  tff(c_3713, plain, (~r2_hidden('#skF_7'(k1_tarski('#skF_8')), k1_tarski('#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_2279, c_3703])).
% 5.73/2.08  tff(c_3716, plain, (k1_tarski('#skF_8')=k1_xboole_0), inference(resolution, [status(thm)], [c_52, c_3713])).
% 5.73/2.08  tff(c_3720, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2279, c_3716])).
% 5.73/2.08  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.73/2.08  
% 5.73/2.08  Inference rules
% 5.73/2.08  ----------------------
% 5.73/2.08  #Ref     : 0
% 5.73/2.08  #Sup     : 1062
% 5.73/2.08  #Fact    : 0
% 5.73/2.08  #Define  : 0
% 5.73/2.08  #Split   : 8
% 5.73/2.08  #Chain   : 0
% 5.73/2.08  #Close   : 0
% 5.73/2.08  
% 5.73/2.08  Ordering : KBO
% 5.73/2.08  
% 5.73/2.08  Simplification rules
% 5.73/2.08  ----------------------
% 5.73/2.08  #Subsume      : 198
% 5.73/2.08  #Demod        : 385
% 5.73/2.08  #Tautology    : 224
% 5.73/2.08  #SimpNegUnit  : 77
% 5.73/2.08  #BackRed      : 9
% 5.73/2.08  
% 5.73/2.08  #Partial instantiations: 0
% 5.73/2.09  #Strategies tried      : 1
% 5.73/2.09  
% 5.73/2.09  Timing (in seconds)
% 5.73/2.09  ----------------------
% 5.73/2.09  Preprocessing        : 0.33
% 5.73/2.09  Parsing              : 0.17
% 5.73/2.09  CNF conversion       : 0.02
% 5.73/2.09  Main loop            : 0.99
% 5.73/2.09  Inferencing          : 0.35
% 5.73/2.09  Reduction            : 0.33
% 5.73/2.09  Demodulation         : 0.24
% 5.73/2.09  BG Simplification    : 0.05
% 5.73/2.09  Subsumption          : 0.18
% 5.73/2.09  Abstraction          : 0.06
% 5.73/2.09  MUC search           : 0.00
% 5.73/2.09  Cooper               : 0.00
% 5.73/2.09  Total                : 1.36
% 5.73/2.09  Index Insertion      : 0.00
% 5.73/2.09  Index Deletion       : 0.00
% 5.73/2.09  Index Matching       : 0.00
% 5.73/2.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
