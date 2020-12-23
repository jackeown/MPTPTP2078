%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:12 EST 2020

% Result     : Theorem 2.72s
% Output     : CNFRefutation 2.72s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 413 expanded)
%              Number of leaves         :   25 ( 129 expanded)
%              Depth                    :    9
%              Number of atoms          :  205 ( 923 expanded)
%              Number of equality atoms :   93 ( 431 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C] :
        ( k4_xboole_0(k2_tarski(A,B),C) = k1_tarski(A)
      <=> ( ~ r2_hidden(A,C)
          & ( r2_hidden(B,C)
            | A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D] : k4_enumset1(A,A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_enumset1)).

tff(f_37,axiom,(
    ! [A,B] : k3_enumset1(A,A,A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_enumset1)).

tff(f_35,axiom,(
    ! [A] : k2_enumset1(A,A,A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_enumset1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k1_tarski(A)
    <=> ( ~ r2_hidden(A,C)
        & ( r2_hidden(B,C)
          | A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l38_zfmisc_1)).

tff(c_36,plain,
    ( ~ r2_hidden('#skF_1','#skF_3')
    | ~ r2_hidden('#skF_5','#skF_6')
    | r2_hidden('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_71,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_30,plain,
    ( ~ r2_hidden('#skF_1','#skF_3')
    | '#skF_5' != '#skF_4'
    | r2_hidden('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_61,plain,(
    '#skF_5' != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_42,plain,
    ( ~ r2_hidden('#skF_1','#skF_3')
    | k4_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_73,plain,(
    ~ r2_hidden('#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_132,plain,(
    ! [C_56,B_57,A_55,D_54,E_53] : k4_enumset1(A_55,A_55,B_57,C_56,D_54,E_53) = k3_enumset1(A_55,B_57,C_56,D_54,E_53) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_8,plain,(
    ! [A_15,B_16,C_17,D_18] : k4_enumset1(A_15,A_15,A_15,B_16,C_17,D_18) = k2_enumset1(A_15,B_16,C_17,D_18) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_148,plain,(
    ! [B_58,C_59,D_60,E_61] : k3_enumset1(B_58,B_58,C_59,D_60,E_61) = k2_enumset1(B_58,C_59,D_60,E_61) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_8])).

tff(c_12,plain,(
    ! [A_20,B_21] : k3_enumset1(A_20,A_20,A_20,A_20,B_21) = k2_tarski(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_194,plain,(
    ! [D_65,E_66] : k2_enumset1(D_65,D_65,D_65,E_66) = k2_tarski(D_65,E_66) ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_12])).

tff(c_10,plain,(
    ! [A_19] : k2_enumset1(A_19,A_19,A_19,A_19) = k1_tarski(A_19) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_201,plain,(
    ! [E_66] : k2_tarski(E_66,E_66) = k1_tarski(E_66) ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_10])).

tff(c_22,plain,(
    ! [B_31,C_32] :
      ( k4_xboole_0(k2_tarski(B_31,B_31),C_32) = k1_tarski(B_31)
      | r2_hidden(B_31,C_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_234,plain,(
    ! [B_68,C_69] :
      ( k4_xboole_0(k1_tarski(B_68),C_69) = k1_tarski(B_68)
      | r2_hidden(B_68,C_69) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_201,c_22])).

tff(c_40,plain,
    ( '#skF_2' = '#skF_1'
    | r2_hidden('#skF_2','#skF_3')
    | k4_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_111,plain,(
    k4_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k1_tarski('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_18,plain,(
    ! [B_31,A_30,C_32] :
      ( B_31 = A_30
      | r2_hidden(B_31,C_32)
      | k4_xboole_0(k2_tarski(A_30,B_31),C_32) != k1_tarski(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_115,plain,
    ( '#skF_5' = '#skF_4'
    | r2_hidden('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_18])).

tff(c_124,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_61,c_115])).

tff(c_126,plain,(
    k4_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') != k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_125,plain,
    ( r2_hidden('#skF_2','#skF_3')
    | '#skF_2' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_127,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_125])).

tff(c_38,plain,
    ( k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') != k1_tarski('#skF_1')
    | k4_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_231,plain,
    ( k4_xboole_0(k1_tarski('#skF_1'),'#skF_3') != k1_tarski('#skF_1')
    | k4_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_201,c_127,c_38])).

tff(c_232,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_3') != k1_tarski('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_126,c_231])).

tff(c_240,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_234,c_232])).

tff(c_248,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_240])).

tff(c_249,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_125])).

tff(c_334,plain,(
    ! [B_86,C_87,A_88] :
      ( ~ r2_hidden(B_86,C_87)
      | k4_xboole_0(k2_tarski(A_88,B_86),C_87) = k1_tarski(A_88)
      | r2_hidden(A_88,C_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_316,plain,(
    k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') != k1_tarski('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_126,c_38])).

tff(c_340,plain,
    ( ~ r2_hidden('#skF_2','#skF_3')
    | r2_hidden('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_334,c_316])).

tff(c_359,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_249,c_340])).

tff(c_361,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_359])).

tff(c_362,plain,(
    k4_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_397,plain,(
    ! [B_95,A_96,C_97] :
      ( B_95 = A_96
      | r2_hidden(B_95,C_97)
      | k4_xboole_0(k2_tarski(A_96,B_95),C_97) != k1_tarski(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_403,plain,
    ( '#skF_5' = '#skF_4'
    | r2_hidden('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_362,c_397])).

tff(c_409,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_61,c_403])).

tff(c_410,plain,
    ( ~ r2_hidden('#skF_1','#skF_3')
    | r2_hidden('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_412,plain,(
    ~ r2_hidden('#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_410])).

tff(c_513,plain,(
    ! [E_116,B_120,C_119,A_118,D_117] : k4_enumset1(A_118,A_118,B_120,C_119,D_117,E_116) = k3_enumset1(A_118,B_120,C_119,D_117,E_116) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_529,plain,(
    ! [B_121,C_122,D_123,E_124] : k3_enumset1(B_121,B_121,C_122,D_123,E_124) = k2_enumset1(B_121,C_122,D_123,E_124) ),
    inference(superposition,[status(thm),theory(equality)],[c_513,c_8])).

tff(c_545,plain,(
    ! [D_125,E_126] : k2_enumset1(D_125,D_125,D_125,E_126) = k2_tarski(D_125,E_126) ),
    inference(superposition,[status(thm),theory(equality)],[c_529,c_12])).

tff(c_552,plain,(
    ! [E_126] : k2_tarski(E_126,E_126) = k1_tarski(E_126) ),
    inference(superposition,[status(thm),theory(equality)],[c_545,c_10])).

tff(c_585,plain,(
    ! [B_128,C_129] :
      ( k4_xboole_0(k1_tarski(B_128),C_129) = k1_tarski(B_128)
      | r2_hidden(B_128,C_129) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_552,c_22])).

tff(c_411,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_34,plain,
    ( '#skF_2' = '#skF_1'
    | r2_hidden('#skF_2','#skF_3')
    | ~ r2_hidden('#skF_5','#skF_6')
    | r2_hidden('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_428,plain,
    ( '#skF_2' = '#skF_1'
    | r2_hidden('#skF_2','#skF_3')
    | r2_hidden('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_411,c_34])).

tff(c_429,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_428])).

tff(c_454,plain,(
    k4_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k1_tarski('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_20,plain,(
    ! [A_30,C_32,B_31] :
      ( ~ r2_hidden(A_30,C_32)
      | k4_xboole_0(k2_tarski(A_30,B_31),C_32) != k1_tarski(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_461,plain,(
    ~ r2_hidden('#skF_4','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_454,c_20])).

tff(c_470,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_429,c_461])).

tff(c_472,plain,(
    k4_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') != k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_471,plain,
    ( r2_hidden('#skF_2','#skF_3')
    | '#skF_2' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_474,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_471])).

tff(c_581,plain,
    ( k4_xboole_0(k1_tarski('#skF_1'),'#skF_3') != k1_tarski('#skF_1')
    | k4_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_552,c_474,c_38])).

tff(c_582,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_3') != k1_tarski('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_472,c_581])).

tff(c_591,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_585,c_582])).

tff(c_599,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_412,c_591])).

tff(c_600,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_471])).

tff(c_24,plain,(
    ! [B_31,C_32,A_30] :
      ( ~ r2_hidden(B_31,C_32)
      | k4_xboole_0(k2_tarski(A_30,B_31),C_32) = k1_tarski(A_30)
      | r2_hidden(A_30,C_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_712,plain,(
    k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') != k1_tarski('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_472,c_38])).

tff(c_715,plain,
    ( ~ r2_hidden('#skF_2','#skF_3')
    | r2_hidden('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_712])).

tff(c_718,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_600,c_715])).

tff(c_720,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_412,c_718])).

tff(c_722,plain,(
    ~ r2_hidden('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_428])).

tff(c_721,plain,
    ( r2_hidden('#skF_2','#skF_3')
    | '#skF_2' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_428])).

tff(c_724,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_721])).

tff(c_32,plain,
    ( k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') != k1_tarski('#skF_1')
    | ~ r2_hidden('#skF_5','#skF_6')
    | r2_hidden('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_804,plain,
    ( k4_xboole_0(k2_tarski('#skF_1','#skF_1'),'#skF_3') != k1_tarski('#skF_1')
    | r2_hidden('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_411,c_724,c_32])).

tff(c_805,plain,(
    k4_xboole_0(k2_tarski('#skF_1','#skF_1'),'#skF_3') != k1_tarski('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_722,c_804])).

tff(c_808,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_805])).

tff(c_812,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_412,c_808])).

tff(c_813,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_721])).

tff(c_925,plain,(
    ! [B_196,C_197,A_198] :
      ( ~ r2_hidden(B_196,C_197)
      | k4_xboole_0(k2_tarski(A_198,B_196),C_197) = k1_tarski(A_198)
      | r2_hidden(A_198,C_197) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_890,plain,
    ( k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') != k1_tarski('#skF_1')
    | r2_hidden('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_411,c_32])).

tff(c_891,plain,(
    k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') != k1_tarski('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_722,c_890])).

tff(c_931,plain,
    ( ~ r2_hidden('#skF_2','#skF_3')
    | r2_hidden('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_925,c_891])).

tff(c_947,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_813,c_931])).

tff(c_949,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_412,c_947])).

tff(c_950,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_410])).

tff(c_951,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_410])).

tff(c_954,plain,(
    k4_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_951,c_42])).

tff(c_959,plain,(
    ! [A_199,C_200,B_201] :
      ( ~ r2_hidden(A_199,C_200)
      | k4_xboole_0(k2_tarski(A_199,B_201),C_200) != k1_tarski(A_199) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_962,plain,(
    ~ r2_hidden('#skF_4','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_954,c_959])).

tff(c_966,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_950,c_962])).

tff(c_967,plain,
    ( ~ r2_hidden('#skF_1','#skF_3')
    | r2_hidden('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_973,plain,(
    ~ r2_hidden('#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_967])).

tff(c_968,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_28,plain,
    ( '#skF_2' = '#skF_1'
    | r2_hidden('#skF_2','#skF_3')
    | '#skF_5' != '#skF_4'
    | r2_hidden('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1000,plain,
    ( '#skF_2' = '#skF_1'
    | r2_hidden('#skF_2','#skF_3')
    | r2_hidden('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_968,c_28])).

tff(c_1001,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_1000])).

tff(c_1021,plain,
    ( '#skF_2' = '#skF_1'
    | r2_hidden('#skF_2','#skF_3')
    | k4_xboole_0(k2_tarski('#skF_4','#skF_4'),'#skF_6') = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_968,c_40])).

tff(c_1022,plain,(
    k4_xboole_0(k2_tarski('#skF_4','#skF_4'),'#skF_6') = k1_tarski('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1021])).

tff(c_1032,plain,(
    ~ r2_hidden('#skF_4','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1022,c_20])).

tff(c_1046,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1001,c_1032])).

tff(c_1048,plain,(
    k4_xboole_0(k2_tarski('#skF_4','#skF_4'),'#skF_6') != k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1021])).

tff(c_1047,plain,
    ( r2_hidden('#skF_2','#skF_3')
    | '#skF_2' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1021])).

tff(c_1049,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1047])).

tff(c_1134,plain,
    ( k4_xboole_0(k2_tarski('#skF_1','#skF_1'),'#skF_3') != k1_tarski('#skF_1')
    | k4_xboole_0(k2_tarski('#skF_4','#skF_4'),'#skF_6') = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_968,c_1049,c_38])).

tff(c_1135,plain,(
    k4_xboole_0(k2_tarski('#skF_1','#skF_1'),'#skF_3') != k1_tarski('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_1048,c_1134])).

tff(c_1141,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_1135])).

tff(c_1147,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_973,c_1141])).

tff(c_1148,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_1047])).

tff(c_1246,plain,
    ( k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') != k1_tarski('#skF_1')
    | k4_xboole_0(k2_tarski('#skF_4','#skF_4'),'#skF_6') = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_968,c_38])).

tff(c_1247,plain,(
    k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') != k1_tarski('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_1048,c_1246])).

tff(c_1250,plain,
    ( ~ r2_hidden('#skF_2','#skF_3')
    | r2_hidden('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1247])).

tff(c_1253,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1148,c_1250])).

tff(c_1255,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_973,c_1253])).

tff(c_1257,plain,(
    ~ r2_hidden('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_1000])).

tff(c_1256,plain,
    ( r2_hidden('#skF_2','#skF_3')
    | '#skF_2' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1000])).

tff(c_1258,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1256])).

tff(c_26,plain,
    ( k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') != k1_tarski('#skF_1')
    | '#skF_5' != '#skF_4'
    | r2_hidden('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1275,plain,
    ( k4_xboole_0(k2_tarski('#skF_1','#skF_1'),'#skF_3') != k1_tarski('#skF_1')
    | r2_hidden('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_968,c_1258,c_26])).

tff(c_1276,plain,(
    k4_xboole_0(k2_tarski('#skF_1','#skF_1'),'#skF_3') != k1_tarski('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_1257,c_1275])).

tff(c_1279,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_1276])).

tff(c_1283,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_973,c_1279])).

tff(c_1284,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_1256])).

tff(c_1319,plain,(
    ! [B_261,C_262,A_263] :
      ( ~ r2_hidden(B_261,C_262)
      | k4_xboole_0(k2_tarski(A_263,B_261),C_262) = k1_tarski(A_263)
      | r2_hidden(A_263,C_262) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1289,plain,
    ( k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') != k1_tarski('#skF_1')
    | r2_hidden('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_968,c_26])).

tff(c_1290,plain,(
    k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') != k1_tarski('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_1257,c_1289])).

tff(c_1328,plain,
    ( ~ r2_hidden('#skF_2','#skF_3')
    | r2_hidden('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1319,c_1290])).

tff(c_1346,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1284,c_1328])).

tff(c_1348,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_973,c_1346])).

tff(c_1349,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_967])).

tff(c_1350,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_967])).

tff(c_1364,plain,(
    k4_xboole_0(k2_tarski('#skF_4','#skF_4'),'#skF_6') = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_968,c_1350,c_42])).

tff(c_1368,plain,(
    ~ r2_hidden('#skF_4','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1364,c_20])).

tff(c_1374,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1349,c_1368])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:43:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.72/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.72/1.43  
% 2.72/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.72/1.43  %$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.72/1.43  
% 2.72/1.43  %Foreground sorts:
% 2.72/1.43  
% 2.72/1.43  
% 2.72/1.43  %Background operators:
% 2.72/1.43  
% 2.72/1.43  
% 2.72/1.43  %Foreground operators:
% 2.72/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.72/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.72/1.43  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.72/1.43  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.72/1.43  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.72/1.43  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.72/1.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.72/1.43  tff('#skF_5', type, '#skF_5': $i).
% 2.72/1.43  tff('#skF_6', type, '#skF_6': $i).
% 2.72/1.43  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.72/1.43  tff('#skF_2', type, '#skF_2': $i).
% 2.72/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.72/1.43  tff('#skF_1', type, '#skF_1': $i).
% 2.72/1.43  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.72/1.43  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.72/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.72/1.43  tff('#skF_4', type, '#skF_4': $i).
% 2.72/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.72/1.43  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.72/1.43  
% 2.72/1.45  tff(f_60, negated_conjecture, ~(![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k1_tarski(A)) <=> (~r2_hidden(A, C) & (r2_hidden(B, C) | (A = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_zfmisc_1)).
% 2.72/1.45  tff(f_29, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 2.72/1.45  tff(f_33, axiom, (![A, B, C, D]: (k4_enumset1(A, A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_enumset1)).
% 2.72/1.45  tff(f_37, axiom, (![A, B]: (k3_enumset1(A, A, A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_enumset1)).
% 2.72/1.45  tff(f_35, axiom, (![A]: (k2_enumset1(A, A, A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t82_enumset1)).
% 2.72/1.45  tff(f_50, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k1_tarski(A)) <=> (~r2_hidden(A, C) & (r2_hidden(B, C) | (A = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l38_zfmisc_1)).
% 2.72/1.45  tff(c_36, plain, (~r2_hidden('#skF_1', '#skF_3') | ~r2_hidden('#skF_5', '#skF_6') | r2_hidden('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.72/1.45  tff(c_71, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_36])).
% 2.72/1.45  tff(c_30, plain, (~r2_hidden('#skF_1', '#skF_3') | '#skF_5'!='#skF_4' | r2_hidden('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.72/1.45  tff(c_61, plain, ('#skF_5'!='#skF_4'), inference(splitLeft, [status(thm)], [c_30])).
% 2.72/1.45  tff(c_42, plain, (~r2_hidden('#skF_1', '#skF_3') | k4_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.72/1.45  tff(c_73, plain, (~r2_hidden('#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_42])).
% 2.72/1.45  tff(c_132, plain, (![C_56, B_57, A_55, D_54, E_53]: (k4_enumset1(A_55, A_55, B_57, C_56, D_54, E_53)=k3_enumset1(A_55, B_57, C_56, D_54, E_53))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.72/1.45  tff(c_8, plain, (![A_15, B_16, C_17, D_18]: (k4_enumset1(A_15, A_15, A_15, B_16, C_17, D_18)=k2_enumset1(A_15, B_16, C_17, D_18))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.72/1.45  tff(c_148, plain, (![B_58, C_59, D_60, E_61]: (k3_enumset1(B_58, B_58, C_59, D_60, E_61)=k2_enumset1(B_58, C_59, D_60, E_61))), inference(superposition, [status(thm), theory('equality')], [c_132, c_8])).
% 2.72/1.45  tff(c_12, plain, (![A_20, B_21]: (k3_enumset1(A_20, A_20, A_20, A_20, B_21)=k2_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.72/1.45  tff(c_194, plain, (![D_65, E_66]: (k2_enumset1(D_65, D_65, D_65, E_66)=k2_tarski(D_65, E_66))), inference(superposition, [status(thm), theory('equality')], [c_148, c_12])).
% 2.72/1.45  tff(c_10, plain, (![A_19]: (k2_enumset1(A_19, A_19, A_19, A_19)=k1_tarski(A_19))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.72/1.45  tff(c_201, plain, (![E_66]: (k2_tarski(E_66, E_66)=k1_tarski(E_66))), inference(superposition, [status(thm), theory('equality')], [c_194, c_10])).
% 2.72/1.45  tff(c_22, plain, (![B_31, C_32]: (k4_xboole_0(k2_tarski(B_31, B_31), C_32)=k1_tarski(B_31) | r2_hidden(B_31, C_32))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.72/1.45  tff(c_234, plain, (![B_68, C_69]: (k4_xboole_0(k1_tarski(B_68), C_69)=k1_tarski(B_68) | r2_hidden(B_68, C_69))), inference(demodulation, [status(thm), theory('equality')], [c_201, c_22])).
% 2.72/1.45  tff(c_40, plain, ('#skF_2'='#skF_1' | r2_hidden('#skF_2', '#skF_3') | k4_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.72/1.45  tff(c_111, plain, (k4_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k1_tarski('#skF_4')), inference(splitLeft, [status(thm)], [c_40])).
% 2.72/1.45  tff(c_18, plain, (![B_31, A_30, C_32]: (B_31=A_30 | r2_hidden(B_31, C_32) | k4_xboole_0(k2_tarski(A_30, B_31), C_32)!=k1_tarski(A_30))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.72/1.45  tff(c_115, plain, ('#skF_5'='#skF_4' | r2_hidden('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_111, c_18])).
% 2.72/1.45  tff(c_124, plain, $false, inference(negUnitSimplification, [status(thm)], [c_71, c_61, c_115])).
% 2.72/1.45  tff(c_126, plain, (k4_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')!=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_40])).
% 2.72/1.45  tff(c_125, plain, (r2_hidden('#skF_2', '#skF_3') | '#skF_2'='#skF_1'), inference(splitRight, [status(thm)], [c_40])).
% 2.72/1.45  tff(c_127, plain, ('#skF_2'='#skF_1'), inference(splitLeft, [status(thm)], [c_125])).
% 2.72/1.45  tff(c_38, plain, (k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')!=k1_tarski('#skF_1') | k4_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.72/1.45  tff(c_231, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_3')!=k1_tarski('#skF_1') | k4_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_201, c_127, c_38])).
% 2.72/1.45  tff(c_232, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_3')!=k1_tarski('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_126, c_231])).
% 2.72/1.45  tff(c_240, plain, (r2_hidden('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_234, c_232])).
% 2.72/1.45  tff(c_248, plain, $false, inference(negUnitSimplification, [status(thm)], [c_73, c_240])).
% 2.72/1.45  tff(c_249, plain, (r2_hidden('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_125])).
% 2.72/1.45  tff(c_334, plain, (![B_86, C_87, A_88]: (~r2_hidden(B_86, C_87) | k4_xboole_0(k2_tarski(A_88, B_86), C_87)=k1_tarski(A_88) | r2_hidden(A_88, C_87))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.72/1.45  tff(c_316, plain, (k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')!=k1_tarski('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_126, c_38])).
% 2.72/1.45  tff(c_340, plain, (~r2_hidden('#skF_2', '#skF_3') | r2_hidden('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_334, c_316])).
% 2.72/1.45  tff(c_359, plain, (r2_hidden('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_249, c_340])).
% 2.72/1.45  tff(c_361, plain, $false, inference(negUnitSimplification, [status(thm)], [c_73, c_359])).
% 2.72/1.45  tff(c_362, plain, (k4_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_42])).
% 2.72/1.45  tff(c_397, plain, (![B_95, A_96, C_97]: (B_95=A_96 | r2_hidden(B_95, C_97) | k4_xboole_0(k2_tarski(A_96, B_95), C_97)!=k1_tarski(A_96))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.72/1.45  tff(c_403, plain, ('#skF_5'='#skF_4' | r2_hidden('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_362, c_397])).
% 2.72/1.45  tff(c_409, plain, $false, inference(negUnitSimplification, [status(thm)], [c_71, c_61, c_403])).
% 2.72/1.45  tff(c_410, plain, (~r2_hidden('#skF_1', '#skF_3') | r2_hidden('#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_36])).
% 2.72/1.45  tff(c_412, plain, (~r2_hidden('#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_410])).
% 2.72/1.45  tff(c_513, plain, (![E_116, B_120, C_119, A_118, D_117]: (k4_enumset1(A_118, A_118, B_120, C_119, D_117, E_116)=k3_enumset1(A_118, B_120, C_119, D_117, E_116))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.72/1.45  tff(c_529, plain, (![B_121, C_122, D_123, E_124]: (k3_enumset1(B_121, B_121, C_122, D_123, E_124)=k2_enumset1(B_121, C_122, D_123, E_124))), inference(superposition, [status(thm), theory('equality')], [c_513, c_8])).
% 2.72/1.45  tff(c_545, plain, (![D_125, E_126]: (k2_enumset1(D_125, D_125, D_125, E_126)=k2_tarski(D_125, E_126))), inference(superposition, [status(thm), theory('equality')], [c_529, c_12])).
% 2.72/1.45  tff(c_552, plain, (![E_126]: (k2_tarski(E_126, E_126)=k1_tarski(E_126))), inference(superposition, [status(thm), theory('equality')], [c_545, c_10])).
% 2.72/1.45  tff(c_585, plain, (![B_128, C_129]: (k4_xboole_0(k1_tarski(B_128), C_129)=k1_tarski(B_128) | r2_hidden(B_128, C_129))), inference(demodulation, [status(thm), theory('equality')], [c_552, c_22])).
% 2.72/1.45  tff(c_411, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_36])).
% 2.72/1.45  tff(c_34, plain, ('#skF_2'='#skF_1' | r2_hidden('#skF_2', '#skF_3') | ~r2_hidden('#skF_5', '#skF_6') | r2_hidden('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.72/1.45  tff(c_428, plain, ('#skF_2'='#skF_1' | r2_hidden('#skF_2', '#skF_3') | r2_hidden('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_411, c_34])).
% 2.72/1.45  tff(c_429, plain, (r2_hidden('#skF_4', '#skF_6')), inference(splitLeft, [status(thm)], [c_428])).
% 2.72/1.45  tff(c_454, plain, (k4_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k1_tarski('#skF_4')), inference(splitLeft, [status(thm)], [c_40])).
% 2.72/1.45  tff(c_20, plain, (![A_30, C_32, B_31]: (~r2_hidden(A_30, C_32) | k4_xboole_0(k2_tarski(A_30, B_31), C_32)!=k1_tarski(A_30))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.72/1.45  tff(c_461, plain, (~r2_hidden('#skF_4', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_454, c_20])).
% 2.72/1.45  tff(c_470, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_429, c_461])).
% 2.72/1.45  tff(c_472, plain, (k4_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')!=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_40])).
% 2.72/1.45  tff(c_471, plain, (r2_hidden('#skF_2', '#skF_3') | '#skF_2'='#skF_1'), inference(splitRight, [status(thm)], [c_40])).
% 2.72/1.45  tff(c_474, plain, ('#skF_2'='#skF_1'), inference(splitLeft, [status(thm)], [c_471])).
% 2.72/1.45  tff(c_581, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_3')!=k1_tarski('#skF_1') | k4_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_552, c_474, c_38])).
% 2.72/1.45  tff(c_582, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_3')!=k1_tarski('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_472, c_581])).
% 2.72/1.45  tff(c_591, plain, (r2_hidden('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_585, c_582])).
% 2.72/1.45  tff(c_599, plain, $false, inference(negUnitSimplification, [status(thm)], [c_412, c_591])).
% 2.72/1.45  tff(c_600, plain, (r2_hidden('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_471])).
% 2.72/1.45  tff(c_24, plain, (![B_31, C_32, A_30]: (~r2_hidden(B_31, C_32) | k4_xboole_0(k2_tarski(A_30, B_31), C_32)=k1_tarski(A_30) | r2_hidden(A_30, C_32))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.72/1.45  tff(c_712, plain, (k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')!=k1_tarski('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_472, c_38])).
% 2.72/1.45  tff(c_715, plain, (~r2_hidden('#skF_2', '#skF_3') | r2_hidden('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_24, c_712])).
% 2.72/1.45  tff(c_718, plain, (r2_hidden('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_600, c_715])).
% 2.72/1.45  tff(c_720, plain, $false, inference(negUnitSimplification, [status(thm)], [c_412, c_718])).
% 2.72/1.45  tff(c_722, plain, (~r2_hidden('#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_428])).
% 2.72/1.45  tff(c_721, plain, (r2_hidden('#skF_2', '#skF_3') | '#skF_2'='#skF_1'), inference(splitRight, [status(thm)], [c_428])).
% 2.72/1.45  tff(c_724, plain, ('#skF_2'='#skF_1'), inference(splitLeft, [status(thm)], [c_721])).
% 2.72/1.45  tff(c_32, plain, (k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')!=k1_tarski('#skF_1') | ~r2_hidden('#skF_5', '#skF_6') | r2_hidden('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.72/1.45  tff(c_804, plain, (k4_xboole_0(k2_tarski('#skF_1', '#skF_1'), '#skF_3')!=k1_tarski('#skF_1') | r2_hidden('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_411, c_724, c_32])).
% 2.72/1.45  tff(c_805, plain, (k4_xboole_0(k2_tarski('#skF_1', '#skF_1'), '#skF_3')!=k1_tarski('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_722, c_804])).
% 2.72/1.45  tff(c_808, plain, (r2_hidden('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_22, c_805])).
% 2.72/1.45  tff(c_812, plain, $false, inference(negUnitSimplification, [status(thm)], [c_412, c_808])).
% 2.72/1.45  tff(c_813, plain, (r2_hidden('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_721])).
% 2.72/1.45  tff(c_925, plain, (![B_196, C_197, A_198]: (~r2_hidden(B_196, C_197) | k4_xboole_0(k2_tarski(A_198, B_196), C_197)=k1_tarski(A_198) | r2_hidden(A_198, C_197))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.72/1.45  tff(c_890, plain, (k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')!=k1_tarski('#skF_1') | r2_hidden('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_411, c_32])).
% 2.72/1.45  tff(c_891, plain, (k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')!=k1_tarski('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_722, c_890])).
% 2.72/1.45  tff(c_931, plain, (~r2_hidden('#skF_2', '#skF_3') | r2_hidden('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_925, c_891])).
% 2.72/1.45  tff(c_947, plain, (r2_hidden('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_813, c_931])).
% 2.72/1.45  tff(c_949, plain, $false, inference(negUnitSimplification, [status(thm)], [c_412, c_947])).
% 2.72/1.45  tff(c_950, plain, (r2_hidden('#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_410])).
% 2.72/1.45  tff(c_951, plain, (r2_hidden('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_410])).
% 2.72/1.45  tff(c_954, plain, (k4_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_951, c_42])).
% 2.72/1.45  tff(c_959, plain, (![A_199, C_200, B_201]: (~r2_hidden(A_199, C_200) | k4_xboole_0(k2_tarski(A_199, B_201), C_200)!=k1_tarski(A_199))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.72/1.45  tff(c_962, plain, (~r2_hidden('#skF_4', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_954, c_959])).
% 2.72/1.45  tff(c_966, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_950, c_962])).
% 2.72/1.45  tff(c_967, plain, (~r2_hidden('#skF_1', '#skF_3') | r2_hidden('#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_30])).
% 2.72/1.45  tff(c_973, plain, (~r2_hidden('#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_967])).
% 2.72/1.45  tff(c_968, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_30])).
% 2.72/1.45  tff(c_28, plain, ('#skF_2'='#skF_1' | r2_hidden('#skF_2', '#skF_3') | '#skF_5'!='#skF_4' | r2_hidden('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.72/1.45  tff(c_1000, plain, ('#skF_2'='#skF_1' | r2_hidden('#skF_2', '#skF_3') | r2_hidden('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_968, c_28])).
% 2.72/1.45  tff(c_1001, plain, (r2_hidden('#skF_4', '#skF_6')), inference(splitLeft, [status(thm)], [c_1000])).
% 2.72/1.45  tff(c_1021, plain, ('#skF_2'='#skF_1' | r2_hidden('#skF_2', '#skF_3') | k4_xboole_0(k2_tarski('#skF_4', '#skF_4'), '#skF_6')=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_968, c_40])).
% 2.72/1.45  tff(c_1022, plain, (k4_xboole_0(k2_tarski('#skF_4', '#skF_4'), '#skF_6')=k1_tarski('#skF_4')), inference(splitLeft, [status(thm)], [c_1021])).
% 2.72/1.45  tff(c_1032, plain, (~r2_hidden('#skF_4', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1022, c_20])).
% 2.72/1.45  tff(c_1046, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1001, c_1032])).
% 2.72/1.45  tff(c_1048, plain, (k4_xboole_0(k2_tarski('#skF_4', '#skF_4'), '#skF_6')!=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_1021])).
% 2.72/1.45  tff(c_1047, plain, (r2_hidden('#skF_2', '#skF_3') | '#skF_2'='#skF_1'), inference(splitRight, [status(thm)], [c_1021])).
% 2.72/1.45  tff(c_1049, plain, ('#skF_2'='#skF_1'), inference(splitLeft, [status(thm)], [c_1047])).
% 2.72/1.45  tff(c_1134, plain, (k4_xboole_0(k2_tarski('#skF_1', '#skF_1'), '#skF_3')!=k1_tarski('#skF_1') | k4_xboole_0(k2_tarski('#skF_4', '#skF_4'), '#skF_6')=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_968, c_1049, c_38])).
% 2.72/1.45  tff(c_1135, plain, (k4_xboole_0(k2_tarski('#skF_1', '#skF_1'), '#skF_3')!=k1_tarski('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_1048, c_1134])).
% 2.72/1.45  tff(c_1141, plain, (r2_hidden('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_22, c_1135])).
% 2.72/1.45  tff(c_1147, plain, $false, inference(negUnitSimplification, [status(thm)], [c_973, c_1141])).
% 2.72/1.45  tff(c_1148, plain, (r2_hidden('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_1047])).
% 2.72/1.45  tff(c_1246, plain, (k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')!=k1_tarski('#skF_1') | k4_xboole_0(k2_tarski('#skF_4', '#skF_4'), '#skF_6')=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_968, c_38])).
% 2.72/1.45  tff(c_1247, plain, (k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')!=k1_tarski('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_1048, c_1246])).
% 2.72/1.45  tff(c_1250, plain, (~r2_hidden('#skF_2', '#skF_3') | r2_hidden('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_24, c_1247])).
% 2.72/1.45  tff(c_1253, plain, (r2_hidden('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1148, c_1250])).
% 2.72/1.45  tff(c_1255, plain, $false, inference(negUnitSimplification, [status(thm)], [c_973, c_1253])).
% 2.72/1.45  tff(c_1257, plain, (~r2_hidden('#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_1000])).
% 2.72/1.45  tff(c_1256, plain, (r2_hidden('#skF_2', '#skF_3') | '#skF_2'='#skF_1'), inference(splitRight, [status(thm)], [c_1000])).
% 2.72/1.45  tff(c_1258, plain, ('#skF_2'='#skF_1'), inference(splitLeft, [status(thm)], [c_1256])).
% 2.72/1.45  tff(c_26, plain, (k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')!=k1_tarski('#skF_1') | '#skF_5'!='#skF_4' | r2_hidden('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.72/1.45  tff(c_1275, plain, (k4_xboole_0(k2_tarski('#skF_1', '#skF_1'), '#skF_3')!=k1_tarski('#skF_1') | r2_hidden('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_968, c_1258, c_26])).
% 2.72/1.45  tff(c_1276, plain, (k4_xboole_0(k2_tarski('#skF_1', '#skF_1'), '#skF_3')!=k1_tarski('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_1257, c_1275])).
% 2.72/1.45  tff(c_1279, plain, (r2_hidden('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_22, c_1276])).
% 2.72/1.45  tff(c_1283, plain, $false, inference(negUnitSimplification, [status(thm)], [c_973, c_1279])).
% 2.72/1.45  tff(c_1284, plain, (r2_hidden('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_1256])).
% 2.72/1.45  tff(c_1319, plain, (![B_261, C_262, A_263]: (~r2_hidden(B_261, C_262) | k4_xboole_0(k2_tarski(A_263, B_261), C_262)=k1_tarski(A_263) | r2_hidden(A_263, C_262))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.72/1.45  tff(c_1289, plain, (k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')!=k1_tarski('#skF_1') | r2_hidden('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_968, c_26])).
% 2.72/1.45  tff(c_1290, plain, (k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')!=k1_tarski('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_1257, c_1289])).
% 2.72/1.45  tff(c_1328, plain, (~r2_hidden('#skF_2', '#skF_3') | r2_hidden('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1319, c_1290])).
% 2.72/1.45  tff(c_1346, plain, (r2_hidden('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1284, c_1328])).
% 2.72/1.45  tff(c_1348, plain, $false, inference(negUnitSimplification, [status(thm)], [c_973, c_1346])).
% 2.72/1.45  tff(c_1349, plain, (r2_hidden('#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_967])).
% 2.72/1.45  tff(c_1350, plain, (r2_hidden('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_967])).
% 2.72/1.45  tff(c_1364, plain, (k4_xboole_0(k2_tarski('#skF_4', '#skF_4'), '#skF_6')=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_968, c_1350, c_42])).
% 2.72/1.45  tff(c_1368, plain, (~r2_hidden('#skF_4', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1364, c_20])).
% 2.72/1.45  tff(c_1374, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1349, c_1368])).
% 2.72/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.72/1.45  
% 2.72/1.45  Inference rules
% 2.72/1.45  ----------------------
% 2.72/1.45  #Ref     : 0
% 2.72/1.45  #Sup     : 286
% 2.72/1.45  #Fact    : 0
% 2.72/1.45  #Define  : 0
% 2.72/1.45  #Split   : 15
% 2.72/1.45  #Chain   : 0
% 2.72/1.45  #Close   : 0
% 2.72/1.45  
% 2.72/1.45  Ordering : KBO
% 2.72/1.45  
% 2.72/1.45  Simplification rules
% 2.72/1.45  ----------------------
% 2.72/1.45  #Subsume      : 20
% 2.72/1.45  #Demod        : 94
% 2.72/1.45  #Tautology    : 216
% 2.72/1.45  #SimpNegUnit  : 34
% 2.72/1.45  #BackRed      : 5
% 2.72/1.45  
% 2.72/1.45  #Partial instantiations: 0
% 2.72/1.45  #Strategies tried      : 1
% 2.72/1.45  
% 2.72/1.45  Timing (in seconds)
% 2.72/1.45  ----------------------
% 2.72/1.46  Preprocessing        : 0.30
% 2.72/1.46  Parsing              : 0.16
% 2.72/1.46  CNF conversion       : 0.02
% 2.72/1.46  Main loop            : 0.37
% 2.72/1.46  Inferencing          : 0.16
% 2.72/1.46  Reduction            : 0.10
% 2.72/1.46  Demodulation         : 0.07
% 2.72/1.46  BG Simplification    : 0.02
% 2.72/1.46  Subsumption          : 0.05
% 2.72/1.46  Abstraction          : 0.02
% 2.72/1.46  MUC search           : 0.00
% 2.72/1.46  Cooper               : 0.00
% 2.72/1.46  Total                : 0.72
% 2.72/1.46  Index Insertion      : 0.00
% 2.72/1.46  Index Deletion       : 0.00
% 2.72/1.46  Index Matching       : 0.00
% 2.72/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
