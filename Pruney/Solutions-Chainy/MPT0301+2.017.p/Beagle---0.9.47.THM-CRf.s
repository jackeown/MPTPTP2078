%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:42 EST 2020

% Result     : Theorem 5.48s
% Output     : CNFRefutation 5.74s
% Verified   : 
% Statistics : Number of formulae       :  210 (1351 expanded)
%              Number of leaves         :   35 ( 419 expanded)
%              Depth                    :   15
%              Number of atoms          :  276 (2461 expanded)
%              Number of equality atoms :  143 (1841 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_1 > #skF_6 > #skF_15 > #skF_10 > #skF_4 > #skF_14 > #skF_13 > #skF_2 > #skF_11 > #skF_7 > #skF_9 > #skF_3 > #skF_8 > #skF_12

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_15',type,(
    '#skF_15': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_14',type,(
    '#skF_14': $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_11',type,(
    '#skF_11': ( $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i ) > $i )).

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

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(f_54,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_56,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_58,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_60,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l35_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_88,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_zfmisc_1(A,B) = k1_xboole_0
      <=> ( A = k1_xboole_0
          | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
    <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).

tff(c_40,plain,(
    ! [A_15] :
      ( r2_hidden('#skF_5'(A_15),A_15)
      | k1_xboole_0 = A_15 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_42,plain,(
    ! [A_17] : k3_xboole_0(A_17,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_44,plain,(
    ! [A_18] : k4_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_138,plain,(
    ! [A_72,B_73] : k4_xboole_0(A_72,k4_xboole_0(A_72,B_73)) = k3_xboole_0(A_72,B_73) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_160,plain,(
    ! [A_18] : k4_xboole_0(A_18,A_18) = k3_xboole_0(A_18,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_138])).

tff(c_176,plain,(
    ! [A_77] : k4_xboole_0(A_77,A_77) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_160])).

tff(c_76,plain,(
    ! [A_57,B_58] :
      ( r2_hidden(A_57,B_58)
      | k4_xboole_0(k1_tarski(A_57),B_58) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_204,plain,(
    ! [A_57] : r2_hidden(A_57,k1_tarski(A_57)) ),
    inference(superposition,[status(thm),theory(equality)],[c_176,c_76])).

tff(c_123,plain,(
    ! [A_66,B_67] :
      ( r2_hidden(A_66,B_67)
      | k4_xboole_0(k1_tarski(A_66),B_67) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_127,plain,(
    ! [A_66] :
      ( r2_hidden(A_66,k1_xboole_0)
      | k1_tarski(A_66) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_123])).

tff(c_164,plain,(
    ! [D_74,B_75,A_76] :
      ( ~ r2_hidden(D_74,B_75)
      | ~ r2_hidden(D_74,k4_xboole_0(A_76,B_75)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2497,plain,(
    ! [D_255,A_256] :
      ( ~ r2_hidden(D_255,k1_xboole_0)
      | ~ r2_hidden(D_255,A_256) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_164])).

tff(c_2515,plain,(
    ! [A_259,A_260] :
      ( ~ r2_hidden(A_259,A_260)
      | k1_tarski(A_259) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_127,c_2497])).

tff(c_2528,plain,(
    ! [A_57] : k1_tarski(A_57) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_204,c_2515])).

tff(c_2541,plain,(
    ! [A_265,B_266] :
      ( k4_xboole_0(k1_tarski(A_265),B_266) = k1_xboole_0
      | ~ r2_hidden(A_265,B_266) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2568,plain,(
    ! [A_265] :
      ( k1_tarski(A_265) = k1_xboole_0
      | ~ r2_hidden(A_265,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2541,c_44])).

tff(c_2590,plain,(
    ! [A_265] : ~ r2_hidden(A_265,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_2528,c_2568])).

tff(c_82,plain,
    ( k1_xboole_0 = '#skF_13'
    | k1_xboole_0 = '#skF_12'
    | k1_xboole_0 != '#skF_15' ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_117,plain,(
    k1_xboole_0 != '#skF_15' ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_84,plain,
    ( k2_zfmisc_1('#skF_12','#skF_13') != k1_xboole_0
    | k1_xboole_0 != '#skF_14' ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_116,plain,(
    k1_xboole_0 != '#skF_14' ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_229,plain,(
    ! [D_80,A_81] :
      ( ~ r2_hidden(D_80,k1_xboole_0)
      | ~ r2_hidden(D_80,A_81) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_164])).

tff(c_247,plain,(
    ! [A_84,A_85] :
      ( ~ r2_hidden(A_84,A_85)
      | k1_tarski(A_84) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_127,c_229])).

tff(c_260,plain,(
    ! [A_57] : k1_tarski(A_57) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_204,c_247])).

tff(c_270,plain,(
    ! [A_87,B_88] :
      ( k4_xboole_0(k1_tarski(A_87),B_88) = k1_xboole_0
      | ~ r2_hidden(A_87,B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_297,plain,(
    ! [A_87] :
      ( k1_tarski(A_87) = k1_xboole_0
      | ~ r2_hidden(A_87,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_270,c_44])).

tff(c_319,plain,(
    ! [A_87] : ~ r2_hidden(A_87,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_260,c_297])).

tff(c_90,plain,
    ( k1_xboole_0 = '#skF_13'
    | k1_xboole_0 = '#skF_12'
    | k2_zfmisc_1('#skF_14','#skF_15') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_264,plain,(
    k2_zfmisc_1('#skF_14','#skF_15') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_90])).

tff(c_728,plain,(
    ! [E_124,F_125,A_126,B_127] :
      ( r2_hidden(k4_tarski(E_124,F_125),k2_zfmisc_1(A_126,B_127))
      | ~ r2_hidden(F_125,B_127)
      | ~ r2_hidden(E_124,A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_733,plain,(
    ! [E_124,F_125] :
      ( r2_hidden(k4_tarski(E_124,F_125),k1_xboole_0)
      | ~ r2_hidden(F_125,'#skF_15')
      | ~ r2_hidden(E_124,'#skF_14') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_264,c_728])).

tff(c_735,plain,(
    ! [F_125,E_124] :
      ( ~ r2_hidden(F_125,'#skF_15')
      | ~ r2_hidden(E_124,'#skF_14') ) ),
    inference(negUnitSimplification,[status(thm)],[c_319,c_733])).

tff(c_737,plain,(
    ! [E_128] : ~ r2_hidden(E_128,'#skF_14') ),
    inference(splitLeft,[status(thm)],[c_735])).

tff(c_741,plain,(
    k1_xboole_0 = '#skF_14' ),
    inference(resolution,[status(thm)],[c_40,c_737])).

tff(c_745,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_116,c_741])).

tff(c_747,plain,(
    ! [F_129] : ~ r2_hidden(F_129,'#skF_15') ),
    inference(splitRight,[status(thm)],[c_735])).

tff(c_751,plain,(
    k1_xboole_0 = '#skF_15' ),
    inference(resolution,[status(thm)],[c_40,c_747])).

tff(c_755,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_117,c_751])).

tff(c_756,plain,
    ( k1_xboole_0 = '#skF_12'
    | k1_xboole_0 = '#skF_13' ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_759,plain,(
    k1_xboole_0 = '#skF_13' ),
    inference(splitLeft,[status(thm)],[c_756])).

tff(c_766,plain,(
    ! [A_15] :
      ( r2_hidden('#skF_5'(A_15),A_15)
      | A_15 = '#skF_13' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_759,c_40])).

tff(c_1597,plain,(
    ! [A_193,B_194,D_195] :
      ( r2_hidden('#skF_11'(A_193,B_194,k2_zfmisc_1(A_193,B_194),D_195),B_194)
      | ~ r2_hidden(D_195,k2_zfmisc_1(A_193,B_194)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_760,plain,(
    ! [A_57] : k1_tarski(A_57) != '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_759,c_260])).

tff(c_78,plain,(
    ! [A_57,B_58] :
      ( k4_xboole_0(k1_tarski(A_57),B_58) = k1_xboole_0
      | ~ r2_hidden(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_870,plain,(
    ! [A_143,B_144] :
      ( k4_xboole_0(k1_tarski(A_143),B_144) = '#skF_13'
      | ~ r2_hidden(A_143,B_144) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_759,c_78])).

tff(c_770,plain,(
    ! [A_18] : k4_xboole_0(A_18,'#skF_13') = A_18 ),
    inference(demodulation,[status(thm),theory(equality)],[c_759,c_44])).

tff(c_881,plain,(
    ! [A_143] :
      ( k1_tarski(A_143) = '#skF_13'
      | ~ r2_hidden(A_143,'#skF_13') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_870,c_770])).

tff(c_914,plain,(
    ! [A_143] : ~ r2_hidden(A_143,'#skF_13') ),
    inference(negUnitSimplification,[status(thm)],[c_760,c_881])).

tff(c_1639,plain,(
    ! [D_196,A_197] : ~ r2_hidden(D_196,k2_zfmisc_1(A_197,'#skF_13')) ),
    inference(resolution,[status(thm)],[c_1597,c_914])).

tff(c_1667,plain,(
    ! [A_197] : k2_zfmisc_1(A_197,'#skF_13') = '#skF_13' ),
    inference(resolution,[status(thm)],[c_766,c_1639])).

tff(c_88,plain,
    ( k2_zfmisc_1('#skF_12','#skF_13') != k1_xboole_0
    | k2_zfmisc_1('#skF_14','#skF_15') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_228,plain,(
    k2_zfmisc_1('#skF_12','#skF_13') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_88])).

tff(c_763,plain,(
    k2_zfmisc_1('#skF_12','#skF_13') != '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_759,c_228])).

tff(c_1671,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1667,c_763])).

tff(c_1672,plain,(
    k1_xboole_0 = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_756])).

tff(c_1682,plain,(
    ! [A_15] :
      ( r2_hidden('#skF_5'(A_15),A_15)
      | A_15 = '#skF_12' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1672,c_40])).

tff(c_2423,plain,(
    ! [A_250,B_251,D_252] :
      ( r2_hidden('#skF_10'(A_250,B_251,k2_zfmisc_1(A_250,B_251),D_252),A_250)
      | ~ r2_hidden(D_252,k2_zfmisc_1(A_250,B_251)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1676,plain,(
    ! [A_57] : k1_tarski(A_57) != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1672,c_260])).

tff(c_1728,plain,(
    ! [A_201,B_202] :
      ( k4_xboole_0(k1_tarski(A_201),B_202) = '#skF_12'
      | ~ r2_hidden(A_201,B_202) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1672,c_78])).

tff(c_1686,plain,(
    ! [A_18] : k4_xboole_0(A_18,'#skF_12') = A_18 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1672,c_44])).

tff(c_1735,plain,(
    ! [A_201] :
      ( k1_tarski(A_201) = '#skF_12'
      | ~ r2_hidden(A_201,'#skF_12') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1728,c_1686])).

tff(c_1761,plain,(
    ! [A_201] : ~ r2_hidden(A_201,'#skF_12') ),
    inference(negUnitSimplification,[status(thm)],[c_1676,c_1735])).

tff(c_2461,plain,(
    ! [D_253,B_254] : ~ r2_hidden(D_253,k2_zfmisc_1('#skF_12',B_254)) ),
    inference(resolution,[status(thm)],[c_2423,c_1761])).

tff(c_2481,plain,(
    ! [B_254] : k2_zfmisc_1('#skF_12',B_254) = '#skF_12' ),
    inference(resolution,[status(thm)],[c_1682,c_2461])).

tff(c_1679,plain,(
    k2_zfmisc_1('#skF_12','#skF_13') != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1672,c_228])).

tff(c_2485,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2481,c_1679])).

tff(c_2487,plain,(
    k2_zfmisc_1('#skF_12','#skF_13') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_3127,plain,(
    ! [E_300,F_301,A_302,B_303] :
      ( r2_hidden(k4_tarski(E_300,F_301),k2_zfmisc_1(A_302,B_303))
      | ~ r2_hidden(F_301,B_303)
      | ~ r2_hidden(E_300,A_302) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_3132,plain,(
    ! [E_300,F_301] :
      ( r2_hidden(k4_tarski(E_300,F_301),k1_xboole_0)
      | ~ r2_hidden(F_301,'#skF_13')
      | ~ r2_hidden(E_300,'#skF_12') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2487,c_3127])).

tff(c_3137,plain,(
    ! [F_301,E_300] :
      ( ~ r2_hidden(F_301,'#skF_13')
      | ~ r2_hidden(E_300,'#skF_12') ) ),
    inference(negUnitSimplification,[status(thm)],[c_2590,c_3132])).

tff(c_3142,plain,(
    ! [E_304] : ~ r2_hidden(E_304,'#skF_12') ),
    inference(splitLeft,[status(thm)],[c_3137])).

tff(c_3152,plain,(
    k1_xboole_0 = '#skF_12' ),
    inference(resolution,[status(thm)],[c_40,c_3142])).

tff(c_3166,plain,(
    '#skF_15' != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3152,c_117])).

tff(c_3736,plain,(
    ! [A_342] :
      ( r2_hidden('#skF_5'(A_342),A_342)
      | A_342 = '#skF_12' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3152,c_40])).

tff(c_3167,plain,(
    '#skF_14' != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3152,c_116])).

tff(c_3586,plain,(
    ! [A_329] :
      ( r2_hidden('#skF_5'(A_329),A_329)
      | A_329 = '#skF_12' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3152,c_40])).

tff(c_2486,plain,(
    k2_zfmisc_1('#skF_14','#skF_15') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_3135,plain,(
    ! [E_300,F_301] :
      ( r2_hidden(k4_tarski(E_300,F_301),k1_xboole_0)
      | ~ r2_hidden(F_301,'#skF_15')
      | ~ r2_hidden(E_300,'#skF_14') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2486,c_3127])).

tff(c_3138,plain,(
    ! [F_301,E_300] :
      ( ~ r2_hidden(F_301,'#skF_15')
      | ~ r2_hidden(E_300,'#skF_14') ) ),
    inference(negUnitSimplification,[status(thm)],[c_2590,c_3135])).

tff(c_3490,plain,(
    ! [E_300] : ~ r2_hidden(E_300,'#skF_14') ),
    inference(splitLeft,[status(thm)],[c_3138])).

tff(c_3606,plain,(
    '#skF_14' = '#skF_12' ),
    inference(resolution,[status(thm)],[c_3586,c_3490])).

tff(c_3639,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3167,c_3606])).

tff(c_3640,plain,(
    ! [F_301] : ~ r2_hidden(F_301,'#skF_15') ),
    inference(splitRight,[status(thm)],[c_3138])).

tff(c_3756,plain,(
    '#skF_15' = '#skF_12' ),
    inference(resolution,[status(thm)],[c_3736,c_3640])).

tff(c_3789,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3166,c_3756])).

tff(c_3791,plain,(
    ! [F_343] : ~ r2_hidden(F_343,'#skF_13') ),
    inference(splitRight,[status(thm)],[c_3137])).

tff(c_3801,plain,(
    k1_xboole_0 = '#skF_13' ),
    inference(resolution,[status(thm)],[c_40,c_3791])).

tff(c_3815,plain,(
    '#skF_15' != '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3801,c_117])).

tff(c_4386,plain,(
    ! [A_381] :
      ( r2_hidden('#skF_5'(A_381),A_381)
      | A_381 = '#skF_13' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3801,c_40])).

tff(c_3816,plain,(
    '#skF_14' != '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3801,c_116])).

tff(c_4234,plain,(
    ! [A_368] :
      ( r2_hidden('#skF_5'(A_368),A_368)
      | A_368 = '#skF_13' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3801,c_40])).

tff(c_4139,plain,(
    ! [E_300] : ~ r2_hidden(E_300,'#skF_14') ),
    inference(splitLeft,[status(thm)],[c_3138])).

tff(c_4254,plain,(
    '#skF_14' = '#skF_13' ),
    inference(resolution,[status(thm)],[c_4234,c_4139])).

tff(c_4287,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3816,c_4254])).

tff(c_4288,plain,(
    ! [F_301] : ~ r2_hidden(F_301,'#skF_15') ),
    inference(splitRight,[status(thm)],[c_3138])).

tff(c_4406,plain,(
    '#skF_15' = '#skF_13' ),
    inference(resolution,[status(thm)],[c_4386,c_4288])).

tff(c_4439,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3815,c_4406])).

tff(c_4441,plain,(
    k1_xboole_0 = '#skF_15' ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_4440,plain,
    ( k1_xboole_0 = '#skF_12'
    | k1_xboole_0 = '#skF_13' ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_4451,plain,
    ( '#skF_15' = '#skF_12'
    | '#skF_15' = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4441,c_4441,c_4440])).

tff(c_4452,plain,(
    '#skF_15' = '#skF_13' ),
    inference(splitLeft,[status(thm)],[c_4451])).

tff(c_4455,plain,(
    k1_xboole_0 = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4452,c_4441])).

tff(c_4482,plain,(
    ! [A_15] :
      ( r2_hidden('#skF_5'(A_15),A_15)
      | A_15 = '#skF_13' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4455,c_40])).

tff(c_5328,plain,(
    ! [A_461,B_462,D_463] :
      ( r2_hidden('#skF_11'(A_461,B_462,k2_zfmisc_1(A_461,B_462),D_463),B_462)
      | ~ r2_hidden(D_463,k2_zfmisc_1(A_461,B_462)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_4444,plain,(
    ! [A_18] : k4_xboole_0(A_18,'#skF_15') = A_18 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4441,c_44])).

tff(c_4464,plain,(
    ! [A_18] : k4_xboole_0(A_18,'#skF_13') = A_18 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4452,c_4444])).

tff(c_4622,plain,(
    ! [A_400,B_401] :
      ( r2_hidden(A_400,B_401)
      | k4_xboole_0(k1_tarski(A_400),B_401) != '#skF_13' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4455,c_76])).

tff(c_4641,plain,(
    ! [A_403] :
      ( r2_hidden(A_403,'#skF_13')
      | k1_tarski(A_403) != '#skF_13' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4464,c_4622])).

tff(c_4443,plain,(
    ! [A_17] : k3_xboole_0(A_17,'#skF_15') = '#skF_15' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4441,c_4441,c_42])).

tff(c_4474,plain,(
    ! [A_17] : k3_xboole_0(A_17,'#skF_13') = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4452,c_4452,c_4443])).

tff(c_4485,plain,(
    ! [A_385,B_386] : k4_xboole_0(A_385,k4_xboole_0(A_385,B_386)) = k3_xboole_0(A_385,B_386) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_4500,plain,(
    ! [A_18] : k4_xboole_0(A_18,A_18) = k3_xboole_0(A_18,'#skF_13') ),
    inference(superposition,[status(thm),theory(equality)],[c_4464,c_4485])).

tff(c_4503,plain,(
    ! [A_18] : k4_xboole_0(A_18,A_18) = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4474,c_4500])).

tff(c_4597,plain,(
    ! [D_395,A_396,B_397] :
      ( r2_hidden(D_395,A_396)
      | ~ r2_hidden(D_395,k4_xboole_0(A_396,B_397)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_4603,plain,(
    ! [D_395,A_18] :
      ( r2_hidden(D_395,A_18)
      | ~ r2_hidden(D_395,'#skF_13') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4503,c_4597])).

tff(c_4647,plain,(
    ! [A_403,A_18] :
      ( r2_hidden(A_403,A_18)
      | k1_tarski(A_403) != '#skF_13' ) ),
    inference(resolution,[status(thm)],[c_4641,c_4603])).

tff(c_4664,plain,(
    ! [D_406,B_407,A_408] :
      ( ~ r2_hidden(D_406,B_407)
      | ~ r2_hidden(D_406,k4_xboole_0(A_408,B_407)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_4697,plain,(
    ! [A_411,B_412] :
      ( ~ r2_hidden(A_411,B_412)
      | k1_tarski(A_411) != '#skF_13' ) ),
    inference(resolution,[status(thm)],[c_4647,c_4664])).

tff(c_4710,plain,(
    ! [A_403] : k1_tarski(A_403) != '#skF_13' ),
    inference(resolution,[status(thm)],[c_4647,c_4697])).

tff(c_4549,plain,(
    ! [A_392,B_393] :
      ( k4_xboole_0(k1_tarski(A_392),B_393) = '#skF_13'
      | ~ r2_hidden(A_392,B_393) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4455,c_78])).

tff(c_4567,plain,(
    ! [A_392] :
      ( k1_tarski(A_392) = '#skF_13'
      | ~ r2_hidden(A_392,'#skF_13') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4549,c_4464])).

tff(c_4722,plain,(
    ! [A_392] : ~ r2_hidden(A_392,'#skF_13') ),
    inference(negUnitSimplification,[status(thm)],[c_4710,c_4567])).

tff(c_5370,plain,(
    ! [D_464,A_465] : ~ r2_hidden(D_464,k2_zfmisc_1(A_465,'#skF_13')) ),
    inference(resolution,[status(thm)],[c_5328,c_4722])).

tff(c_5398,plain,(
    ! [A_465] : k2_zfmisc_1(A_465,'#skF_13') = '#skF_13' ),
    inference(resolution,[status(thm)],[c_4482,c_5370])).

tff(c_80,plain,
    ( k2_zfmisc_1('#skF_12','#skF_13') != k1_xboole_0
    | k1_xboole_0 != '#skF_15' ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_4450,plain,(
    k2_zfmisc_1('#skF_12','#skF_13') != '#skF_15' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4441,c_4441,c_80])).

tff(c_4454,plain,(
    k2_zfmisc_1('#skF_12','#skF_13') != '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4452,c_4450])).

tff(c_5402,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5398,c_4454])).

tff(c_5403,plain,(
    '#skF_15' = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_4451])).

tff(c_5407,plain,(
    k1_xboole_0 = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5403,c_4441])).

tff(c_5437,plain,(
    ! [A_15] :
      ( r2_hidden('#skF_5'(A_15),A_15)
      | A_15 = '#skF_12' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5407,c_40])).

tff(c_6241,plain,(
    ! [A_541,B_542,D_543] :
      ( r2_hidden('#skF_10'(A_541,B_542,k2_zfmisc_1(A_541,B_542),D_543),A_541)
      | ~ r2_hidden(D_543,k2_zfmisc_1(A_541,B_542)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_5417,plain,(
    ! [A_18] : k4_xboole_0(A_18,'#skF_12') = A_18 ),
    inference(demodulation,[status(thm),theory(equality)],[c_5403,c_4444])).

tff(c_5635,plain,(
    ! [A_496,B_497] :
      ( ~ r2_hidden(A_496,B_497)
      | k4_xboole_0(k1_tarski(A_496),B_497) != k1_tarski(A_496) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_5653,plain,(
    ! [A_496] : ~ r2_hidden(A_496,'#skF_12') ),
    inference(superposition,[status(thm),theory(equality)],[c_5417,c_5635])).

tff(c_6283,plain,(
    ! [D_544,B_545] : ~ r2_hidden(D_544,k2_zfmisc_1('#skF_12',B_545)) ),
    inference(resolution,[status(thm)],[c_6241,c_5653])).

tff(c_6311,plain,(
    ! [B_545] : k2_zfmisc_1('#skF_12',B_545) = '#skF_12' ),
    inference(resolution,[status(thm)],[c_5437,c_6283])).

tff(c_5406,plain,(
    k2_zfmisc_1('#skF_12','#skF_13') != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5403,c_4450])).

tff(c_6315,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6311,c_5406])).

tff(c_6317,plain,(
    k1_xboole_0 = '#skF_14' ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_86,plain,
    ( k1_xboole_0 = '#skF_13'
    | k1_xboole_0 = '#skF_12'
    | k1_xboole_0 != '#skF_14' ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_6344,plain,
    ( '#skF_14' = '#skF_13'
    | '#skF_14' = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6317,c_6317,c_6317,c_86])).

tff(c_6345,plain,(
    '#skF_14' = '#skF_12' ),
    inference(splitLeft,[status(thm)],[c_6344])).

tff(c_6341,plain,(
    ! [A_15] :
      ( r2_hidden('#skF_5'(A_15),A_15)
      | A_15 = '#skF_14' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6317,c_40])).

tff(c_6346,plain,(
    ! [A_15] :
      ( r2_hidden('#skF_5'(A_15),A_15)
      | A_15 = '#skF_12' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6345,c_6341])).

tff(c_7000,plain,(
    ! [A_619,B_620,D_621] :
      ( r2_hidden('#skF_10'(A_619,B_620,k2_zfmisc_1(A_619,B_620),D_621),A_619)
      | ~ r2_hidden(D_621,k2_zfmisc_1(A_619,B_620)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_6319,plain,(
    ! [A_18] : k4_xboole_0(A_18,'#skF_14') = A_18 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6317,c_44])).

tff(c_6347,plain,(
    ! [A_18] : k4_xboole_0(A_18,'#skF_12') = A_18 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6345,c_6319])).

tff(c_6574,plain,(
    ! [A_579,B_580] :
      ( ~ r2_hidden(A_579,B_580)
      | k4_xboole_0(k1_tarski(A_579),B_580) != k1_tarski(A_579) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_6592,plain,(
    ! [A_579] : ~ r2_hidden(A_579,'#skF_12') ),
    inference(superposition,[status(thm),theory(equality)],[c_6347,c_6574])).

tff(c_7042,plain,(
    ! [D_622,B_623] : ~ r2_hidden(D_622,k2_zfmisc_1('#skF_12',B_623)) ),
    inference(resolution,[status(thm)],[c_7000,c_6592])).

tff(c_7062,plain,(
    ! [B_623] : k2_zfmisc_1('#skF_12',B_623) = '#skF_12' ),
    inference(resolution,[status(thm)],[c_6346,c_7042])).

tff(c_6316,plain,(
    k2_zfmisc_1('#skF_12','#skF_13') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_6324,plain,(
    k2_zfmisc_1('#skF_12','#skF_13') != '#skF_14' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6317,c_6316])).

tff(c_6349,plain,(
    k2_zfmisc_1('#skF_12','#skF_13') != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6345,c_6324])).

tff(c_7066,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7062,c_6349])).

tff(c_7067,plain,(
    '#skF_14' = '#skF_13' ),
    inference(splitRight,[status(thm)],[c_6344])).

tff(c_7069,plain,(
    ! [A_15] :
      ( r2_hidden('#skF_5'(A_15),A_15)
      | A_15 = '#skF_13' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7067,c_6341])).

tff(c_7878,plain,(
    ! [A_703,B_704,D_705] :
      ( r2_hidden('#skF_11'(A_703,B_704,k2_zfmisc_1(A_703,B_704),D_705),B_704)
      | ~ r2_hidden(D_705,k2_zfmisc_1(A_703,B_704)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_7070,plain,(
    ! [A_18] : k4_xboole_0(A_18,'#skF_13') = A_18 ),
    inference(demodulation,[status(thm),theory(equality)],[c_7067,c_6319])).

tff(c_7073,plain,(
    k1_xboole_0 = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7067,c_6317])).

tff(c_7127,plain,(
    ! [A_636,B_637] :
      ( r2_hidden(A_636,B_637)
      | k4_xboole_0(k1_tarski(A_636),B_637) != '#skF_13' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7073,c_76])).

tff(c_7131,plain,(
    ! [A_636] :
      ( r2_hidden(A_636,'#skF_13')
      | k1_tarski(A_636) != '#skF_13' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7070,c_7127])).

tff(c_7138,plain,(
    ! [A_640] :
      ( r2_hidden(A_640,'#skF_13')
      | k1_tarski(A_640) != '#skF_13' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7070,c_7127])).

tff(c_7117,plain,(
    ! [D_633,B_634,A_635] :
      ( ~ r2_hidden(D_633,B_634)
      | ~ r2_hidden(D_633,k4_xboole_0(A_635,B_634)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_7124,plain,(
    ! [D_633,A_18] :
      ( ~ r2_hidden(D_633,'#skF_13')
      | ~ r2_hidden(D_633,A_18) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7070,c_7117])).

tff(c_7142,plain,(
    ! [A_641,A_642] :
      ( ~ r2_hidden(A_641,A_642)
      | k1_tarski(A_641) != '#skF_13' ) ),
    inference(resolution,[status(thm)],[c_7138,c_7124])).

tff(c_7152,plain,(
    ! [A_636] : k1_tarski(A_636) != '#skF_13' ),
    inference(resolution,[status(thm)],[c_7131,c_7142])).

tff(c_7224,plain,(
    ! [A_650,B_651] :
      ( k4_xboole_0(k1_tarski(A_650),B_651) = '#skF_13'
      | ~ r2_hidden(A_650,B_651) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7073,c_78])).

tff(c_7251,plain,(
    ! [A_650] :
      ( k1_tarski(A_650) = '#skF_13'
      | ~ r2_hidden(A_650,'#skF_13') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7224,c_7070])).

tff(c_7271,plain,(
    ! [A_650] : ~ r2_hidden(A_650,'#skF_13') ),
    inference(negUnitSimplification,[status(thm)],[c_7152,c_7251])).

tff(c_7924,plain,(
    ! [D_706,A_707] : ~ r2_hidden(D_706,k2_zfmisc_1(A_707,'#skF_13')) ),
    inference(resolution,[status(thm)],[c_7878,c_7271])).

tff(c_7952,plain,(
    ! [A_707] : k2_zfmisc_1(A_707,'#skF_13') = '#skF_13' ),
    inference(resolution,[status(thm)],[c_7069,c_7924])).

tff(c_7072,plain,(
    k2_zfmisc_1('#skF_12','#skF_13') != '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7067,c_6324])).

tff(c_7956,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7952,c_7072])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:24:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.48/2.08  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.56/2.10  
% 5.56/2.10  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.56/2.11  %$ r2_hidden > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_1 > #skF_6 > #skF_15 > #skF_10 > #skF_4 > #skF_14 > #skF_13 > #skF_2 > #skF_11 > #skF_7 > #skF_9 > #skF_3 > #skF_8 > #skF_12
% 5.56/2.11  
% 5.56/2.11  %Foreground sorts:
% 5.56/2.11  
% 5.56/2.11  
% 5.56/2.11  %Background operators:
% 5.56/2.11  
% 5.56/2.11  
% 5.56/2.11  %Foreground operators:
% 5.56/2.11  tff('#skF_5', type, '#skF_5': $i > $i).
% 5.56/2.11  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.56/2.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.56/2.11  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.56/2.11  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 5.56/2.11  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.56/2.11  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.56/2.11  tff('#skF_15', type, '#skF_15': $i).
% 5.56/2.11  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.56/2.11  tff('#skF_10', type, '#skF_10': ($i * $i * $i * $i) > $i).
% 5.56/2.11  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.56/2.11  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 5.56/2.11  tff('#skF_14', type, '#skF_14': $i).
% 5.56/2.11  tff('#skF_13', type, '#skF_13': $i).
% 5.56/2.11  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.56/2.11  tff('#skF_11', type, '#skF_11': ($i * $i * $i * $i) > $i).
% 5.56/2.11  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 5.56/2.11  tff('#skF_9', type, '#skF_9': ($i * $i * $i) > $i).
% 5.56/2.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.56/2.11  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.56/2.11  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 5.56/2.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.56/2.11  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.56/2.11  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 5.56/2.11  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.56/2.11  tff('#skF_12', type, '#skF_12': $i).
% 5.56/2.11  
% 5.74/2.13  tff(f_54, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 5.74/2.13  tff(f_56, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 5.74/2.13  tff(f_58, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 5.74/2.13  tff(f_60, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.74/2.13  tff(f_81, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l35_zfmisc_1)).
% 5.74/2.13  tff(f_44, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 5.74/2.13  tff(f_88, negated_conjecture, ~(![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.74/2.13  tff(f_72, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 5.74/2.13  tff(f_77, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l33_zfmisc_1)).
% 5.74/2.13  tff(c_40, plain, (![A_15]: (r2_hidden('#skF_5'(A_15), A_15) | k1_xboole_0=A_15)), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.74/2.13  tff(c_42, plain, (![A_17]: (k3_xboole_0(A_17, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.74/2.13  tff(c_44, plain, (![A_18]: (k4_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.74/2.13  tff(c_138, plain, (![A_72, B_73]: (k4_xboole_0(A_72, k4_xboole_0(A_72, B_73))=k3_xboole_0(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.74/2.13  tff(c_160, plain, (![A_18]: (k4_xboole_0(A_18, A_18)=k3_xboole_0(A_18, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_44, c_138])).
% 5.74/2.13  tff(c_176, plain, (![A_77]: (k4_xboole_0(A_77, A_77)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_160])).
% 5.74/2.13  tff(c_76, plain, (![A_57, B_58]: (r2_hidden(A_57, B_58) | k4_xboole_0(k1_tarski(A_57), B_58)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.74/2.13  tff(c_204, plain, (![A_57]: (r2_hidden(A_57, k1_tarski(A_57)))), inference(superposition, [status(thm), theory('equality')], [c_176, c_76])).
% 5.74/2.13  tff(c_123, plain, (![A_66, B_67]: (r2_hidden(A_66, B_67) | k4_xboole_0(k1_tarski(A_66), B_67)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.74/2.13  tff(c_127, plain, (![A_66]: (r2_hidden(A_66, k1_xboole_0) | k1_tarski(A_66)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_44, c_123])).
% 5.74/2.13  tff(c_164, plain, (![D_74, B_75, A_76]: (~r2_hidden(D_74, B_75) | ~r2_hidden(D_74, k4_xboole_0(A_76, B_75)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.74/2.13  tff(c_2497, plain, (![D_255, A_256]: (~r2_hidden(D_255, k1_xboole_0) | ~r2_hidden(D_255, A_256))), inference(superposition, [status(thm), theory('equality')], [c_44, c_164])).
% 5.74/2.13  tff(c_2515, plain, (![A_259, A_260]: (~r2_hidden(A_259, A_260) | k1_tarski(A_259)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_127, c_2497])).
% 5.74/2.13  tff(c_2528, plain, (![A_57]: (k1_tarski(A_57)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_204, c_2515])).
% 5.74/2.13  tff(c_2541, plain, (![A_265, B_266]: (k4_xboole_0(k1_tarski(A_265), B_266)=k1_xboole_0 | ~r2_hidden(A_265, B_266))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.74/2.13  tff(c_2568, plain, (![A_265]: (k1_tarski(A_265)=k1_xboole_0 | ~r2_hidden(A_265, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2541, c_44])).
% 5.74/2.13  tff(c_2590, plain, (![A_265]: (~r2_hidden(A_265, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_2528, c_2568])).
% 5.74/2.13  tff(c_82, plain, (k1_xboole_0='#skF_13' | k1_xboole_0='#skF_12' | k1_xboole_0!='#skF_15'), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.74/2.13  tff(c_117, plain, (k1_xboole_0!='#skF_15'), inference(splitLeft, [status(thm)], [c_82])).
% 5.74/2.13  tff(c_84, plain, (k2_zfmisc_1('#skF_12', '#skF_13')!=k1_xboole_0 | k1_xboole_0!='#skF_14'), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.74/2.13  tff(c_116, plain, (k1_xboole_0!='#skF_14'), inference(splitLeft, [status(thm)], [c_84])).
% 5.74/2.13  tff(c_229, plain, (![D_80, A_81]: (~r2_hidden(D_80, k1_xboole_0) | ~r2_hidden(D_80, A_81))), inference(superposition, [status(thm), theory('equality')], [c_44, c_164])).
% 5.74/2.13  tff(c_247, plain, (![A_84, A_85]: (~r2_hidden(A_84, A_85) | k1_tarski(A_84)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_127, c_229])).
% 5.74/2.13  tff(c_260, plain, (![A_57]: (k1_tarski(A_57)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_204, c_247])).
% 5.74/2.13  tff(c_270, plain, (![A_87, B_88]: (k4_xboole_0(k1_tarski(A_87), B_88)=k1_xboole_0 | ~r2_hidden(A_87, B_88))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.74/2.13  tff(c_297, plain, (![A_87]: (k1_tarski(A_87)=k1_xboole_0 | ~r2_hidden(A_87, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_270, c_44])).
% 5.74/2.13  tff(c_319, plain, (![A_87]: (~r2_hidden(A_87, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_260, c_297])).
% 5.74/2.13  tff(c_90, plain, (k1_xboole_0='#skF_13' | k1_xboole_0='#skF_12' | k2_zfmisc_1('#skF_14', '#skF_15')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.74/2.13  tff(c_264, plain, (k2_zfmisc_1('#skF_14', '#skF_15')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_90])).
% 5.74/2.13  tff(c_728, plain, (![E_124, F_125, A_126, B_127]: (r2_hidden(k4_tarski(E_124, F_125), k2_zfmisc_1(A_126, B_127)) | ~r2_hidden(F_125, B_127) | ~r2_hidden(E_124, A_126))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.74/2.13  tff(c_733, plain, (![E_124, F_125]: (r2_hidden(k4_tarski(E_124, F_125), k1_xboole_0) | ~r2_hidden(F_125, '#skF_15') | ~r2_hidden(E_124, '#skF_14'))), inference(superposition, [status(thm), theory('equality')], [c_264, c_728])).
% 5.74/2.13  tff(c_735, plain, (![F_125, E_124]: (~r2_hidden(F_125, '#skF_15') | ~r2_hidden(E_124, '#skF_14'))), inference(negUnitSimplification, [status(thm)], [c_319, c_733])).
% 5.74/2.13  tff(c_737, plain, (![E_128]: (~r2_hidden(E_128, '#skF_14'))), inference(splitLeft, [status(thm)], [c_735])).
% 5.74/2.13  tff(c_741, plain, (k1_xboole_0='#skF_14'), inference(resolution, [status(thm)], [c_40, c_737])).
% 5.74/2.13  tff(c_745, plain, $false, inference(negUnitSimplification, [status(thm)], [c_116, c_741])).
% 5.74/2.13  tff(c_747, plain, (![F_129]: (~r2_hidden(F_129, '#skF_15'))), inference(splitRight, [status(thm)], [c_735])).
% 5.74/2.13  tff(c_751, plain, (k1_xboole_0='#skF_15'), inference(resolution, [status(thm)], [c_40, c_747])).
% 5.74/2.13  tff(c_755, plain, $false, inference(negUnitSimplification, [status(thm)], [c_117, c_751])).
% 5.74/2.13  tff(c_756, plain, (k1_xboole_0='#skF_12' | k1_xboole_0='#skF_13'), inference(splitRight, [status(thm)], [c_90])).
% 5.74/2.13  tff(c_759, plain, (k1_xboole_0='#skF_13'), inference(splitLeft, [status(thm)], [c_756])).
% 5.74/2.13  tff(c_766, plain, (![A_15]: (r2_hidden('#skF_5'(A_15), A_15) | A_15='#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_759, c_40])).
% 5.74/2.13  tff(c_1597, plain, (![A_193, B_194, D_195]: (r2_hidden('#skF_11'(A_193, B_194, k2_zfmisc_1(A_193, B_194), D_195), B_194) | ~r2_hidden(D_195, k2_zfmisc_1(A_193, B_194)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.74/2.13  tff(c_760, plain, (![A_57]: (k1_tarski(A_57)!='#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_759, c_260])).
% 5.74/2.13  tff(c_78, plain, (![A_57, B_58]: (k4_xboole_0(k1_tarski(A_57), B_58)=k1_xboole_0 | ~r2_hidden(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.74/2.13  tff(c_870, plain, (![A_143, B_144]: (k4_xboole_0(k1_tarski(A_143), B_144)='#skF_13' | ~r2_hidden(A_143, B_144))), inference(demodulation, [status(thm), theory('equality')], [c_759, c_78])).
% 5.74/2.13  tff(c_770, plain, (![A_18]: (k4_xboole_0(A_18, '#skF_13')=A_18)), inference(demodulation, [status(thm), theory('equality')], [c_759, c_44])).
% 5.74/2.13  tff(c_881, plain, (![A_143]: (k1_tarski(A_143)='#skF_13' | ~r2_hidden(A_143, '#skF_13'))), inference(superposition, [status(thm), theory('equality')], [c_870, c_770])).
% 5.74/2.13  tff(c_914, plain, (![A_143]: (~r2_hidden(A_143, '#skF_13'))), inference(negUnitSimplification, [status(thm)], [c_760, c_881])).
% 5.74/2.13  tff(c_1639, plain, (![D_196, A_197]: (~r2_hidden(D_196, k2_zfmisc_1(A_197, '#skF_13')))), inference(resolution, [status(thm)], [c_1597, c_914])).
% 5.74/2.13  tff(c_1667, plain, (![A_197]: (k2_zfmisc_1(A_197, '#skF_13')='#skF_13')), inference(resolution, [status(thm)], [c_766, c_1639])).
% 5.74/2.13  tff(c_88, plain, (k2_zfmisc_1('#skF_12', '#skF_13')!=k1_xboole_0 | k2_zfmisc_1('#skF_14', '#skF_15')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.74/2.13  tff(c_228, plain, (k2_zfmisc_1('#skF_12', '#skF_13')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_88])).
% 5.74/2.13  tff(c_763, plain, (k2_zfmisc_1('#skF_12', '#skF_13')!='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_759, c_228])).
% 5.74/2.13  tff(c_1671, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1667, c_763])).
% 5.74/2.13  tff(c_1672, plain, (k1_xboole_0='#skF_12'), inference(splitRight, [status(thm)], [c_756])).
% 5.74/2.13  tff(c_1682, plain, (![A_15]: (r2_hidden('#skF_5'(A_15), A_15) | A_15='#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_1672, c_40])).
% 5.74/2.13  tff(c_2423, plain, (![A_250, B_251, D_252]: (r2_hidden('#skF_10'(A_250, B_251, k2_zfmisc_1(A_250, B_251), D_252), A_250) | ~r2_hidden(D_252, k2_zfmisc_1(A_250, B_251)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.74/2.13  tff(c_1676, plain, (![A_57]: (k1_tarski(A_57)!='#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_1672, c_260])).
% 5.74/2.13  tff(c_1728, plain, (![A_201, B_202]: (k4_xboole_0(k1_tarski(A_201), B_202)='#skF_12' | ~r2_hidden(A_201, B_202))), inference(demodulation, [status(thm), theory('equality')], [c_1672, c_78])).
% 5.74/2.13  tff(c_1686, plain, (![A_18]: (k4_xboole_0(A_18, '#skF_12')=A_18)), inference(demodulation, [status(thm), theory('equality')], [c_1672, c_44])).
% 5.74/2.13  tff(c_1735, plain, (![A_201]: (k1_tarski(A_201)='#skF_12' | ~r2_hidden(A_201, '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_1728, c_1686])).
% 5.74/2.13  tff(c_1761, plain, (![A_201]: (~r2_hidden(A_201, '#skF_12'))), inference(negUnitSimplification, [status(thm)], [c_1676, c_1735])).
% 5.74/2.13  tff(c_2461, plain, (![D_253, B_254]: (~r2_hidden(D_253, k2_zfmisc_1('#skF_12', B_254)))), inference(resolution, [status(thm)], [c_2423, c_1761])).
% 5.74/2.13  tff(c_2481, plain, (![B_254]: (k2_zfmisc_1('#skF_12', B_254)='#skF_12')), inference(resolution, [status(thm)], [c_1682, c_2461])).
% 5.74/2.13  tff(c_1679, plain, (k2_zfmisc_1('#skF_12', '#skF_13')!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_1672, c_228])).
% 5.74/2.13  tff(c_2485, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2481, c_1679])).
% 5.74/2.13  tff(c_2487, plain, (k2_zfmisc_1('#skF_12', '#skF_13')=k1_xboole_0), inference(splitRight, [status(thm)], [c_88])).
% 5.74/2.13  tff(c_3127, plain, (![E_300, F_301, A_302, B_303]: (r2_hidden(k4_tarski(E_300, F_301), k2_zfmisc_1(A_302, B_303)) | ~r2_hidden(F_301, B_303) | ~r2_hidden(E_300, A_302))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.74/2.13  tff(c_3132, plain, (![E_300, F_301]: (r2_hidden(k4_tarski(E_300, F_301), k1_xboole_0) | ~r2_hidden(F_301, '#skF_13') | ~r2_hidden(E_300, '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_2487, c_3127])).
% 5.74/2.13  tff(c_3137, plain, (![F_301, E_300]: (~r2_hidden(F_301, '#skF_13') | ~r2_hidden(E_300, '#skF_12'))), inference(negUnitSimplification, [status(thm)], [c_2590, c_3132])).
% 5.74/2.13  tff(c_3142, plain, (![E_304]: (~r2_hidden(E_304, '#skF_12'))), inference(splitLeft, [status(thm)], [c_3137])).
% 5.74/2.13  tff(c_3152, plain, (k1_xboole_0='#skF_12'), inference(resolution, [status(thm)], [c_40, c_3142])).
% 5.74/2.13  tff(c_3166, plain, ('#skF_15'!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_3152, c_117])).
% 5.74/2.13  tff(c_3736, plain, (![A_342]: (r2_hidden('#skF_5'(A_342), A_342) | A_342='#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_3152, c_40])).
% 5.74/2.13  tff(c_3167, plain, ('#skF_14'!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_3152, c_116])).
% 5.74/2.13  tff(c_3586, plain, (![A_329]: (r2_hidden('#skF_5'(A_329), A_329) | A_329='#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_3152, c_40])).
% 5.74/2.13  tff(c_2486, plain, (k2_zfmisc_1('#skF_14', '#skF_15')=k1_xboole_0), inference(splitRight, [status(thm)], [c_88])).
% 5.74/2.13  tff(c_3135, plain, (![E_300, F_301]: (r2_hidden(k4_tarski(E_300, F_301), k1_xboole_0) | ~r2_hidden(F_301, '#skF_15') | ~r2_hidden(E_300, '#skF_14'))), inference(superposition, [status(thm), theory('equality')], [c_2486, c_3127])).
% 5.74/2.13  tff(c_3138, plain, (![F_301, E_300]: (~r2_hidden(F_301, '#skF_15') | ~r2_hidden(E_300, '#skF_14'))), inference(negUnitSimplification, [status(thm)], [c_2590, c_3135])).
% 5.74/2.13  tff(c_3490, plain, (![E_300]: (~r2_hidden(E_300, '#skF_14'))), inference(splitLeft, [status(thm)], [c_3138])).
% 5.74/2.13  tff(c_3606, plain, ('#skF_14'='#skF_12'), inference(resolution, [status(thm)], [c_3586, c_3490])).
% 5.74/2.13  tff(c_3639, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3167, c_3606])).
% 5.74/2.13  tff(c_3640, plain, (![F_301]: (~r2_hidden(F_301, '#skF_15'))), inference(splitRight, [status(thm)], [c_3138])).
% 5.74/2.13  tff(c_3756, plain, ('#skF_15'='#skF_12'), inference(resolution, [status(thm)], [c_3736, c_3640])).
% 5.74/2.13  tff(c_3789, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3166, c_3756])).
% 5.74/2.13  tff(c_3791, plain, (![F_343]: (~r2_hidden(F_343, '#skF_13'))), inference(splitRight, [status(thm)], [c_3137])).
% 5.74/2.13  tff(c_3801, plain, (k1_xboole_0='#skF_13'), inference(resolution, [status(thm)], [c_40, c_3791])).
% 5.74/2.13  tff(c_3815, plain, ('#skF_15'!='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_3801, c_117])).
% 5.74/2.13  tff(c_4386, plain, (![A_381]: (r2_hidden('#skF_5'(A_381), A_381) | A_381='#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_3801, c_40])).
% 5.74/2.13  tff(c_3816, plain, ('#skF_14'!='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_3801, c_116])).
% 5.74/2.13  tff(c_4234, plain, (![A_368]: (r2_hidden('#skF_5'(A_368), A_368) | A_368='#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_3801, c_40])).
% 5.74/2.13  tff(c_4139, plain, (![E_300]: (~r2_hidden(E_300, '#skF_14'))), inference(splitLeft, [status(thm)], [c_3138])).
% 5.74/2.13  tff(c_4254, plain, ('#skF_14'='#skF_13'), inference(resolution, [status(thm)], [c_4234, c_4139])).
% 5.74/2.13  tff(c_4287, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3816, c_4254])).
% 5.74/2.13  tff(c_4288, plain, (![F_301]: (~r2_hidden(F_301, '#skF_15'))), inference(splitRight, [status(thm)], [c_3138])).
% 5.74/2.13  tff(c_4406, plain, ('#skF_15'='#skF_13'), inference(resolution, [status(thm)], [c_4386, c_4288])).
% 5.74/2.13  tff(c_4439, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3815, c_4406])).
% 5.74/2.13  tff(c_4441, plain, (k1_xboole_0='#skF_15'), inference(splitRight, [status(thm)], [c_82])).
% 5.74/2.13  tff(c_4440, plain, (k1_xboole_0='#skF_12' | k1_xboole_0='#skF_13'), inference(splitRight, [status(thm)], [c_82])).
% 5.74/2.13  tff(c_4451, plain, ('#skF_15'='#skF_12' | '#skF_15'='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_4441, c_4441, c_4440])).
% 5.74/2.13  tff(c_4452, plain, ('#skF_15'='#skF_13'), inference(splitLeft, [status(thm)], [c_4451])).
% 5.74/2.13  tff(c_4455, plain, (k1_xboole_0='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_4452, c_4441])).
% 5.74/2.13  tff(c_4482, plain, (![A_15]: (r2_hidden('#skF_5'(A_15), A_15) | A_15='#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_4455, c_40])).
% 5.74/2.13  tff(c_5328, plain, (![A_461, B_462, D_463]: (r2_hidden('#skF_11'(A_461, B_462, k2_zfmisc_1(A_461, B_462), D_463), B_462) | ~r2_hidden(D_463, k2_zfmisc_1(A_461, B_462)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.74/2.13  tff(c_4444, plain, (![A_18]: (k4_xboole_0(A_18, '#skF_15')=A_18)), inference(demodulation, [status(thm), theory('equality')], [c_4441, c_44])).
% 5.74/2.13  tff(c_4464, plain, (![A_18]: (k4_xboole_0(A_18, '#skF_13')=A_18)), inference(demodulation, [status(thm), theory('equality')], [c_4452, c_4444])).
% 5.74/2.13  tff(c_4622, plain, (![A_400, B_401]: (r2_hidden(A_400, B_401) | k4_xboole_0(k1_tarski(A_400), B_401)!='#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_4455, c_76])).
% 5.74/2.13  tff(c_4641, plain, (![A_403]: (r2_hidden(A_403, '#skF_13') | k1_tarski(A_403)!='#skF_13')), inference(superposition, [status(thm), theory('equality')], [c_4464, c_4622])).
% 5.74/2.13  tff(c_4443, plain, (![A_17]: (k3_xboole_0(A_17, '#skF_15')='#skF_15')), inference(demodulation, [status(thm), theory('equality')], [c_4441, c_4441, c_42])).
% 5.74/2.13  tff(c_4474, plain, (![A_17]: (k3_xboole_0(A_17, '#skF_13')='#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_4452, c_4452, c_4443])).
% 5.74/2.13  tff(c_4485, plain, (![A_385, B_386]: (k4_xboole_0(A_385, k4_xboole_0(A_385, B_386))=k3_xboole_0(A_385, B_386))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.74/2.13  tff(c_4500, plain, (![A_18]: (k4_xboole_0(A_18, A_18)=k3_xboole_0(A_18, '#skF_13'))), inference(superposition, [status(thm), theory('equality')], [c_4464, c_4485])).
% 5.74/2.13  tff(c_4503, plain, (![A_18]: (k4_xboole_0(A_18, A_18)='#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_4474, c_4500])).
% 5.74/2.13  tff(c_4597, plain, (![D_395, A_396, B_397]: (r2_hidden(D_395, A_396) | ~r2_hidden(D_395, k4_xboole_0(A_396, B_397)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.74/2.13  tff(c_4603, plain, (![D_395, A_18]: (r2_hidden(D_395, A_18) | ~r2_hidden(D_395, '#skF_13'))), inference(superposition, [status(thm), theory('equality')], [c_4503, c_4597])).
% 5.74/2.13  tff(c_4647, plain, (![A_403, A_18]: (r2_hidden(A_403, A_18) | k1_tarski(A_403)!='#skF_13')), inference(resolution, [status(thm)], [c_4641, c_4603])).
% 5.74/2.13  tff(c_4664, plain, (![D_406, B_407, A_408]: (~r2_hidden(D_406, B_407) | ~r2_hidden(D_406, k4_xboole_0(A_408, B_407)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.74/2.13  tff(c_4697, plain, (![A_411, B_412]: (~r2_hidden(A_411, B_412) | k1_tarski(A_411)!='#skF_13')), inference(resolution, [status(thm)], [c_4647, c_4664])).
% 5.74/2.13  tff(c_4710, plain, (![A_403]: (k1_tarski(A_403)!='#skF_13')), inference(resolution, [status(thm)], [c_4647, c_4697])).
% 5.74/2.13  tff(c_4549, plain, (![A_392, B_393]: (k4_xboole_0(k1_tarski(A_392), B_393)='#skF_13' | ~r2_hidden(A_392, B_393))), inference(demodulation, [status(thm), theory('equality')], [c_4455, c_78])).
% 5.74/2.13  tff(c_4567, plain, (![A_392]: (k1_tarski(A_392)='#skF_13' | ~r2_hidden(A_392, '#skF_13'))), inference(superposition, [status(thm), theory('equality')], [c_4549, c_4464])).
% 5.74/2.13  tff(c_4722, plain, (![A_392]: (~r2_hidden(A_392, '#skF_13'))), inference(negUnitSimplification, [status(thm)], [c_4710, c_4567])).
% 5.74/2.13  tff(c_5370, plain, (![D_464, A_465]: (~r2_hidden(D_464, k2_zfmisc_1(A_465, '#skF_13')))), inference(resolution, [status(thm)], [c_5328, c_4722])).
% 5.74/2.13  tff(c_5398, plain, (![A_465]: (k2_zfmisc_1(A_465, '#skF_13')='#skF_13')), inference(resolution, [status(thm)], [c_4482, c_5370])).
% 5.74/2.13  tff(c_80, plain, (k2_zfmisc_1('#skF_12', '#skF_13')!=k1_xboole_0 | k1_xboole_0!='#skF_15'), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.74/2.13  tff(c_4450, plain, (k2_zfmisc_1('#skF_12', '#skF_13')!='#skF_15'), inference(demodulation, [status(thm), theory('equality')], [c_4441, c_4441, c_80])).
% 5.74/2.14  tff(c_4454, plain, (k2_zfmisc_1('#skF_12', '#skF_13')!='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_4452, c_4450])).
% 5.74/2.14  tff(c_5402, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5398, c_4454])).
% 5.74/2.14  tff(c_5403, plain, ('#skF_15'='#skF_12'), inference(splitRight, [status(thm)], [c_4451])).
% 5.74/2.14  tff(c_5407, plain, (k1_xboole_0='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_5403, c_4441])).
% 5.74/2.14  tff(c_5437, plain, (![A_15]: (r2_hidden('#skF_5'(A_15), A_15) | A_15='#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_5407, c_40])).
% 5.74/2.14  tff(c_6241, plain, (![A_541, B_542, D_543]: (r2_hidden('#skF_10'(A_541, B_542, k2_zfmisc_1(A_541, B_542), D_543), A_541) | ~r2_hidden(D_543, k2_zfmisc_1(A_541, B_542)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.74/2.14  tff(c_5417, plain, (![A_18]: (k4_xboole_0(A_18, '#skF_12')=A_18)), inference(demodulation, [status(thm), theory('equality')], [c_5403, c_4444])).
% 5.74/2.14  tff(c_5635, plain, (![A_496, B_497]: (~r2_hidden(A_496, B_497) | k4_xboole_0(k1_tarski(A_496), B_497)!=k1_tarski(A_496))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.74/2.14  tff(c_5653, plain, (![A_496]: (~r2_hidden(A_496, '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_5417, c_5635])).
% 5.74/2.14  tff(c_6283, plain, (![D_544, B_545]: (~r2_hidden(D_544, k2_zfmisc_1('#skF_12', B_545)))), inference(resolution, [status(thm)], [c_6241, c_5653])).
% 5.74/2.14  tff(c_6311, plain, (![B_545]: (k2_zfmisc_1('#skF_12', B_545)='#skF_12')), inference(resolution, [status(thm)], [c_5437, c_6283])).
% 5.74/2.14  tff(c_5406, plain, (k2_zfmisc_1('#skF_12', '#skF_13')!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_5403, c_4450])).
% 5.74/2.14  tff(c_6315, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6311, c_5406])).
% 5.74/2.14  tff(c_6317, plain, (k1_xboole_0='#skF_14'), inference(splitRight, [status(thm)], [c_84])).
% 5.74/2.14  tff(c_86, plain, (k1_xboole_0='#skF_13' | k1_xboole_0='#skF_12' | k1_xboole_0!='#skF_14'), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.74/2.14  tff(c_6344, plain, ('#skF_14'='#skF_13' | '#skF_14'='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_6317, c_6317, c_6317, c_86])).
% 5.74/2.14  tff(c_6345, plain, ('#skF_14'='#skF_12'), inference(splitLeft, [status(thm)], [c_6344])).
% 5.74/2.14  tff(c_6341, plain, (![A_15]: (r2_hidden('#skF_5'(A_15), A_15) | A_15='#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_6317, c_40])).
% 5.74/2.14  tff(c_6346, plain, (![A_15]: (r2_hidden('#skF_5'(A_15), A_15) | A_15='#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_6345, c_6341])).
% 5.74/2.14  tff(c_7000, plain, (![A_619, B_620, D_621]: (r2_hidden('#skF_10'(A_619, B_620, k2_zfmisc_1(A_619, B_620), D_621), A_619) | ~r2_hidden(D_621, k2_zfmisc_1(A_619, B_620)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.74/2.14  tff(c_6319, plain, (![A_18]: (k4_xboole_0(A_18, '#skF_14')=A_18)), inference(demodulation, [status(thm), theory('equality')], [c_6317, c_44])).
% 5.74/2.14  tff(c_6347, plain, (![A_18]: (k4_xboole_0(A_18, '#skF_12')=A_18)), inference(demodulation, [status(thm), theory('equality')], [c_6345, c_6319])).
% 5.74/2.14  tff(c_6574, plain, (![A_579, B_580]: (~r2_hidden(A_579, B_580) | k4_xboole_0(k1_tarski(A_579), B_580)!=k1_tarski(A_579))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.74/2.14  tff(c_6592, plain, (![A_579]: (~r2_hidden(A_579, '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_6347, c_6574])).
% 5.74/2.14  tff(c_7042, plain, (![D_622, B_623]: (~r2_hidden(D_622, k2_zfmisc_1('#skF_12', B_623)))), inference(resolution, [status(thm)], [c_7000, c_6592])).
% 5.74/2.14  tff(c_7062, plain, (![B_623]: (k2_zfmisc_1('#skF_12', B_623)='#skF_12')), inference(resolution, [status(thm)], [c_6346, c_7042])).
% 5.74/2.14  tff(c_6316, plain, (k2_zfmisc_1('#skF_12', '#skF_13')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_84])).
% 5.74/2.14  tff(c_6324, plain, (k2_zfmisc_1('#skF_12', '#skF_13')!='#skF_14'), inference(demodulation, [status(thm), theory('equality')], [c_6317, c_6316])).
% 5.74/2.14  tff(c_6349, plain, (k2_zfmisc_1('#skF_12', '#skF_13')!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_6345, c_6324])).
% 5.74/2.14  tff(c_7066, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7062, c_6349])).
% 5.74/2.14  tff(c_7067, plain, ('#skF_14'='#skF_13'), inference(splitRight, [status(thm)], [c_6344])).
% 5.74/2.14  tff(c_7069, plain, (![A_15]: (r2_hidden('#skF_5'(A_15), A_15) | A_15='#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_7067, c_6341])).
% 5.74/2.14  tff(c_7878, plain, (![A_703, B_704, D_705]: (r2_hidden('#skF_11'(A_703, B_704, k2_zfmisc_1(A_703, B_704), D_705), B_704) | ~r2_hidden(D_705, k2_zfmisc_1(A_703, B_704)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.74/2.14  tff(c_7070, plain, (![A_18]: (k4_xboole_0(A_18, '#skF_13')=A_18)), inference(demodulation, [status(thm), theory('equality')], [c_7067, c_6319])).
% 5.74/2.14  tff(c_7073, plain, (k1_xboole_0='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_7067, c_6317])).
% 5.74/2.14  tff(c_7127, plain, (![A_636, B_637]: (r2_hidden(A_636, B_637) | k4_xboole_0(k1_tarski(A_636), B_637)!='#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_7073, c_76])).
% 5.74/2.14  tff(c_7131, plain, (![A_636]: (r2_hidden(A_636, '#skF_13') | k1_tarski(A_636)!='#skF_13')), inference(superposition, [status(thm), theory('equality')], [c_7070, c_7127])).
% 5.74/2.14  tff(c_7138, plain, (![A_640]: (r2_hidden(A_640, '#skF_13') | k1_tarski(A_640)!='#skF_13')), inference(superposition, [status(thm), theory('equality')], [c_7070, c_7127])).
% 5.74/2.14  tff(c_7117, plain, (![D_633, B_634, A_635]: (~r2_hidden(D_633, B_634) | ~r2_hidden(D_633, k4_xboole_0(A_635, B_634)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.74/2.14  tff(c_7124, plain, (![D_633, A_18]: (~r2_hidden(D_633, '#skF_13') | ~r2_hidden(D_633, A_18))), inference(superposition, [status(thm), theory('equality')], [c_7070, c_7117])).
% 5.74/2.14  tff(c_7142, plain, (![A_641, A_642]: (~r2_hidden(A_641, A_642) | k1_tarski(A_641)!='#skF_13')), inference(resolution, [status(thm)], [c_7138, c_7124])).
% 5.74/2.14  tff(c_7152, plain, (![A_636]: (k1_tarski(A_636)!='#skF_13')), inference(resolution, [status(thm)], [c_7131, c_7142])).
% 5.74/2.14  tff(c_7224, plain, (![A_650, B_651]: (k4_xboole_0(k1_tarski(A_650), B_651)='#skF_13' | ~r2_hidden(A_650, B_651))), inference(demodulation, [status(thm), theory('equality')], [c_7073, c_78])).
% 5.74/2.14  tff(c_7251, plain, (![A_650]: (k1_tarski(A_650)='#skF_13' | ~r2_hidden(A_650, '#skF_13'))), inference(superposition, [status(thm), theory('equality')], [c_7224, c_7070])).
% 5.74/2.14  tff(c_7271, plain, (![A_650]: (~r2_hidden(A_650, '#skF_13'))), inference(negUnitSimplification, [status(thm)], [c_7152, c_7251])).
% 5.74/2.14  tff(c_7924, plain, (![D_706, A_707]: (~r2_hidden(D_706, k2_zfmisc_1(A_707, '#skF_13')))), inference(resolution, [status(thm)], [c_7878, c_7271])).
% 5.74/2.14  tff(c_7952, plain, (![A_707]: (k2_zfmisc_1(A_707, '#skF_13')='#skF_13')), inference(resolution, [status(thm)], [c_7069, c_7924])).
% 5.74/2.14  tff(c_7072, plain, (k2_zfmisc_1('#skF_12', '#skF_13')!='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_7067, c_6324])).
% 5.74/2.14  tff(c_7956, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7952, c_7072])).
% 5.74/2.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.74/2.14  
% 5.74/2.14  Inference rules
% 5.74/2.14  ----------------------
% 5.74/2.14  #Ref     : 0
% 5.74/2.14  #Sup     : 1772
% 5.74/2.14  #Fact    : 0
% 5.74/2.14  #Define  : 0
% 5.74/2.14  #Split   : 12
% 5.74/2.14  #Chain   : 0
% 5.74/2.14  #Close   : 0
% 5.74/2.14  
% 5.74/2.14  Ordering : KBO
% 5.74/2.14  
% 5.74/2.14  Simplification rules
% 5.74/2.14  ----------------------
% 5.74/2.14  #Subsume      : 344
% 5.74/2.14  #Demod        : 566
% 5.74/2.14  #Tautology    : 754
% 5.74/2.14  #SimpNegUnit  : 231
% 5.74/2.14  #BackRed      : 98
% 5.74/2.14  
% 5.74/2.14  #Partial instantiations: 0
% 5.74/2.14  #Strategies tried      : 1
% 5.74/2.14  
% 5.74/2.14  Timing (in seconds)
% 5.74/2.14  ----------------------
% 5.74/2.14  Preprocessing        : 0.35
% 5.74/2.14  Parsing              : 0.17
% 5.74/2.14  CNF conversion       : 0.03
% 5.74/2.14  Main loop            : 0.99
% 5.74/2.14  Inferencing          : 0.38
% 5.74/2.14  Reduction            : 0.29
% 5.74/2.14  Demodulation         : 0.19
% 5.74/2.14  BG Simplification    : 0.05
% 5.74/2.14  Subsumption          : 0.17
% 5.74/2.14  Abstraction          : 0.05
% 5.74/2.14  MUC search           : 0.00
% 5.74/2.14  Cooper               : 0.00
% 5.74/2.14  Total                : 1.40
% 5.74/2.14  Index Insertion      : 0.00
% 5.74/2.14  Index Deletion       : 0.00
% 5.74/2.14  Index Matching       : 0.00
% 5.74/2.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
