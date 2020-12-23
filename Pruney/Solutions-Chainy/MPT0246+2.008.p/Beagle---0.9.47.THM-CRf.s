%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:01 EST 2020

% Result     : Theorem 6.30s
% Output     : CNFRefutation 6.30s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 937 expanded)
%              Number of leaves         :   24 ( 319 expanded)
%              Depth                    :   19
%              Number of atoms          :  163 (2133 expanded)
%              Number of equality atoms :   70 (1075 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_88,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( A != k1_tarski(B)
          & A != k1_xboole_0
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & C != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_zfmisc_1)).

tff(f_40,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_63,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_65,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_61,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_56,plain,(
    k1_tarski('#skF_6') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_54,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_70,plain,(
    ! [A_34] :
      ( r2_hidden('#skF_2'(A_34),A_34)
      | k1_xboole_0 = A_34 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_52,plain,(
    ! [C_27] :
      ( C_27 = '#skF_6'
      | ~ r2_hidden(C_27,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_74,plain,
    ( '#skF_2'('#skF_5') = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_70,c_52])).

tff(c_77,plain,(
    '#skF_2'('#skF_5') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_74])).

tff(c_8,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_81,plain,
    ( r2_hidden('#skF_6','#skF_5')
    | k1_xboole_0 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_8])).

tff(c_84,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_81])).

tff(c_173,plain,(
    ! [C_63,B_64,A_65] :
      ( r2_hidden(C_63,B_64)
      | ~ r2_hidden(C_63,A_65)
      | ~ r1_tarski(A_65,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_198,plain,(
    ! [B_64] :
      ( r2_hidden('#skF_6',B_64)
      | ~ r1_tarski('#skF_5',B_64) ) ),
    inference(resolution,[status(thm)],[c_84,c_173])).

tff(c_40,plain,(
    ! [A_17] : k2_tarski(A_17,A_17) = k1_tarski(A_17) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_319,plain,(
    ! [A_91,B_92,C_93] :
      ( r1_tarski(k2_tarski(A_91,B_92),C_93)
      | ~ r2_hidden(B_92,C_93)
      | ~ r2_hidden(A_91,C_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_342,plain,(
    ! [A_17,C_93] :
      ( r1_tarski(k1_tarski(A_17),C_93)
      | ~ r2_hidden(A_17,C_93)
      | ~ r2_hidden(A_17,C_93) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_319])).

tff(c_199,plain,(
    ! [A_6,B_64] :
      ( r2_hidden('#skF_2'(A_6),B_64)
      | ~ r1_tarski(A_6,B_64)
      | k1_xboole_0 = A_6 ) ),
    inference(resolution,[status(thm)],[c_8,c_173])).

tff(c_42,plain,(
    ! [A_18,B_19] : k1_enumset1(A_18,A_18,B_19) = k2_tarski(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_509,plain,(
    ! [E_109,C_110,B_111,A_112] :
      ( E_109 = C_110
      | E_109 = B_111
      | E_109 = A_112
      | ~ r2_hidden(E_109,k1_enumset1(A_112,B_111,C_110)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_578,plain,(
    ! [E_117,B_118,A_119] :
      ( E_117 = B_118
      | E_117 = A_119
      | E_117 = A_119
      | ~ r2_hidden(E_117,k2_tarski(A_119,B_118)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_509])).

tff(c_703,plain,(
    ! [E_130,A_131] :
      ( E_130 = A_131
      | E_130 = A_131
      | E_130 = A_131
      | ~ r2_hidden(E_130,k1_tarski(A_131)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_578])).

tff(c_762,plain,(
    ! [A_133,A_134] :
      ( A_133 = '#skF_2'(A_134)
      | ~ r1_tarski(A_134,k1_tarski(A_133))
      | k1_xboole_0 = A_134 ) ),
    inference(resolution,[status(thm)],[c_199,c_703])).

tff(c_912,plain,(
    ! [A_149,A_150] :
      ( A_149 = '#skF_2'(k1_tarski(A_150))
      | k1_tarski(A_150) = k1_xboole_0
      | ~ r2_hidden(A_150,k1_tarski(A_149)) ) ),
    inference(resolution,[status(thm)],[c_342,c_762])).

tff(c_943,plain,(
    ! [A_149] :
      ( A_149 = '#skF_2'(k1_tarski('#skF_6'))
      | k1_tarski('#skF_6') = k1_xboole_0
      | ~ r1_tarski('#skF_5',k1_tarski(A_149)) ) ),
    inference(resolution,[status(thm)],[c_198,c_912])).

tff(c_971,plain,(
    k1_tarski('#skF_6') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_943])).

tff(c_93,plain,(
    ! [A_41,B_42] : k1_enumset1(A_41,A_41,B_42) = k2_tarski(A_41,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_20,plain,(
    ! [E_16,A_10,C_12] : r2_hidden(E_16,k1_enumset1(A_10,E_16,C_12)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_111,plain,(
    ! [A_43,B_44] : r2_hidden(A_43,k2_tarski(A_43,B_44)) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_20])).

tff(c_114,plain,(
    ! [A_17] : r2_hidden(A_17,k1_tarski(A_17)) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_111])).

tff(c_1871,plain,(
    r2_hidden('#skF_6',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_971,c_114])).

tff(c_157,plain,(
    ! [A_60,B_61] :
      ( r2_hidden('#skF_1'(A_60,B_61),A_60)
      | r1_tarski(A_60,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_168,plain,(
    ! [B_61] :
      ( '#skF_1'('#skF_5',B_61) = '#skF_6'
      | r1_tarski('#skF_5',B_61) ) ),
    inference(resolution,[status(thm)],[c_157,c_52])).

tff(c_350,plain,(
    ! [A_94,C_95] :
      ( r1_tarski(k1_tarski(A_94),C_95)
      | ~ r2_hidden(A_94,C_95)
      | ~ r2_hidden(A_94,C_95) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_319])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( B_9 = A_8
      | ~ r1_tarski(B_9,A_8)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_374,plain,(
    ! [A_96,C_97] :
      ( k1_tarski(A_96) = C_97
      | ~ r1_tarski(C_97,k1_tarski(A_96))
      | ~ r2_hidden(A_96,C_97) ) ),
    inference(resolution,[status(thm)],[c_350,c_10])).

tff(c_393,plain,(
    ! [A_96] :
      ( k1_tarski(A_96) = '#skF_5'
      | ~ r2_hidden(A_96,'#skF_5')
      | '#skF_1'('#skF_5',k1_tarski(A_96)) = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_168,c_374])).

tff(c_1856,plain,
    ( k1_tarski('#skF_6') = '#skF_5'
    | ~ r2_hidden('#skF_6','#skF_5')
    | '#skF_1'('#skF_5',k1_xboole_0) = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_971,c_393])).

tff(c_1886,plain,
    ( k1_xboole_0 = '#skF_5'
    | '#skF_1'('#skF_5',k1_xboole_0) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_971,c_1856])).

tff(c_1887,plain,(
    '#skF_1'('#skF_5',k1_xboole_0) = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1886])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1909,plain,
    ( ~ r2_hidden('#skF_6',k1_xboole_0)
    | r1_tarski('#skF_5',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1887,c_4])).

tff(c_1930,plain,(
    r1_tarski('#skF_5',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1871,c_1909])).

tff(c_1937,plain,
    ( k1_xboole_0 = '#skF_5'
    | ~ r1_tarski(k1_xboole_0,'#skF_5') ),
    inference(resolution,[status(thm)],[c_1930,c_10])).

tff(c_1945,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1937])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_434,plain,(
    ! [A_102,B_103,B_104] :
      ( r2_hidden('#skF_1'(A_102,B_103),B_104)
      | ~ r1_tarski(A_102,B_104)
      | r1_tarski(A_102,B_103) ) ),
    inference(resolution,[status(thm)],[c_6,c_173])).

tff(c_451,plain,(
    ! [A_105,B_106] :
      ( '#skF_1'(A_105,B_106) = '#skF_6'
      | ~ r1_tarski(A_105,'#skF_5')
      | r1_tarski(A_105,B_106) ) ),
    inference(resolution,[status(thm)],[c_434,c_52])).

tff(c_464,plain,(
    ! [A_17,B_106] :
      ( '#skF_1'(k1_tarski(A_17),B_106) = '#skF_6'
      | r1_tarski(k1_tarski(A_17),B_106)
      | ~ r2_hidden(A_17,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_342,c_451])).

tff(c_1851,plain,(
    ! [B_106] :
      ( '#skF_1'(k1_tarski('#skF_6'),B_106) = '#skF_6'
      | r1_tarski(k1_xboole_0,B_106)
      | ~ r2_hidden('#skF_6','#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_971,c_464])).

tff(c_3122,plain,(
    ! [B_3284] :
      ( '#skF_1'(k1_xboole_0,B_3284) = '#skF_6'
      | r1_tarski(k1_xboole_0,B_3284) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_971,c_1851])).

tff(c_3180,plain,(
    '#skF_1'(k1_xboole_0,'#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_3122,c_1945])).

tff(c_3206,plain,
    ( ~ r2_hidden('#skF_6','#skF_5')
    | r1_tarski(k1_xboole_0,'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_3180,c_4])).

tff(c_3236,plain,(
    r1_tarski(k1_xboole_0,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_3206])).

tff(c_3238,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1945,c_3236])).

tff(c_3240,plain,(
    k1_tarski('#skF_6') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_943])).

tff(c_738,plain,(
    ! [A_131] :
      ( '#skF_2'(k1_tarski(A_131)) = A_131
      | k1_tarski(A_131) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_703])).

tff(c_6424,plain,(
    ! [A_8630,A_8629] :
      ( k1_tarski(A_8630) = k1_tarski(A_8629)
      | ~ r2_hidden(A_8629,k1_tarski(A_8630))
      | ~ r2_hidden(A_8630,k1_tarski(A_8629)) ) ),
    inference(resolution,[status(thm)],[c_342,c_374])).

tff(c_6668,plain,(
    ! [A_8955] :
      ( k1_tarski(A_8955) = k1_tarski('#skF_6')
      | ~ r2_hidden(A_8955,k1_tarski('#skF_6'))
      | ~ r1_tarski('#skF_5',k1_tarski(A_8955)) ) ),
    inference(resolution,[status(thm)],[c_198,c_6424])).

tff(c_6701,plain,
    ( k1_tarski('#skF_2'(k1_tarski('#skF_6'))) = k1_tarski('#skF_6')
    | ~ r1_tarski('#skF_5',k1_tarski('#skF_2'(k1_tarski('#skF_6'))))
    | k1_tarski('#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_6668])).

tff(c_6714,plain,
    ( k1_tarski('#skF_2'(k1_tarski('#skF_6'))) = k1_tarski('#skF_6')
    | ~ r1_tarski('#skF_5',k1_tarski('#skF_2'(k1_tarski('#skF_6')))) ),
    inference(negUnitSimplification,[status(thm)],[c_3240,c_6701])).

tff(c_8388,plain,(
    ~ r1_tarski('#skF_5',k1_tarski('#skF_2'(k1_tarski('#skF_6')))) ),
    inference(splitLeft,[status(thm)],[c_6714])).

tff(c_8430,plain,
    ( ~ r1_tarski('#skF_5',k1_tarski('#skF_6'))
    | k1_tarski('#skF_6') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_738,c_8388])).

tff(c_8439,plain,(
    ~ r1_tarski('#skF_5',k1_tarski('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_3240,c_8430])).

tff(c_8453,plain,(
    '#skF_1'('#skF_5',k1_tarski('#skF_6')) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_168,c_8439])).

tff(c_8488,plain,
    ( ~ r2_hidden('#skF_6',k1_tarski('#skF_6'))
    | r1_tarski('#skF_5',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_8453,c_4])).

tff(c_8595,plain,(
    r1_tarski('#skF_5',k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_8488])).

tff(c_8597,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8439,c_8595])).

tff(c_8598,plain,(
    k1_tarski('#skF_2'(k1_tarski('#skF_6'))) = k1_tarski('#skF_6') ),
    inference(splitRight,[status(thm)],[c_6714])).

tff(c_8599,plain,(
    r1_tarski('#skF_5',k1_tarski('#skF_2'(k1_tarski('#skF_6')))) ),
    inference(splitRight,[status(thm)],[c_6714])).

tff(c_8775,plain,(
    r1_tarski('#skF_5',k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8598,c_8599])).

tff(c_372,plain,(
    ! [A_94,C_95] :
      ( k1_tarski(A_94) = C_95
      | ~ r1_tarski(C_95,k1_tarski(A_94))
      | ~ r2_hidden(A_94,C_95) ) ),
    inference(resolution,[status(thm)],[c_350,c_10])).

tff(c_8798,plain,
    ( k1_tarski('#skF_6') = '#skF_5'
    | ~ r2_hidden('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_8775,c_372])).

tff(c_8822,plain,(
    k1_tarski('#skF_6') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_8798])).

tff(c_8824,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_8822])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:52:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.30/2.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.30/2.51  
% 6.30/2.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.30/2.51  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 6.30/2.51  
% 6.30/2.51  %Foreground sorts:
% 6.30/2.51  
% 6.30/2.51  
% 6.30/2.51  %Background operators:
% 6.30/2.51  
% 6.30/2.51  
% 6.30/2.51  %Foreground operators:
% 6.30/2.51  tff('#skF_2', type, '#skF_2': $i > $i).
% 6.30/2.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.30/2.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.30/2.51  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.30/2.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.30/2.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.30/2.51  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.30/2.51  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.30/2.51  tff('#skF_5', type, '#skF_5': $i).
% 6.30/2.51  tff('#skF_6', type, '#skF_6': $i).
% 6.30/2.51  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.30/2.51  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 6.30/2.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.30/2.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.30/2.51  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 6.30/2.51  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.30/2.51  
% 6.30/2.52  tff(f_88, negated_conjecture, ~(![A, B]: ~((~(A = k1_tarski(B)) & ~(A = k1_xboole_0)) & (![C]: ~(r2_hidden(C, A) & ~(C = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_zfmisc_1)).
% 6.30/2.52  tff(f_40, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 6.30/2.52  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 6.30/2.52  tff(f_63, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 6.30/2.52  tff(f_73, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 6.30/2.52  tff(f_65, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 6.30/2.52  tff(f_61, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 6.30/2.52  tff(f_46, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.30/2.52  tff(c_56, plain, (k1_tarski('#skF_6')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_88])).
% 6.30/2.52  tff(c_54, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_88])).
% 6.30/2.52  tff(c_70, plain, (![A_34]: (r2_hidden('#skF_2'(A_34), A_34) | k1_xboole_0=A_34)), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.30/2.52  tff(c_52, plain, (![C_27]: (C_27='#skF_6' | ~r2_hidden(C_27, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 6.30/2.52  tff(c_74, plain, ('#skF_2'('#skF_5')='#skF_6' | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_70, c_52])).
% 6.30/2.52  tff(c_77, plain, ('#skF_2'('#skF_5')='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_54, c_74])).
% 6.30/2.52  tff(c_8, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.30/2.52  tff(c_81, plain, (r2_hidden('#skF_6', '#skF_5') | k1_xboole_0='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_77, c_8])).
% 6.30/2.52  tff(c_84, plain, (r2_hidden('#skF_6', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_54, c_81])).
% 6.30/2.52  tff(c_173, plain, (![C_63, B_64, A_65]: (r2_hidden(C_63, B_64) | ~r2_hidden(C_63, A_65) | ~r1_tarski(A_65, B_64))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.30/2.52  tff(c_198, plain, (![B_64]: (r2_hidden('#skF_6', B_64) | ~r1_tarski('#skF_5', B_64))), inference(resolution, [status(thm)], [c_84, c_173])).
% 6.30/2.52  tff(c_40, plain, (![A_17]: (k2_tarski(A_17, A_17)=k1_tarski(A_17))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.30/2.52  tff(c_319, plain, (![A_91, B_92, C_93]: (r1_tarski(k2_tarski(A_91, B_92), C_93) | ~r2_hidden(B_92, C_93) | ~r2_hidden(A_91, C_93))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.30/2.52  tff(c_342, plain, (![A_17, C_93]: (r1_tarski(k1_tarski(A_17), C_93) | ~r2_hidden(A_17, C_93) | ~r2_hidden(A_17, C_93))), inference(superposition, [status(thm), theory('equality')], [c_40, c_319])).
% 6.30/2.52  tff(c_199, plain, (![A_6, B_64]: (r2_hidden('#skF_2'(A_6), B_64) | ~r1_tarski(A_6, B_64) | k1_xboole_0=A_6)), inference(resolution, [status(thm)], [c_8, c_173])).
% 6.30/2.52  tff(c_42, plain, (![A_18, B_19]: (k1_enumset1(A_18, A_18, B_19)=k2_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.30/2.52  tff(c_509, plain, (![E_109, C_110, B_111, A_112]: (E_109=C_110 | E_109=B_111 | E_109=A_112 | ~r2_hidden(E_109, k1_enumset1(A_112, B_111, C_110)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.30/2.52  tff(c_578, plain, (![E_117, B_118, A_119]: (E_117=B_118 | E_117=A_119 | E_117=A_119 | ~r2_hidden(E_117, k2_tarski(A_119, B_118)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_509])).
% 6.30/2.52  tff(c_703, plain, (![E_130, A_131]: (E_130=A_131 | E_130=A_131 | E_130=A_131 | ~r2_hidden(E_130, k1_tarski(A_131)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_578])).
% 6.30/2.52  tff(c_762, plain, (![A_133, A_134]: (A_133='#skF_2'(A_134) | ~r1_tarski(A_134, k1_tarski(A_133)) | k1_xboole_0=A_134)), inference(resolution, [status(thm)], [c_199, c_703])).
% 6.30/2.52  tff(c_912, plain, (![A_149, A_150]: (A_149='#skF_2'(k1_tarski(A_150)) | k1_tarski(A_150)=k1_xboole_0 | ~r2_hidden(A_150, k1_tarski(A_149)))), inference(resolution, [status(thm)], [c_342, c_762])).
% 6.30/2.52  tff(c_943, plain, (![A_149]: (A_149='#skF_2'(k1_tarski('#skF_6')) | k1_tarski('#skF_6')=k1_xboole_0 | ~r1_tarski('#skF_5', k1_tarski(A_149)))), inference(resolution, [status(thm)], [c_198, c_912])).
% 6.30/2.52  tff(c_971, plain, (k1_tarski('#skF_6')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_943])).
% 6.30/2.52  tff(c_93, plain, (![A_41, B_42]: (k1_enumset1(A_41, A_41, B_42)=k2_tarski(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.30/2.52  tff(c_20, plain, (![E_16, A_10, C_12]: (r2_hidden(E_16, k1_enumset1(A_10, E_16, C_12)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.30/2.52  tff(c_111, plain, (![A_43, B_44]: (r2_hidden(A_43, k2_tarski(A_43, B_44)))), inference(superposition, [status(thm), theory('equality')], [c_93, c_20])).
% 6.30/2.52  tff(c_114, plain, (![A_17]: (r2_hidden(A_17, k1_tarski(A_17)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_111])).
% 6.30/2.52  tff(c_1871, plain, (r2_hidden('#skF_6', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_971, c_114])).
% 6.30/2.52  tff(c_157, plain, (![A_60, B_61]: (r2_hidden('#skF_1'(A_60, B_61), A_60) | r1_tarski(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.30/2.52  tff(c_168, plain, (![B_61]: ('#skF_1'('#skF_5', B_61)='#skF_6' | r1_tarski('#skF_5', B_61))), inference(resolution, [status(thm)], [c_157, c_52])).
% 6.30/2.52  tff(c_350, plain, (![A_94, C_95]: (r1_tarski(k1_tarski(A_94), C_95) | ~r2_hidden(A_94, C_95) | ~r2_hidden(A_94, C_95))), inference(superposition, [status(thm), theory('equality')], [c_40, c_319])).
% 6.30/2.52  tff(c_10, plain, (![B_9, A_8]: (B_9=A_8 | ~r1_tarski(B_9, A_8) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.30/2.52  tff(c_374, plain, (![A_96, C_97]: (k1_tarski(A_96)=C_97 | ~r1_tarski(C_97, k1_tarski(A_96)) | ~r2_hidden(A_96, C_97))), inference(resolution, [status(thm)], [c_350, c_10])).
% 6.30/2.52  tff(c_393, plain, (![A_96]: (k1_tarski(A_96)='#skF_5' | ~r2_hidden(A_96, '#skF_5') | '#skF_1'('#skF_5', k1_tarski(A_96))='#skF_6')), inference(resolution, [status(thm)], [c_168, c_374])).
% 6.30/2.52  tff(c_1856, plain, (k1_tarski('#skF_6')='#skF_5' | ~r2_hidden('#skF_6', '#skF_5') | '#skF_1'('#skF_5', k1_xboole_0)='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_971, c_393])).
% 6.30/2.52  tff(c_1886, plain, (k1_xboole_0='#skF_5' | '#skF_1'('#skF_5', k1_xboole_0)='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_971, c_1856])).
% 6.30/2.52  tff(c_1887, plain, ('#skF_1'('#skF_5', k1_xboole_0)='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_54, c_1886])).
% 6.30/2.52  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.30/2.52  tff(c_1909, plain, (~r2_hidden('#skF_6', k1_xboole_0) | r1_tarski('#skF_5', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1887, c_4])).
% 6.30/2.52  tff(c_1930, plain, (r1_tarski('#skF_5', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1871, c_1909])).
% 6.30/2.52  tff(c_1937, plain, (k1_xboole_0='#skF_5' | ~r1_tarski(k1_xboole_0, '#skF_5')), inference(resolution, [status(thm)], [c_1930, c_10])).
% 6.30/2.52  tff(c_1945, plain, (~r1_tarski(k1_xboole_0, '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_54, c_1937])).
% 6.30/2.52  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.30/2.52  tff(c_434, plain, (![A_102, B_103, B_104]: (r2_hidden('#skF_1'(A_102, B_103), B_104) | ~r1_tarski(A_102, B_104) | r1_tarski(A_102, B_103))), inference(resolution, [status(thm)], [c_6, c_173])).
% 6.30/2.52  tff(c_451, plain, (![A_105, B_106]: ('#skF_1'(A_105, B_106)='#skF_6' | ~r1_tarski(A_105, '#skF_5') | r1_tarski(A_105, B_106))), inference(resolution, [status(thm)], [c_434, c_52])).
% 6.30/2.52  tff(c_464, plain, (![A_17, B_106]: ('#skF_1'(k1_tarski(A_17), B_106)='#skF_6' | r1_tarski(k1_tarski(A_17), B_106) | ~r2_hidden(A_17, '#skF_5'))), inference(resolution, [status(thm)], [c_342, c_451])).
% 6.30/2.52  tff(c_1851, plain, (![B_106]: ('#skF_1'(k1_tarski('#skF_6'), B_106)='#skF_6' | r1_tarski(k1_xboole_0, B_106) | ~r2_hidden('#skF_6', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_971, c_464])).
% 6.30/2.52  tff(c_3122, plain, (![B_3284]: ('#skF_1'(k1_xboole_0, B_3284)='#skF_6' | r1_tarski(k1_xboole_0, B_3284))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_971, c_1851])).
% 6.30/2.52  tff(c_3180, plain, ('#skF_1'(k1_xboole_0, '#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_3122, c_1945])).
% 6.30/2.52  tff(c_3206, plain, (~r2_hidden('#skF_6', '#skF_5') | r1_tarski(k1_xboole_0, '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_3180, c_4])).
% 6.30/2.52  tff(c_3236, plain, (r1_tarski(k1_xboole_0, '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_3206])).
% 6.30/2.52  tff(c_3238, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1945, c_3236])).
% 6.30/2.52  tff(c_3240, plain, (k1_tarski('#skF_6')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_943])).
% 6.30/2.52  tff(c_738, plain, (![A_131]: ('#skF_2'(k1_tarski(A_131))=A_131 | k1_tarski(A_131)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_703])).
% 6.30/2.52  tff(c_6424, plain, (![A_8630, A_8629]: (k1_tarski(A_8630)=k1_tarski(A_8629) | ~r2_hidden(A_8629, k1_tarski(A_8630)) | ~r2_hidden(A_8630, k1_tarski(A_8629)))), inference(resolution, [status(thm)], [c_342, c_374])).
% 6.30/2.52  tff(c_6668, plain, (![A_8955]: (k1_tarski(A_8955)=k1_tarski('#skF_6') | ~r2_hidden(A_8955, k1_tarski('#skF_6')) | ~r1_tarski('#skF_5', k1_tarski(A_8955)))), inference(resolution, [status(thm)], [c_198, c_6424])).
% 6.30/2.52  tff(c_6701, plain, (k1_tarski('#skF_2'(k1_tarski('#skF_6')))=k1_tarski('#skF_6') | ~r1_tarski('#skF_5', k1_tarski('#skF_2'(k1_tarski('#skF_6')))) | k1_tarski('#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_8, c_6668])).
% 6.30/2.52  tff(c_6714, plain, (k1_tarski('#skF_2'(k1_tarski('#skF_6')))=k1_tarski('#skF_6') | ~r1_tarski('#skF_5', k1_tarski('#skF_2'(k1_tarski('#skF_6'))))), inference(negUnitSimplification, [status(thm)], [c_3240, c_6701])).
% 6.30/2.52  tff(c_8388, plain, (~r1_tarski('#skF_5', k1_tarski('#skF_2'(k1_tarski('#skF_6'))))), inference(splitLeft, [status(thm)], [c_6714])).
% 6.30/2.52  tff(c_8430, plain, (~r1_tarski('#skF_5', k1_tarski('#skF_6')) | k1_tarski('#skF_6')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_738, c_8388])).
% 6.30/2.52  tff(c_8439, plain, (~r1_tarski('#skF_5', k1_tarski('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_3240, c_8430])).
% 6.30/2.52  tff(c_8453, plain, ('#skF_1'('#skF_5', k1_tarski('#skF_6'))='#skF_6'), inference(resolution, [status(thm)], [c_168, c_8439])).
% 6.30/2.52  tff(c_8488, plain, (~r2_hidden('#skF_6', k1_tarski('#skF_6')) | r1_tarski('#skF_5', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_8453, c_4])).
% 6.30/2.52  tff(c_8595, plain, (r1_tarski('#skF_5', k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_114, c_8488])).
% 6.30/2.52  tff(c_8597, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8439, c_8595])).
% 6.30/2.52  tff(c_8598, plain, (k1_tarski('#skF_2'(k1_tarski('#skF_6')))=k1_tarski('#skF_6')), inference(splitRight, [status(thm)], [c_6714])).
% 6.30/2.52  tff(c_8599, plain, (r1_tarski('#skF_5', k1_tarski('#skF_2'(k1_tarski('#skF_6'))))), inference(splitRight, [status(thm)], [c_6714])).
% 6.30/2.52  tff(c_8775, plain, (r1_tarski('#skF_5', k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_8598, c_8599])).
% 6.30/2.52  tff(c_372, plain, (![A_94, C_95]: (k1_tarski(A_94)=C_95 | ~r1_tarski(C_95, k1_tarski(A_94)) | ~r2_hidden(A_94, C_95))), inference(resolution, [status(thm)], [c_350, c_10])).
% 6.30/2.52  tff(c_8798, plain, (k1_tarski('#skF_6')='#skF_5' | ~r2_hidden('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_8775, c_372])).
% 6.30/2.52  tff(c_8822, plain, (k1_tarski('#skF_6')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_8798])).
% 6.30/2.52  tff(c_8824, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_8822])).
% 6.30/2.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.30/2.52  
% 6.30/2.52  Inference rules
% 6.30/2.52  ----------------------
% 6.30/2.52  #Ref     : 0
% 6.30/2.52  #Sup     : 1650
% 6.30/2.52  #Fact    : 4
% 6.30/2.52  #Define  : 0
% 6.30/2.52  #Split   : 6
% 6.30/2.52  #Chain   : 0
% 6.30/2.52  #Close   : 0
% 6.30/2.52  
% 6.30/2.52  Ordering : KBO
% 6.30/2.52  
% 6.30/2.52  Simplification rules
% 6.30/2.52  ----------------------
% 6.30/2.52  #Subsume      : 556
% 6.30/2.52  #Demod        : 197
% 6.30/2.52  #Tautology    : 256
% 6.30/2.52  #SimpNegUnit  : 59
% 6.30/2.52  #BackRed      : 1
% 6.30/2.52  
% 6.30/2.52  #Partial instantiations: 5929
% 6.30/2.52  #Strategies tried      : 1
% 6.30/2.52  
% 6.30/2.52  Timing (in seconds)
% 6.30/2.53  ----------------------
% 6.30/2.53  Preprocessing        : 0.45
% 6.30/2.53  Parsing              : 0.22
% 6.30/2.53  CNF conversion       : 0.03
% 6.30/2.53  Main loop            : 1.26
% 6.30/2.53  Inferencing          : 0.47
% 6.30/2.53  Reduction            : 0.31
% 6.30/2.53  Demodulation         : 0.21
% 6.30/2.53  BG Simplification    : 0.05
% 6.30/2.53  Subsumption          : 0.37
% 6.30/2.53  Abstraction          : 0.05
% 6.30/2.53  MUC search           : 0.00
% 6.30/2.53  Cooper               : 0.00
% 6.30/2.53  Total                : 1.75
% 6.30/2.53  Index Insertion      : 0.00
% 6.30/2.53  Index Deletion       : 0.00
% 6.30/2.53  Index Matching       : 0.00
% 6.30/2.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
