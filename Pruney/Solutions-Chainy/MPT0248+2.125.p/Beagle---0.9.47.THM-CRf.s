%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:21 EST 2020

% Result     : Theorem 7.82s
% Output     : CNFRefutation 7.82s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 242 expanded)
%              Number of leaves         :   42 (  93 expanded)
%              Depth                    :   13
%              Number of atoms          :  123 ( 479 expanded)
%              Number of equality atoms :   83 ( 430 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_5 > #skF_2 > #skF_8 > #skF_3

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_116,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_54,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_52,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_48,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_50,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_44,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_60,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_56,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_58,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_42,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_71,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(c_86,plain,
    ( k1_tarski('#skF_6') != '#skF_8'
    | k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_134,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_84,plain,
    ( k1_xboole_0 != '#skF_8'
    | k1_tarski('#skF_6') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_129,plain,(
    k1_tarski('#skF_6') != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_90,plain,(
    k2_xboole_0('#skF_7','#skF_8') = k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_130,plain,(
    ! [A_68,B_69] : r1_tarski(A_68,k2_xboole_0(A_68,B_69)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_133,plain,(
    r1_tarski('#skF_7',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_130])).

tff(c_722,plain,(
    ! [B_141,A_142] :
      ( k1_tarski(B_141) = A_142
      | k1_xboole_0 = A_142
      | ~ r1_tarski(A_142,k1_tarski(B_141)) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_728,plain,
    ( k1_tarski('#skF_6') = '#skF_7'
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_133,c_722])).

tff(c_737,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_134,c_129,c_728])).

tff(c_738,plain,(
    k1_tarski('#skF_6') != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_739,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_28,plain,(
    ! [A_14] : k5_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_742,plain,(
    ! [A_14] : k5_xboole_0(A_14,'#skF_7') = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_739,c_28])).

tff(c_74,plain,(
    ! [B_58] : r1_tarski(k1_xboole_0,k1_tarski(B_58)) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_743,plain,(
    ! [B_58] : r1_tarski('#skF_7',k1_tarski(B_58)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_739,c_74])).

tff(c_851,plain,(
    ! [A_161,B_162] :
      ( k2_xboole_0(A_161,B_162) = B_162
      | ~ r1_tarski(A_161,B_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_866,plain,(
    ! [B_58] : k2_xboole_0('#skF_7',k1_tarski(B_58)) = k1_tarski(B_58) ),
    inference(resolution,[status(thm)],[c_743,c_851])).

tff(c_26,plain,(
    ! [A_13] : k3_xboole_0(A_13,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_741,plain,(
    ! [A_13] : k3_xboole_0(A_13,'#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_739,c_739,c_26])).

tff(c_922,plain,(
    ! [A_168,B_169] : k5_xboole_0(A_168,k3_xboole_0(A_168,B_169)) = k4_xboole_0(A_168,B_169) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_931,plain,(
    ! [A_13] : k5_xboole_0(A_13,'#skF_7') = k4_xboole_0(A_13,'#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_741,c_922])).

tff(c_935,plain,(
    ! [A_170] : k4_xboole_0(A_170,'#skF_7') = A_170 ),
    inference(demodulation,[status(thm),theory(equality)],[c_742,c_931])).

tff(c_36,plain,(
    ! [A_21,B_22] : k5_xboole_0(A_21,k4_xboole_0(B_22,A_21)) = k2_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_941,plain,(
    ! [A_170] : k5_xboole_0('#skF_7',A_170) = k2_xboole_0('#skF_7',A_170) ),
    inference(superposition,[status(thm),theory(equality)],[c_935,c_36])).

tff(c_1644,plain,(
    ! [A_232,B_233,C_234] : k5_xboole_0(k5_xboole_0(A_232,B_233),C_234) = k5_xboole_0(A_232,k5_xboole_0(B_233,C_234)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_34,plain,(
    ! [A_20] : k5_xboole_0(A_20,A_20) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_740,plain,(
    ! [A_20] : k5_xboole_0(A_20,A_20) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_739,c_34])).

tff(c_1713,plain,(
    ! [A_235,B_236] : k5_xboole_0(A_235,k5_xboole_0(B_236,k5_xboole_0(A_235,B_236))) = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_1644,c_740])).

tff(c_1765,plain,(
    ! [A_14] : k5_xboole_0(A_14,k5_xboole_0('#skF_7',A_14)) = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_742,c_1713])).

tff(c_1779,plain,(
    ! [A_14] : k5_xboole_0(A_14,k2_xboole_0('#skF_7',A_14)) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_941,c_1765])).

tff(c_1781,plain,(
    ! [A_237] : k5_xboole_0(A_237,k2_xboole_0('#skF_7',A_237)) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_941,c_1765])).

tff(c_1838,plain,(
    k5_xboole_0('#skF_8',k1_tarski('#skF_6')) = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_1781])).

tff(c_32,plain,(
    ! [A_17,B_18,C_19] : k5_xboole_0(k5_xboole_0(A_17,B_18),C_19) = k5_xboole_0(A_17,k5_xboole_0(B_18,C_19)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1858,plain,(
    ! [C_19] : k5_xboole_0('#skF_8',k5_xboole_0(k1_tarski('#skF_6'),C_19)) = k5_xboole_0('#skF_7',C_19) ),
    inference(superposition,[status(thm),theory(equality)],[c_1838,c_32])).

tff(c_1864,plain,(
    ! [C_238] : k5_xboole_0('#skF_8',k5_xboole_0(k1_tarski('#skF_6'),C_238)) = k2_xboole_0('#skF_7',C_238) ),
    inference(demodulation,[status(thm),theory(equality)],[c_941,c_1858])).

tff(c_1888,plain,(
    k2_xboole_0('#skF_7',k2_xboole_0('#skF_7',k1_tarski('#skF_6'))) = k5_xboole_0('#skF_8','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_1779,c_1864])).

tff(c_1919,plain,(
    k1_tarski('#skF_6') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_742,c_866,c_866,c_1888])).

tff(c_1921,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_738,c_1919])).

tff(c_1923,plain,(
    k1_tarski('#skF_6') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_88,plain,
    ( k1_tarski('#skF_6') != '#skF_8'
    | k1_tarski('#skF_6') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_1943,plain,(
    '#skF_7' != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1923,c_1923,c_88])).

tff(c_1922,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_20,plain,(
    ! [A_7] :
      ( r2_hidden('#skF_3'(A_7),A_7)
      | k1_xboole_0 = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1924,plain,(
    k2_xboole_0('#skF_7','#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1923,c_90])).

tff(c_2189,plain,(
    ! [D_271,B_272,A_273] :
      ( ~ r2_hidden(D_271,B_272)
      | r2_hidden(D_271,k2_xboole_0(A_273,B_272)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_2210,plain,(
    ! [D_271] :
      ( ~ r2_hidden(D_271,'#skF_8')
      | r2_hidden(D_271,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1924,c_2189])).

tff(c_56,plain,(
    ! [A_29] : k2_tarski(A_29,A_29) = k1_tarski(A_29) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2429,plain,(
    ! [D_300,B_301,A_302] :
      ( D_300 = B_301
      | D_300 = A_302
      | ~ r2_hidden(D_300,k2_tarski(A_302,B_301)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2461,plain,(
    ! [D_303,A_304] :
      ( D_303 = A_304
      | D_303 = A_304
      | ~ r2_hidden(D_303,k1_tarski(A_304)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_2429])).

tff(c_2510,plain,(
    ! [D_309] :
      ( D_309 = '#skF_6'
      | D_309 = '#skF_6'
      | ~ r2_hidden(D_309,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1923,c_2461])).

tff(c_2544,plain,(
    ! [D_310] :
      ( D_310 = '#skF_6'
      | ~ r2_hidden(D_310,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_2210,c_2510])).

tff(c_2552,plain,
    ( '#skF_3'('#skF_8') = '#skF_6'
    | k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_20,c_2544])).

tff(c_2557,plain,(
    '#skF_3'('#skF_8') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_1922,c_2552])).

tff(c_2561,plain,
    ( r2_hidden('#skF_6','#skF_8')
    | k1_xboole_0 = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_2557,c_20])).

tff(c_2564,plain,(
    r2_hidden('#skF_6','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_1922,c_2561])).

tff(c_3603,plain,(
    ! [A_354,B_355,C_356] :
      ( r1_tarski(k2_tarski(A_354,B_355),C_356)
      | ~ r2_hidden(B_355,C_356)
      | ~ r2_hidden(A_354,C_356) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_9921,plain,(
    ! [A_16224,C_16225] :
      ( r1_tarski(k1_tarski(A_16224),C_16225)
      | ~ r2_hidden(A_16224,C_16225)
      | ~ r2_hidden(A_16224,C_16225) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_3603])).

tff(c_24,plain,(
    ! [A_11,B_12] :
      ( k2_xboole_0(A_11,B_12) = B_12
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_9940,plain,(
    ! [A_16342,C_16343] :
      ( k2_xboole_0(k1_tarski(A_16342),C_16343) = C_16343
      | ~ r2_hidden(A_16342,C_16343) ) ),
    inference(resolution,[status(thm)],[c_9921,c_24])).

tff(c_10182,plain,(
    ! [C_16695] :
      ( k2_xboole_0('#skF_7',C_16695) = C_16695
      | ~ r2_hidden('#skF_6',C_16695) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1923,c_9940])).

tff(c_10244,plain,(
    k2_xboole_0('#skF_7','#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_2564,c_10182])).

tff(c_10269,plain,(
    '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10244,c_1924])).

tff(c_10271,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1943,c_10269])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 17:32:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.82/2.66  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.82/2.67  
% 7.82/2.67  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.82/2.67  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_5 > #skF_2 > #skF_8 > #skF_3
% 7.82/2.67  
% 7.82/2.67  %Foreground sorts:
% 7.82/2.67  
% 7.82/2.67  
% 7.82/2.67  %Background operators:
% 7.82/2.67  
% 7.82/2.67  
% 7.82/2.67  %Foreground operators:
% 7.82/2.67  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 7.82/2.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.82/2.67  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.82/2.67  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.82/2.67  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.82/2.67  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.82/2.67  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 7.82/2.67  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 7.82/2.67  tff('#skF_7', type, '#skF_7': $i).
% 7.82/2.67  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.82/2.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.82/2.67  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.82/2.67  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.82/2.67  tff('#skF_6', type, '#skF_6': $i).
% 7.82/2.67  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 7.82/2.67  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.82/2.67  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.82/2.67  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.82/2.67  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 7.82/2.67  tff('#skF_8', type, '#skF_8': $i).
% 7.82/2.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.82/2.67  tff(k3_tarski, type, k3_tarski: $i > $i).
% 7.82/2.67  tff('#skF_3', type, '#skF_3': $i > $i).
% 7.82/2.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.82/2.67  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.82/2.67  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.82/2.67  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 7.82/2.67  
% 7.82/2.70  tff(f_116, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 7.82/2.70  tff(f_54, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 7.82/2.70  tff(f_89, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 7.82/2.70  tff(f_52, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 7.82/2.70  tff(f_48, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 7.82/2.70  tff(f_50, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 7.82/2.70  tff(f_44, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 7.82/2.70  tff(f_60, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 7.82/2.70  tff(f_56, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 7.82/2.70  tff(f_58, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 7.82/2.70  tff(f_42, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 7.82/2.70  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 7.82/2.70  tff(f_71, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 7.82/2.70  tff(f_69, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 7.82/2.70  tff(f_97, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 7.82/2.70  tff(c_86, plain, (k1_tarski('#skF_6')!='#skF_8' | k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_116])).
% 7.82/2.70  tff(c_134, plain, (k1_xboole_0!='#skF_7'), inference(splitLeft, [status(thm)], [c_86])).
% 7.82/2.70  tff(c_84, plain, (k1_xboole_0!='#skF_8' | k1_tarski('#skF_6')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_116])).
% 7.82/2.70  tff(c_129, plain, (k1_tarski('#skF_6')!='#skF_7'), inference(splitLeft, [status(thm)], [c_84])).
% 7.82/2.70  tff(c_90, plain, (k2_xboole_0('#skF_7', '#skF_8')=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_116])).
% 7.82/2.70  tff(c_130, plain, (![A_68, B_69]: (r1_tarski(A_68, k2_xboole_0(A_68, B_69)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.82/2.70  tff(c_133, plain, (r1_tarski('#skF_7', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_90, c_130])).
% 7.82/2.70  tff(c_722, plain, (![B_141, A_142]: (k1_tarski(B_141)=A_142 | k1_xboole_0=A_142 | ~r1_tarski(A_142, k1_tarski(B_141)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 7.82/2.70  tff(c_728, plain, (k1_tarski('#skF_6')='#skF_7' | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_133, c_722])).
% 7.82/2.70  tff(c_737, plain, $false, inference(negUnitSimplification, [status(thm)], [c_134, c_129, c_728])).
% 7.82/2.70  tff(c_738, plain, (k1_tarski('#skF_6')!='#skF_8'), inference(splitRight, [status(thm)], [c_86])).
% 7.82/2.70  tff(c_739, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_86])).
% 7.82/2.70  tff(c_28, plain, (![A_14]: (k5_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.82/2.70  tff(c_742, plain, (![A_14]: (k5_xboole_0(A_14, '#skF_7')=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_739, c_28])).
% 7.82/2.70  tff(c_74, plain, (![B_58]: (r1_tarski(k1_xboole_0, k1_tarski(B_58)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 7.82/2.70  tff(c_743, plain, (![B_58]: (r1_tarski('#skF_7', k1_tarski(B_58)))), inference(demodulation, [status(thm), theory('equality')], [c_739, c_74])).
% 7.82/2.70  tff(c_851, plain, (![A_161, B_162]: (k2_xboole_0(A_161, B_162)=B_162 | ~r1_tarski(A_161, B_162))), inference(cnfTransformation, [status(thm)], [f_48])).
% 7.82/2.70  tff(c_866, plain, (![B_58]: (k2_xboole_0('#skF_7', k1_tarski(B_58))=k1_tarski(B_58))), inference(resolution, [status(thm)], [c_743, c_851])).
% 7.82/2.70  tff(c_26, plain, (![A_13]: (k3_xboole_0(A_13, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.82/2.70  tff(c_741, plain, (![A_13]: (k3_xboole_0(A_13, '#skF_7')='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_739, c_739, c_26])).
% 7.82/2.70  tff(c_922, plain, (![A_168, B_169]: (k5_xboole_0(A_168, k3_xboole_0(A_168, B_169))=k4_xboole_0(A_168, B_169))), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.82/2.70  tff(c_931, plain, (![A_13]: (k5_xboole_0(A_13, '#skF_7')=k4_xboole_0(A_13, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_741, c_922])).
% 7.82/2.70  tff(c_935, plain, (![A_170]: (k4_xboole_0(A_170, '#skF_7')=A_170)), inference(demodulation, [status(thm), theory('equality')], [c_742, c_931])).
% 7.82/2.70  tff(c_36, plain, (![A_21, B_22]: (k5_xboole_0(A_21, k4_xboole_0(B_22, A_21))=k2_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.82/2.70  tff(c_941, plain, (![A_170]: (k5_xboole_0('#skF_7', A_170)=k2_xboole_0('#skF_7', A_170))), inference(superposition, [status(thm), theory('equality')], [c_935, c_36])).
% 7.82/2.70  tff(c_1644, plain, (![A_232, B_233, C_234]: (k5_xboole_0(k5_xboole_0(A_232, B_233), C_234)=k5_xboole_0(A_232, k5_xboole_0(B_233, C_234)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 7.82/2.70  tff(c_34, plain, (![A_20]: (k5_xboole_0(A_20, A_20)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.82/2.70  tff(c_740, plain, (![A_20]: (k5_xboole_0(A_20, A_20)='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_739, c_34])).
% 7.82/2.70  tff(c_1713, plain, (![A_235, B_236]: (k5_xboole_0(A_235, k5_xboole_0(B_236, k5_xboole_0(A_235, B_236)))='#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_1644, c_740])).
% 7.82/2.70  tff(c_1765, plain, (![A_14]: (k5_xboole_0(A_14, k5_xboole_0('#skF_7', A_14))='#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_742, c_1713])).
% 7.82/2.70  tff(c_1779, plain, (![A_14]: (k5_xboole_0(A_14, k2_xboole_0('#skF_7', A_14))='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_941, c_1765])).
% 7.82/2.70  tff(c_1781, plain, (![A_237]: (k5_xboole_0(A_237, k2_xboole_0('#skF_7', A_237))='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_941, c_1765])).
% 7.82/2.70  tff(c_1838, plain, (k5_xboole_0('#skF_8', k1_tarski('#skF_6'))='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_90, c_1781])).
% 7.82/2.70  tff(c_32, plain, (![A_17, B_18, C_19]: (k5_xboole_0(k5_xboole_0(A_17, B_18), C_19)=k5_xboole_0(A_17, k5_xboole_0(B_18, C_19)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 7.82/2.70  tff(c_1858, plain, (![C_19]: (k5_xboole_0('#skF_8', k5_xboole_0(k1_tarski('#skF_6'), C_19))=k5_xboole_0('#skF_7', C_19))), inference(superposition, [status(thm), theory('equality')], [c_1838, c_32])).
% 7.82/2.70  tff(c_1864, plain, (![C_238]: (k5_xboole_0('#skF_8', k5_xboole_0(k1_tarski('#skF_6'), C_238))=k2_xboole_0('#skF_7', C_238))), inference(demodulation, [status(thm), theory('equality')], [c_941, c_1858])).
% 7.82/2.70  tff(c_1888, plain, (k2_xboole_0('#skF_7', k2_xboole_0('#skF_7', k1_tarski('#skF_6')))=k5_xboole_0('#skF_8', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_1779, c_1864])).
% 7.82/2.70  tff(c_1919, plain, (k1_tarski('#skF_6')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_742, c_866, c_866, c_1888])).
% 7.82/2.70  tff(c_1921, plain, $false, inference(negUnitSimplification, [status(thm)], [c_738, c_1919])).
% 7.82/2.70  tff(c_1923, plain, (k1_tarski('#skF_6')='#skF_7'), inference(splitRight, [status(thm)], [c_84])).
% 7.82/2.70  tff(c_88, plain, (k1_tarski('#skF_6')!='#skF_8' | k1_tarski('#skF_6')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_116])).
% 7.82/2.70  tff(c_1943, plain, ('#skF_7'!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_1923, c_1923, c_88])).
% 7.82/2.70  tff(c_1922, plain, (k1_xboole_0!='#skF_8'), inference(splitRight, [status(thm)], [c_84])).
% 7.82/2.70  tff(c_20, plain, (![A_7]: (r2_hidden('#skF_3'(A_7), A_7) | k1_xboole_0=A_7)), inference(cnfTransformation, [status(thm)], [f_42])).
% 7.82/2.70  tff(c_1924, plain, (k2_xboole_0('#skF_7', '#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_1923, c_90])).
% 7.82/2.70  tff(c_2189, plain, (![D_271, B_272, A_273]: (~r2_hidden(D_271, B_272) | r2_hidden(D_271, k2_xboole_0(A_273, B_272)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.82/2.70  tff(c_2210, plain, (![D_271]: (~r2_hidden(D_271, '#skF_8') | r2_hidden(D_271, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_1924, c_2189])).
% 7.82/2.70  tff(c_56, plain, (![A_29]: (k2_tarski(A_29, A_29)=k1_tarski(A_29))), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.82/2.70  tff(c_2429, plain, (![D_300, B_301, A_302]: (D_300=B_301 | D_300=A_302 | ~r2_hidden(D_300, k2_tarski(A_302, B_301)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.82/2.70  tff(c_2461, plain, (![D_303, A_304]: (D_303=A_304 | D_303=A_304 | ~r2_hidden(D_303, k1_tarski(A_304)))), inference(superposition, [status(thm), theory('equality')], [c_56, c_2429])).
% 7.82/2.70  tff(c_2510, plain, (![D_309]: (D_309='#skF_6' | D_309='#skF_6' | ~r2_hidden(D_309, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_1923, c_2461])).
% 7.82/2.70  tff(c_2544, plain, (![D_310]: (D_310='#skF_6' | ~r2_hidden(D_310, '#skF_8'))), inference(resolution, [status(thm)], [c_2210, c_2510])).
% 7.82/2.70  tff(c_2552, plain, ('#skF_3'('#skF_8')='#skF_6' | k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_20, c_2544])).
% 7.82/2.70  tff(c_2557, plain, ('#skF_3'('#skF_8')='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_1922, c_2552])).
% 7.82/2.70  tff(c_2561, plain, (r2_hidden('#skF_6', '#skF_8') | k1_xboole_0='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_2557, c_20])).
% 7.82/2.70  tff(c_2564, plain, (r2_hidden('#skF_6', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_1922, c_2561])).
% 7.82/2.70  tff(c_3603, plain, (![A_354, B_355, C_356]: (r1_tarski(k2_tarski(A_354, B_355), C_356) | ~r2_hidden(B_355, C_356) | ~r2_hidden(A_354, C_356))), inference(cnfTransformation, [status(thm)], [f_97])).
% 7.82/2.70  tff(c_9921, plain, (![A_16224, C_16225]: (r1_tarski(k1_tarski(A_16224), C_16225) | ~r2_hidden(A_16224, C_16225) | ~r2_hidden(A_16224, C_16225))), inference(superposition, [status(thm), theory('equality')], [c_56, c_3603])).
% 7.82/2.70  tff(c_24, plain, (![A_11, B_12]: (k2_xboole_0(A_11, B_12)=B_12 | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_48])).
% 7.82/2.70  tff(c_9940, plain, (![A_16342, C_16343]: (k2_xboole_0(k1_tarski(A_16342), C_16343)=C_16343 | ~r2_hidden(A_16342, C_16343))), inference(resolution, [status(thm)], [c_9921, c_24])).
% 7.82/2.70  tff(c_10182, plain, (![C_16695]: (k2_xboole_0('#skF_7', C_16695)=C_16695 | ~r2_hidden('#skF_6', C_16695))), inference(superposition, [status(thm), theory('equality')], [c_1923, c_9940])).
% 7.82/2.70  tff(c_10244, plain, (k2_xboole_0('#skF_7', '#skF_8')='#skF_8'), inference(resolution, [status(thm)], [c_2564, c_10182])).
% 7.82/2.70  tff(c_10269, plain, ('#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_10244, c_1924])).
% 7.82/2.70  tff(c_10271, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1943, c_10269])).
% 7.82/2.70  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.82/2.70  
% 7.82/2.70  Inference rules
% 7.82/2.70  ----------------------
% 7.82/2.70  #Ref     : 0
% 7.82/2.70  #Sup     : 1926
% 7.82/2.70  #Fact    : 14
% 7.82/2.70  #Define  : 0
% 7.82/2.70  #Split   : 9
% 7.82/2.70  #Chain   : 0
% 7.82/2.70  #Close   : 0
% 7.82/2.70  
% 7.82/2.70  Ordering : KBO
% 7.82/2.70  
% 7.82/2.70  Simplification rules
% 7.82/2.70  ----------------------
% 7.82/2.70  #Subsume      : 117
% 7.82/2.70  #Demod        : 1489
% 7.82/2.70  #Tautology    : 1182
% 7.82/2.70  #SimpNegUnit  : 28
% 7.82/2.70  #BackRed      : 54
% 7.82/2.70  
% 7.82/2.70  #Partial instantiations: 6204
% 7.82/2.70  #Strategies tried      : 1
% 7.82/2.70  
% 7.82/2.70  Timing (in seconds)
% 7.82/2.70  ----------------------
% 7.82/2.70  Preprocessing        : 0.35
% 7.82/2.70  Parsing              : 0.18
% 7.82/2.70  CNF conversion       : 0.03
% 7.82/2.70  Main loop            : 1.58
% 7.82/2.70  Inferencing          : 0.69
% 7.82/2.70  Reduction            : 0.51
% 7.82/2.70  Demodulation         : 0.40
% 7.82/2.70  BG Simplification    : 0.06
% 7.82/2.70  Subsumption          : 0.22
% 7.82/2.71  Abstraction          : 0.06
% 7.82/2.71  MUC search           : 0.00
% 7.82/2.71  Cooper               : 0.00
% 7.82/2.71  Total                : 1.98
% 7.82/2.71  Index Insertion      : 0.00
% 7.82/2.71  Index Deletion       : 0.00
% 7.82/2.71  Index Matching       : 0.00
% 7.82/2.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
