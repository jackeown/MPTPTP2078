%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:31 EST 2020

% Result     : Theorem 3.49s
% Output     : CNFRefutation 3.53s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 117 expanded)
%              Number of leaves         :   35 (  56 expanded)
%              Depth                    :    9
%              Number of atoms          :   84 ( 146 expanded)
%              Number of equality atoms :   49 (  84 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_7 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_1 > #skF_5 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_51,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_73,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_91,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k3_xboole_0(B,k1_tarski(A)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l31_zfmisc_1)).

tff(f_102,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
      <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_49,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_96,axiom,(
    ! [A,B] :
      ( A != B
     => r1_xboole_0(k1_tarski(A),k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_16,plain,(
    ! [A_13,B_14] : r1_xboole_0(k4_xboole_0(A_13,B_14),B_14) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1303,plain,(
    ! [A_195,B_196] :
      ( k3_xboole_0(A_195,B_196) = k1_xboole_0
      | ~ r1_xboole_0(A_195,B_196) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1319,plain,(
    ! [A_13,B_14] : k3_xboole_0(k4_xboole_0(A_13,B_14),B_14) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_1303])).

tff(c_1464,plain,(
    ! [A_213,B_214,C_215] :
      ( ~ r1_xboole_0(A_213,B_214)
      | ~ r2_hidden(C_215,k3_xboole_0(A_213,B_214)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1473,plain,(
    ! [A_13,B_14,C_215] :
      ( ~ r1_xboole_0(k4_xboole_0(A_13,B_14),B_14)
      | ~ r2_hidden(C_215,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1319,c_1464])).

tff(c_1485,plain,(
    ! [C_215] : ~ r2_hidden(C_215,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1473])).

tff(c_44,plain,(
    ! [C_26] : r2_hidden(C_26,k1_tarski(C_26)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1568,plain,(
    ! [B_221,A_222] :
      ( k3_xboole_0(B_221,k1_tarski(A_222)) = k1_tarski(A_222)
      | ~ r2_hidden(A_222,B_221) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_713,plain,(
    ! [A_148,B_149] :
      ( k3_xboole_0(A_148,B_149) = k1_xboole_0
      | ~ r1_xboole_0(A_148,B_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_725,plain,(
    ! [A_13,B_14] : k3_xboole_0(k4_xboole_0(A_13,B_14),B_14) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_713])).

tff(c_938,plain,(
    ! [A_160,B_161,C_162] :
      ( ~ r1_xboole_0(A_160,B_161)
      | ~ r2_hidden(C_162,k3_xboole_0(A_160,B_161)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_953,plain,(
    ! [A_13,B_14,C_162] :
      ( ~ r1_xboole_0(k4_xboole_0(A_13,B_14),B_14)
      | ~ r2_hidden(C_162,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_725,c_938])).

tff(c_969,plain,(
    ! [C_162] : ~ r2_hidden(C_162,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_953])).

tff(c_1116,plain,(
    ! [B_171,A_172] :
      ( k3_xboole_0(B_171,k1_tarski(A_172)) = k1_tarski(A_172)
      | ~ r2_hidden(A_172,B_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_74,plain,
    ( '#skF_7' != '#skF_6'
    | '#skF_9' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_79,plain,(
    '#skF_7' != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_14,plain,(
    ! [A_12] : k5_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_213,plain,(
    ! [A_91,B_92] :
      ( r1_xboole_0(k1_tarski(A_91),k1_tarski(B_92))
      | B_92 = A_91 ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_332,plain,(
    ! [A_105,B_106] :
      ( k3_xboole_0(k1_tarski(A_105),k1_tarski(B_106)) = k1_xboole_0
      | B_106 = A_105 ) ),
    inference(resolution,[status(thm)],[c_213,c_4])).

tff(c_12,plain,(
    ! [A_10,B_11] : k5_xboole_0(A_10,k3_xboole_0(A_10,B_11)) = k4_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_344,plain,(
    ! [A_105,B_106] :
      ( k4_xboole_0(k1_tarski(A_105),k1_tarski(B_106)) = k5_xboole_0(k1_tarski(A_105),k1_xboole_0)
      | B_106 = A_105 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_332,c_12])).

tff(c_634,plain,(
    ! [A_131,B_132] :
      ( k4_xboole_0(k1_tarski(A_131),k1_tarski(B_132)) = k1_tarski(A_131)
      | B_132 = A_131 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_344])).

tff(c_72,plain,
    ( k4_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_7')) != k1_tarski('#skF_6')
    | '#skF_9' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_135,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_7')) != k1_tarski('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_649,plain,(
    '#skF_7' = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_634,c_135])).

tff(c_667,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_649])).

tff(c_668,plain,(
    '#skF_9' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_669,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_7')) = k1_tarski('#skF_6') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_76,plain,
    ( k4_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_7')) != k1_tarski('#skF_6')
    | k4_xboole_0(k1_tarski('#skF_8'),k1_tarski('#skF_9')) = k1_tarski('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_772,plain,(
    k4_xboole_0(k1_tarski('#skF_8'),k1_tarski('#skF_8')) = k1_tarski('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_668,c_669,c_76])).

tff(c_782,plain,(
    r1_xboole_0(k1_tarski('#skF_8'),k1_tarski('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_772,c_16])).

tff(c_789,plain,(
    k3_xboole_0(k1_tarski('#skF_8'),k1_tarski('#skF_8')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_782,c_4])).

tff(c_1144,plain,
    ( k1_tarski('#skF_8') = k1_xboole_0
    | ~ r2_hidden('#skF_8',k1_tarski('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1116,c_789])).

tff(c_1184,plain,(
    k1_tarski('#skF_8') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1144])).

tff(c_1212,plain,(
    r2_hidden('#skF_8',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1184,c_44])).

tff(c_1218,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_969,c_1212])).

tff(c_1219,plain,(
    '#skF_9' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_1220,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_78,plain,
    ( '#skF_7' != '#skF_6'
    | k4_xboole_0(k1_tarski('#skF_8'),k1_tarski('#skF_9')) = k1_tarski('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1293,plain,(
    k4_xboole_0(k1_tarski('#skF_8'),k1_tarski('#skF_8')) = k1_tarski('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1219,c_1220,c_78])).

tff(c_1320,plain,(
    ! [A_197,B_198] : k3_xboole_0(k4_xboole_0(A_197,B_198),B_198) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_1303])).

tff(c_1333,plain,(
    k3_xboole_0(k1_tarski('#skF_8'),k1_tarski('#skF_8')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1293,c_1320])).

tff(c_1587,plain,
    ( k1_tarski('#skF_8') = k1_xboole_0
    | ~ r2_hidden('#skF_8',k1_tarski('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1568,c_1333])).

tff(c_1621,plain,(
    k1_tarski('#skF_8') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1587])).

tff(c_1649,plain,(
    r2_hidden('#skF_8',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1621,c_44])).

tff(c_1655,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1485,c_1649])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:12:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.49/1.54  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.53/1.54  
% 3.53/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.53/1.55  %$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_7 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 3.53/1.55  
% 3.53/1.55  %Foreground sorts:
% 3.53/1.55  
% 3.53/1.55  
% 3.53/1.55  %Background operators:
% 3.53/1.55  
% 3.53/1.55  
% 3.53/1.55  %Foreground operators:
% 3.53/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.53/1.55  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.53/1.55  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.53/1.55  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.53/1.55  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.53/1.55  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.53/1.55  tff('#skF_7', type, '#skF_7': $i).
% 3.53/1.55  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.53/1.55  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.53/1.55  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.53/1.55  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.53/1.55  tff('#skF_6', type, '#skF_6': $i).
% 3.53/1.55  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.53/1.55  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.53/1.55  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.53/1.55  tff('#skF_9', type, '#skF_9': $i).
% 3.53/1.55  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.53/1.55  tff('#skF_8', type, '#skF_8': $i).
% 3.53/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.53/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.53/1.55  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.53/1.55  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 3.53/1.55  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.53/1.55  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.53/1.55  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.53/1.55  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.53/1.55  
% 3.53/1.56  tff(f_51, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 3.53/1.56  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.53/1.56  tff(f_45, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.53/1.56  tff(f_73, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 3.53/1.56  tff(f_91, axiom, (![A, B]: (r2_hidden(A, B) => (k3_xboole_0(B, k1_tarski(A)) = k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l31_zfmisc_1)).
% 3.53/1.56  tff(f_102, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 3.53/1.56  tff(f_49, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 3.53/1.56  tff(f_96, axiom, (![A, B]: (~(A = B) => r1_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 3.53/1.56  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.53/1.56  tff(c_16, plain, (![A_13, B_14]: (r1_xboole_0(k4_xboole_0(A_13, B_14), B_14))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.53/1.56  tff(c_1303, plain, (![A_195, B_196]: (k3_xboole_0(A_195, B_196)=k1_xboole_0 | ~r1_xboole_0(A_195, B_196))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.53/1.56  tff(c_1319, plain, (![A_13, B_14]: (k3_xboole_0(k4_xboole_0(A_13, B_14), B_14)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_1303])).
% 3.53/1.56  tff(c_1464, plain, (![A_213, B_214, C_215]: (~r1_xboole_0(A_213, B_214) | ~r2_hidden(C_215, k3_xboole_0(A_213, B_214)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.53/1.56  tff(c_1473, plain, (![A_13, B_14, C_215]: (~r1_xboole_0(k4_xboole_0(A_13, B_14), B_14) | ~r2_hidden(C_215, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1319, c_1464])).
% 3.53/1.56  tff(c_1485, plain, (![C_215]: (~r2_hidden(C_215, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_1473])).
% 3.53/1.56  tff(c_44, plain, (![C_26]: (r2_hidden(C_26, k1_tarski(C_26)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.53/1.56  tff(c_1568, plain, (![B_221, A_222]: (k3_xboole_0(B_221, k1_tarski(A_222))=k1_tarski(A_222) | ~r2_hidden(A_222, B_221))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.53/1.56  tff(c_713, plain, (![A_148, B_149]: (k3_xboole_0(A_148, B_149)=k1_xboole_0 | ~r1_xboole_0(A_148, B_149))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.53/1.56  tff(c_725, plain, (![A_13, B_14]: (k3_xboole_0(k4_xboole_0(A_13, B_14), B_14)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_713])).
% 3.53/1.56  tff(c_938, plain, (![A_160, B_161, C_162]: (~r1_xboole_0(A_160, B_161) | ~r2_hidden(C_162, k3_xboole_0(A_160, B_161)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.53/1.56  tff(c_953, plain, (![A_13, B_14, C_162]: (~r1_xboole_0(k4_xboole_0(A_13, B_14), B_14) | ~r2_hidden(C_162, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_725, c_938])).
% 3.53/1.56  tff(c_969, plain, (![C_162]: (~r2_hidden(C_162, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_953])).
% 3.53/1.56  tff(c_1116, plain, (![B_171, A_172]: (k3_xboole_0(B_171, k1_tarski(A_172))=k1_tarski(A_172) | ~r2_hidden(A_172, B_171))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.53/1.56  tff(c_74, plain, ('#skF_7'!='#skF_6' | '#skF_9'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.53/1.56  tff(c_79, plain, ('#skF_7'!='#skF_6'), inference(splitLeft, [status(thm)], [c_74])).
% 3.53/1.56  tff(c_14, plain, (![A_12]: (k5_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.53/1.56  tff(c_213, plain, (![A_91, B_92]: (r1_xboole_0(k1_tarski(A_91), k1_tarski(B_92)) | B_92=A_91)), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.53/1.56  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.53/1.56  tff(c_332, plain, (![A_105, B_106]: (k3_xboole_0(k1_tarski(A_105), k1_tarski(B_106))=k1_xboole_0 | B_106=A_105)), inference(resolution, [status(thm)], [c_213, c_4])).
% 3.53/1.56  tff(c_12, plain, (![A_10, B_11]: (k5_xboole_0(A_10, k3_xboole_0(A_10, B_11))=k4_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.53/1.56  tff(c_344, plain, (![A_105, B_106]: (k4_xboole_0(k1_tarski(A_105), k1_tarski(B_106))=k5_xboole_0(k1_tarski(A_105), k1_xboole_0) | B_106=A_105)), inference(superposition, [status(thm), theory('equality')], [c_332, c_12])).
% 3.53/1.56  tff(c_634, plain, (![A_131, B_132]: (k4_xboole_0(k1_tarski(A_131), k1_tarski(B_132))=k1_tarski(A_131) | B_132=A_131)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_344])).
% 3.53/1.56  tff(c_72, plain, (k4_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_7'))!=k1_tarski('#skF_6') | '#skF_9'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.53/1.56  tff(c_135, plain, (k4_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_7'))!=k1_tarski('#skF_6')), inference(splitLeft, [status(thm)], [c_72])).
% 3.53/1.56  tff(c_649, plain, ('#skF_7'='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_634, c_135])).
% 3.53/1.56  tff(c_667, plain, $false, inference(negUnitSimplification, [status(thm)], [c_79, c_649])).
% 3.53/1.56  tff(c_668, plain, ('#skF_9'='#skF_8'), inference(splitRight, [status(thm)], [c_72])).
% 3.53/1.56  tff(c_669, plain, (k4_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_7'))=k1_tarski('#skF_6')), inference(splitRight, [status(thm)], [c_72])).
% 3.53/1.56  tff(c_76, plain, (k4_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_7'))!=k1_tarski('#skF_6') | k4_xboole_0(k1_tarski('#skF_8'), k1_tarski('#skF_9'))=k1_tarski('#skF_8')), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.53/1.56  tff(c_772, plain, (k4_xboole_0(k1_tarski('#skF_8'), k1_tarski('#skF_8'))=k1_tarski('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_668, c_669, c_76])).
% 3.53/1.56  tff(c_782, plain, (r1_xboole_0(k1_tarski('#skF_8'), k1_tarski('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_772, c_16])).
% 3.53/1.56  tff(c_789, plain, (k3_xboole_0(k1_tarski('#skF_8'), k1_tarski('#skF_8'))=k1_xboole_0), inference(resolution, [status(thm)], [c_782, c_4])).
% 3.53/1.56  tff(c_1144, plain, (k1_tarski('#skF_8')=k1_xboole_0 | ~r2_hidden('#skF_8', k1_tarski('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_1116, c_789])).
% 3.53/1.56  tff(c_1184, plain, (k1_tarski('#skF_8')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_44, c_1144])).
% 3.53/1.56  tff(c_1212, plain, (r2_hidden('#skF_8', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1184, c_44])).
% 3.53/1.56  tff(c_1218, plain, $false, inference(negUnitSimplification, [status(thm)], [c_969, c_1212])).
% 3.53/1.56  tff(c_1219, plain, ('#skF_9'='#skF_8'), inference(splitRight, [status(thm)], [c_74])).
% 3.53/1.56  tff(c_1220, plain, ('#skF_7'='#skF_6'), inference(splitRight, [status(thm)], [c_74])).
% 3.53/1.56  tff(c_78, plain, ('#skF_7'!='#skF_6' | k4_xboole_0(k1_tarski('#skF_8'), k1_tarski('#skF_9'))=k1_tarski('#skF_8')), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.53/1.56  tff(c_1293, plain, (k4_xboole_0(k1_tarski('#skF_8'), k1_tarski('#skF_8'))=k1_tarski('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1219, c_1220, c_78])).
% 3.53/1.56  tff(c_1320, plain, (![A_197, B_198]: (k3_xboole_0(k4_xboole_0(A_197, B_198), B_198)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_1303])).
% 3.53/1.56  tff(c_1333, plain, (k3_xboole_0(k1_tarski('#skF_8'), k1_tarski('#skF_8'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1293, c_1320])).
% 3.53/1.56  tff(c_1587, plain, (k1_tarski('#skF_8')=k1_xboole_0 | ~r2_hidden('#skF_8', k1_tarski('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_1568, c_1333])).
% 3.53/1.56  tff(c_1621, plain, (k1_tarski('#skF_8')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_44, c_1587])).
% 3.53/1.56  tff(c_1649, plain, (r2_hidden('#skF_8', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1621, c_44])).
% 3.53/1.56  tff(c_1655, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1485, c_1649])).
% 3.53/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.53/1.56  
% 3.53/1.56  Inference rules
% 3.53/1.56  ----------------------
% 3.53/1.56  #Ref     : 0
% 3.53/1.56  #Sup     : 400
% 3.53/1.56  #Fact    : 0
% 3.53/1.56  #Define  : 0
% 3.53/1.56  #Split   : 2
% 3.53/1.56  #Chain   : 0
% 3.53/1.56  #Close   : 0
% 3.53/1.56  
% 3.53/1.56  Ordering : KBO
% 3.53/1.56  
% 3.53/1.56  Simplification rules
% 3.53/1.56  ----------------------
% 3.53/1.56  #Subsume      : 62
% 3.53/1.56  #Demod        : 162
% 3.53/1.56  #Tautology    : 215
% 3.53/1.56  #SimpNegUnit  : 10
% 3.53/1.56  #BackRed      : 6
% 3.53/1.56  
% 3.53/1.56  #Partial instantiations: 0
% 3.53/1.56  #Strategies tried      : 1
% 3.53/1.56  
% 3.53/1.56  Timing (in seconds)
% 3.53/1.56  ----------------------
% 3.53/1.56  Preprocessing        : 0.35
% 3.53/1.56  Parsing              : 0.18
% 3.53/1.56  CNF conversion       : 0.03
% 3.53/1.56  Main loop            : 0.43
% 3.53/1.56  Inferencing          : 0.16
% 3.53/1.56  Reduction            : 0.15
% 3.53/1.56  Demodulation         : 0.11
% 3.53/1.56  BG Simplification    : 0.03
% 3.53/1.56  Subsumption          : 0.07
% 3.53/1.56  Abstraction          : 0.02
% 3.53/1.56  MUC search           : 0.00
% 3.53/1.56  Cooper               : 0.00
% 3.53/1.56  Total                : 0.82
% 3.53/1.56  Index Insertion      : 0.00
% 3.53/1.56  Index Deletion       : 0.00
% 3.53/1.56  Index Matching       : 0.00
% 3.53/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
