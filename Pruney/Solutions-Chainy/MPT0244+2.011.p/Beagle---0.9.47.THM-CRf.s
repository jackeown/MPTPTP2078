%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:57 EST 2020

% Result     : Theorem 3.38s
% Output     : CNFRefutation 3.38s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 282 expanded)
%              Number of leaves         :   25 (  95 expanded)
%              Depth                    :   10
%              Number of atoms          :  153 ( 503 expanded)
%              Number of equality atoms :   78 ( 282 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_53,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_73,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_85,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,k1_tarski(B))
      <=> ( A = k1_xboole_0
          | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_59,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(c_14,plain,(
    ! [B_9] : r1_tarski(B_9,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_34,plain,(
    ! [A_21,B_22] :
      ( r1_tarski(k1_tarski(A_21),B_22)
      | ~ r2_hidden(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_38,plain,
    ( ~ r1_tarski('#skF_2',k1_tarski('#skF_3'))
    | k1_tarski('#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_80,plain,(
    k1_tarski('#skF_5') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_116,plain,(
    ! [A_45,B_46] :
      ( k4_xboole_0(A_45,B_46) = k1_xboole_0
      | ~ r1_tarski(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_128,plain,(
    ! [B_9] : k4_xboole_0(B_9,B_9) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_116])).

tff(c_48,plain,
    ( k1_tarski('#skF_3') = '#skF_2'
    | k1_xboole_0 = '#skF_2'
    | r1_tarski('#skF_4',k1_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_213,plain,(
    r1_tarski('#skF_4',k1_tarski('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( B_9 = A_8
      | ~ r1_tarski(B_9,A_8)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_215,plain,
    ( k1_tarski('#skF_5') = '#skF_4'
    | ~ r1_tarski(k1_tarski('#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_213,c_10])).

tff(c_221,plain,(
    ~ r1_tarski(k1_tarski('#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_215])).

tff(c_230,plain,(
    ~ r2_hidden('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_221])).

tff(c_42,plain,
    ( ~ r1_tarski('#skF_2',k1_tarski('#skF_3'))
    | k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_70,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_81,plain,(
    ! [A_34,B_35] :
      ( r1_xboole_0(k1_tarski(A_34),B_35)
      | r2_hidden(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_151,plain,(
    ! [B_48,A_49] :
      ( r1_xboole_0(B_48,k1_tarski(A_49))
      | r2_hidden(A_49,B_48) ) ),
    inference(resolution,[status(thm)],[c_81,c_2])).

tff(c_22,plain,(
    ! [A_13,B_14] :
      ( k4_xboole_0(A_13,B_14) = A_13
      | ~ r1_xboole_0(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_292,plain,(
    ! [B_70,A_71] :
      ( k4_xboole_0(B_70,k1_tarski(A_71)) = B_70
      | r2_hidden(A_71,B_70) ) ),
    inference(resolution,[status(thm)],[c_151,c_22])).

tff(c_18,plain,(
    ! [A_10,B_11] :
      ( k4_xboole_0(A_10,B_11) = k1_xboole_0
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_222,plain,(
    k4_xboole_0('#skF_4',k1_tarski('#skF_5')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_213,c_18])).

tff(c_302,plain,
    ( k1_xboole_0 = '#skF_4'
    | r2_hidden('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_292,c_222])).

tff(c_330,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_230,c_70,c_302])).

tff(c_331,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_tarski('#skF_3') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_337,plain,(
    k1_tarski('#skF_3') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_331])).

tff(c_16,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,B_11)
      | k4_xboole_0(A_10,B_11) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_46,plain,
    ( ~ r1_tarski('#skF_2',k1_tarski('#skF_3'))
    | r1_tarski('#skF_4',k1_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_146,plain,(
    ~ r1_tarski('#skF_2',k1_tarski('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_150,plain,(
    k4_xboole_0('#skF_2',k1_tarski('#skF_3')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_146])).

tff(c_338,plain,(
    k4_xboole_0('#skF_2','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_337,c_150])).

tff(c_342,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_338])).

tff(c_343,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_331])).

tff(c_20,plain,(
    ! [A_12] : k4_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_351,plain,(
    ! [A_12] : k4_xboole_0(A_12,'#skF_2') = A_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_343,c_20])).

tff(c_72,plain,(
    ! [A_32,B_33] :
      ( r1_xboole_0(A_32,B_33)
      | k4_xboole_0(A_32,B_33) != A_32 ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_159,plain,(
    ! [B_50,A_51] :
      ( r1_xboole_0(B_50,A_51)
      | k4_xboole_0(A_51,B_50) != A_51 ) ),
    inference(resolution,[status(thm)],[c_72,c_2])).

tff(c_488,plain,(
    ! [B_87,A_88] :
      ( k4_xboole_0(B_87,A_88) = B_87
      | k4_xboole_0(A_88,B_87) != A_88 ) ),
    inference(resolution,[status(thm)],[c_159,c_22])).

tff(c_496,plain,(
    ! [A_12] : k4_xboole_0('#skF_2',A_12) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_351,c_488])).

tff(c_346,plain,(
    k4_xboole_0('#skF_2',k1_tarski('#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_343,c_150])).

tff(c_499,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_496,c_346])).

tff(c_500,plain,(
    r1_tarski('#skF_4',k1_tarski('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_534,plain,(
    ! [B_93,A_94] :
      ( B_93 = A_94
      | ~ r1_tarski(B_93,A_94)
      | ~ r1_tarski(A_94,B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_538,plain,
    ( k1_tarski('#skF_5') = '#skF_4'
    | ~ r1_tarski(k1_tarski('#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_500,c_534])).

tff(c_548,plain,(
    ~ r1_tarski(k1_tarski('#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_538])).

tff(c_562,plain,(
    ~ r2_hidden('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_548])).

tff(c_518,plain,(
    ! [B_89,A_90] :
      ( r1_xboole_0(B_89,k1_tarski(A_90))
      | r2_hidden(A_90,B_89) ) ),
    inference(resolution,[status(thm)],[c_81,c_2])).

tff(c_1458,plain,(
    ! [B_160,A_161] :
      ( k4_xboole_0(B_160,k1_tarski(A_161)) = B_160
      | r2_hidden(A_161,B_160) ) ),
    inference(resolution,[status(thm)],[c_518,c_22])).

tff(c_505,plain,(
    k4_xboole_0('#skF_4',k1_tarski('#skF_5')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_500,c_18])).

tff(c_1476,plain,
    ( k1_xboole_0 = '#skF_4'
    | r2_hidden('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1458,c_505])).

tff(c_1505,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_562,c_70,c_1476])).

tff(c_1507,plain,(
    k1_tarski('#skF_5') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_40,plain,
    ( k1_tarski('#skF_3') = '#skF_2'
    | k1_xboole_0 = '#skF_2'
    | k1_tarski('#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1550,plain,
    ( k1_tarski('#skF_3') = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1507,c_40])).

tff(c_1551,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_1550])).

tff(c_1553,plain,(
    ! [A_12] : k4_xboole_0(A_12,'#skF_2') = A_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1551,c_20])).

tff(c_1512,plain,(
    ! [A_162,B_163] :
      ( r1_xboole_0(k1_tarski(A_162),B_163)
      | r2_hidden(A_162,B_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1652,plain,(
    ! [B_182,A_183] :
      ( r1_xboole_0(B_182,k1_tarski(A_183))
      | r2_hidden(A_183,B_182) ) ),
    inference(resolution,[status(thm)],[c_1512,c_2])).

tff(c_2106,plain,(
    ! [B_214,A_215] :
      ( k4_xboole_0(B_214,k1_tarski(A_215)) = B_214
      | r2_hidden(A_215,B_214) ) ),
    inference(resolution,[status(thm)],[c_1652,c_22])).

tff(c_1638,plain,(
    ! [A_180,B_181] :
      ( r1_tarski(A_180,B_181)
      | k4_xboole_0(A_180,B_181) != '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1551,c_16])).

tff(c_1506,plain,(
    ~ r1_tarski('#skF_2',k1_tarski('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_1651,plain,(
    k4_xboole_0('#skF_2',k1_tarski('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_1638,c_1506])).

tff(c_2143,plain,(
    r2_hidden('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2106,c_1651])).

tff(c_1568,plain,(
    ! [A_171,B_172] :
      ( k4_xboole_0(A_171,B_172) = '#skF_2'
      | ~ r1_tarski(A_171,B_172) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1551,c_18])).

tff(c_1708,plain,(
    ! [A_195,B_196] :
      ( k4_xboole_0(k1_tarski(A_195),B_196) = '#skF_2'
      | ~ r2_hidden(A_195,B_196) ) ),
    inference(resolution,[status(thm)],[c_34,c_1568])).

tff(c_1719,plain,(
    ! [A_195] :
      ( k1_tarski(A_195) = '#skF_2'
      | ~ r2_hidden(A_195,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1708,c_1553])).

tff(c_2216,plain,(
    k1_tarski('#skF_3') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_2143,c_1719])).

tff(c_2217,plain,(
    k4_xboole_0('#skF_2','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2216,c_1651])).

tff(c_2221,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1553,c_2217])).

tff(c_2222,plain,(
    k1_tarski('#skF_3') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1550])).

tff(c_2225,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2222,c_1506])).

tff(c_2228,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_2225])).

tff(c_2230,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_2276,plain,(
    ! [A_230,B_231] :
      ( k4_xboole_0(A_230,B_231) = '#skF_4'
      | ~ r1_tarski(A_230,B_231) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2230,c_18])).

tff(c_2284,plain,(
    ! [B_9] : k4_xboole_0(B_9,B_9) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_14,c_2276])).

tff(c_2231,plain,(
    ! [A_12] : k4_xboole_0(A_12,'#skF_4') = A_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2230,c_20])).

tff(c_2256,plain,(
    ! [A_225,B_226] :
      ( r1_xboole_0(A_225,B_226)
      | k4_xboole_0(A_225,B_226) != A_225 ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2339,plain,(
    ! [B_237,A_238] :
      ( r1_xboole_0(B_237,A_238)
      | k4_xboole_0(A_238,B_237) != A_238 ) ),
    inference(resolution,[status(thm)],[c_2256,c_2])).

tff(c_2434,plain,(
    ! [B_253,A_254] :
      ( k4_xboole_0(B_253,A_254) = B_253
      | k4_xboole_0(A_254,B_253) != A_254 ) ),
    inference(resolution,[status(thm)],[c_2339,c_22])).

tff(c_2442,plain,(
    ! [A_12] : k4_xboole_0('#skF_4',A_12) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_2231,c_2434])).

tff(c_44,plain,
    ( k1_tarski('#skF_3') = '#skF_2'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2318,plain,
    ( k1_tarski('#skF_3') = '#skF_2'
    | '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2230,c_2230,c_44])).

tff(c_2319,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_2318])).

tff(c_2303,plain,(
    ! [A_233,B_234] :
      ( r1_tarski(A_233,B_234)
      | k4_xboole_0(A_233,B_234) != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2230,c_16])).

tff(c_2229,plain,(
    ~ r1_tarski('#skF_2',k1_tarski('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_2316,plain,(
    k4_xboole_0('#skF_2',k1_tarski('#skF_3')) != '#skF_4' ),
    inference(resolution,[status(thm)],[c_2303,c_2229])).

tff(c_2320,plain,(
    k4_xboole_0('#skF_4',k1_tarski('#skF_3')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2319,c_2316])).

tff(c_2458,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2442,c_2320])).

tff(c_2459,plain,(
    k1_tarski('#skF_3') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_2318])).

tff(c_2461,plain,(
    k4_xboole_0('#skF_2','#skF_2') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2459,c_2316])).

tff(c_2465,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2284,c_2461])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n002.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 17:28:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.38/1.56  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.38/1.57  
% 3.38/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.38/1.57  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.38/1.57  
% 3.38/1.57  %Foreground sorts:
% 3.38/1.57  
% 3.38/1.57  
% 3.38/1.57  %Background operators:
% 3.38/1.57  
% 3.38/1.57  
% 3.38/1.57  %Foreground operators:
% 3.38/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.38/1.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.38/1.57  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.38/1.57  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.38/1.57  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.38/1.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.38/1.57  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.38/1.57  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.38/1.57  tff('#skF_5', type, '#skF_5': $i).
% 3.38/1.57  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.38/1.57  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.38/1.57  tff('#skF_2', type, '#skF_2': $i).
% 3.38/1.57  tff('#skF_3', type, '#skF_3': $i).
% 3.38/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.38/1.57  tff('#skF_4', type, '#skF_4': $i).
% 3.38/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.38/1.57  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.38/1.57  
% 3.38/1.59  tff(f_53, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.38/1.59  tff(f_73, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.38/1.59  tff(f_85, negated_conjecture, ~(![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_zfmisc_1)).
% 3.38/1.59  tff(f_57, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.38/1.59  tff(f_78, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 3.38/1.59  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.38/1.59  tff(f_63, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.38/1.59  tff(f_59, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 3.38/1.59  tff(c_14, plain, (![B_9]: (r1_tarski(B_9, B_9))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.38/1.59  tff(c_34, plain, (![A_21, B_22]: (r1_tarski(k1_tarski(A_21), B_22) | ~r2_hidden(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.38/1.59  tff(c_38, plain, (~r1_tarski('#skF_2', k1_tarski('#skF_3')) | k1_tarski('#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.38/1.59  tff(c_80, plain, (k1_tarski('#skF_5')!='#skF_4'), inference(splitLeft, [status(thm)], [c_38])).
% 3.38/1.59  tff(c_116, plain, (![A_45, B_46]: (k4_xboole_0(A_45, B_46)=k1_xboole_0 | ~r1_tarski(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.38/1.59  tff(c_128, plain, (![B_9]: (k4_xboole_0(B_9, B_9)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_116])).
% 3.38/1.59  tff(c_48, plain, (k1_tarski('#skF_3')='#skF_2' | k1_xboole_0='#skF_2' | r1_tarski('#skF_4', k1_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.38/1.59  tff(c_213, plain, (r1_tarski('#skF_4', k1_tarski('#skF_5'))), inference(splitLeft, [status(thm)], [c_48])).
% 3.38/1.59  tff(c_10, plain, (![B_9, A_8]: (B_9=A_8 | ~r1_tarski(B_9, A_8) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.38/1.59  tff(c_215, plain, (k1_tarski('#skF_5')='#skF_4' | ~r1_tarski(k1_tarski('#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_213, c_10])).
% 3.38/1.59  tff(c_221, plain, (~r1_tarski(k1_tarski('#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_80, c_215])).
% 3.38/1.59  tff(c_230, plain, (~r2_hidden('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_34, c_221])).
% 3.38/1.59  tff(c_42, plain, (~r1_tarski('#skF_2', k1_tarski('#skF_3')) | k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.38/1.59  tff(c_70, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_42])).
% 3.38/1.59  tff(c_81, plain, (![A_34, B_35]: (r1_xboole_0(k1_tarski(A_34), B_35) | r2_hidden(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.38/1.59  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.38/1.59  tff(c_151, plain, (![B_48, A_49]: (r1_xboole_0(B_48, k1_tarski(A_49)) | r2_hidden(A_49, B_48))), inference(resolution, [status(thm)], [c_81, c_2])).
% 3.38/1.59  tff(c_22, plain, (![A_13, B_14]: (k4_xboole_0(A_13, B_14)=A_13 | ~r1_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.38/1.59  tff(c_292, plain, (![B_70, A_71]: (k4_xboole_0(B_70, k1_tarski(A_71))=B_70 | r2_hidden(A_71, B_70))), inference(resolution, [status(thm)], [c_151, c_22])).
% 3.38/1.59  tff(c_18, plain, (![A_10, B_11]: (k4_xboole_0(A_10, B_11)=k1_xboole_0 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.38/1.59  tff(c_222, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_5'))=k1_xboole_0), inference(resolution, [status(thm)], [c_213, c_18])).
% 3.38/1.59  tff(c_302, plain, (k1_xboole_0='#skF_4' | r2_hidden('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_292, c_222])).
% 3.38/1.59  tff(c_330, plain, $false, inference(negUnitSimplification, [status(thm)], [c_230, c_70, c_302])).
% 3.38/1.59  tff(c_331, plain, (k1_xboole_0='#skF_2' | k1_tarski('#skF_3')='#skF_2'), inference(splitRight, [status(thm)], [c_48])).
% 3.38/1.59  tff(c_337, plain, (k1_tarski('#skF_3')='#skF_2'), inference(splitLeft, [status(thm)], [c_331])).
% 3.38/1.59  tff(c_16, plain, (![A_10, B_11]: (r1_tarski(A_10, B_11) | k4_xboole_0(A_10, B_11)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.38/1.59  tff(c_46, plain, (~r1_tarski('#skF_2', k1_tarski('#skF_3')) | r1_tarski('#skF_4', k1_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.38/1.59  tff(c_146, plain, (~r1_tarski('#skF_2', k1_tarski('#skF_3'))), inference(splitLeft, [status(thm)], [c_46])).
% 3.38/1.59  tff(c_150, plain, (k4_xboole_0('#skF_2', k1_tarski('#skF_3'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_16, c_146])).
% 3.38/1.59  tff(c_338, plain, (k4_xboole_0('#skF_2', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_337, c_150])).
% 3.38/1.59  tff(c_342, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_128, c_338])).
% 3.38/1.59  tff(c_343, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_331])).
% 3.38/1.59  tff(c_20, plain, (![A_12]: (k4_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.38/1.59  tff(c_351, plain, (![A_12]: (k4_xboole_0(A_12, '#skF_2')=A_12)), inference(demodulation, [status(thm), theory('equality')], [c_343, c_20])).
% 3.38/1.59  tff(c_72, plain, (![A_32, B_33]: (r1_xboole_0(A_32, B_33) | k4_xboole_0(A_32, B_33)!=A_32)), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.38/1.59  tff(c_159, plain, (![B_50, A_51]: (r1_xboole_0(B_50, A_51) | k4_xboole_0(A_51, B_50)!=A_51)), inference(resolution, [status(thm)], [c_72, c_2])).
% 3.38/1.59  tff(c_488, plain, (![B_87, A_88]: (k4_xboole_0(B_87, A_88)=B_87 | k4_xboole_0(A_88, B_87)!=A_88)), inference(resolution, [status(thm)], [c_159, c_22])).
% 3.38/1.59  tff(c_496, plain, (![A_12]: (k4_xboole_0('#skF_2', A_12)='#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_351, c_488])).
% 3.38/1.59  tff(c_346, plain, (k4_xboole_0('#skF_2', k1_tarski('#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_343, c_150])).
% 3.38/1.59  tff(c_499, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_496, c_346])).
% 3.38/1.59  tff(c_500, plain, (r1_tarski('#skF_4', k1_tarski('#skF_5'))), inference(splitRight, [status(thm)], [c_46])).
% 3.38/1.59  tff(c_534, plain, (![B_93, A_94]: (B_93=A_94 | ~r1_tarski(B_93, A_94) | ~r1_tarski(A_94, B_93))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.38/1.59  tff(c_538, plain, (k1_tarski('#skF_5')='#skF_4' | ~r1_tarski(k1_tarski('#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_500, c_534])).
% 3.38/1.59  tff(c_548, plain, (~r1_tarski(k1_tarski('#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_80, c_538])).
% 3.38/1.59  tff(c_562, plain, (~r2_hidden('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_34, c_548])).
% 3.38/1.59  tff(c_518, plain, (![B_89, A_90]: (r1_xboole_0(B_89, k1_tarski(A_90)) | r2_hidden(A_90, B_89))), inference(resolution, [status(thm)], [c_81, c_2])).
% 3.38/1.59  tff(c_1458, plain, (![B_160, A_161]: (k4_xboole_0(B_160, k1_tarski(A_161))=B_160 | r2_hidden(A_161, B_160))), inference(resolution, [status(thm)], [c_518, c_22])).
% 3.38/1.59  tff(c_505, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_5'))=k1_xboole_0), inference(resolution, [status(thm)], [c_500, c_18])).
% 3.38/1.59  tff(c_1476, plain, (k1_xboole_0='#skF_4' | r2_hidden('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1458, c_505])).
% 3.38/1.59  tff(c_1505, plain, $false, inference(negUnitSimplification, [status(thm)], [c_562, c_70, c_1476])).
% 3.38/1.59  tff(c_1507, plain, (k1_tarski('#skF_5')='#skF_4'), inference(splitRight, [status(thm)], [c_38])).
% 3.38/1.59  tff(c_40, plain, (k1_tarski('#skF_3')='#skF_2' | k1_xboole_0='#skF_2' | k1_tarski('#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.38/1.59  tff(c_1550, plain, (k1_tarski('#skF_3')='#skF_2' | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1507, c_40])).
% 3.38/1.59  tff(c_1551, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_1550])).
% 3.38/1.59  tff(c_1553, plain, (![A_12]: (k4_xboole_0(A_12, '#skF_2')=A_12)), inference(demodulation, [status(thm), theory('equality')], [c_1551, c_20])).
% 3.38/1.59  tff(c_1512, plain, (![A_162, B_163]: (r1_xboole_0(k1_tarski(A_162), B_163) | r2_hidden(A_162, B_163))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.38/1.59  tff(c_1652, plain, (![B_182, A_183]: (r1_xboole_0(B_182, k1_tarski(A_183)) | r2_hidden(A_183, B_182))), inference(resolution, [status(thm)], [c_1512, c_2])).
% 3.38/1.59  tff(c_2106, plain, (![B_214, A_215]: (k4_xboole_0(B_214, k1_tarski(A_215))=B_214 | r2_hidden(A_215, B_214))), inference(resolution, [status(thm)], [c_1652, c_22])).
% 3.38/1.59  tff(c_1638, plain, (![A_180, B_181]: (r1_tarski(A_180, B_181) | k4_xboole_0(A_180, B_181)!='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1551, c_16])).
% 3.38/1.59  tff(c_1506, plain, (~r1_tarski('#skF_2', k1_tarski('#skF_3'))), inference(splitRight, [status(thm)], [c_38])).
% 3.38/1.59  tff(c_1651, plain, (k4_xboole_0('#skF_2', k1_tarski('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_1638, c_1506])).
% 3.38/1.59  tff(c_2143, plain, (r2_hidden('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2106, c_1651])).
% 3.38/1.59  tff(c_1568, plain, (![A_171, B_172]: (k4_xboole_0(A_171, B_172)='#skF_2' | ~r1_tarski(A_171, B_172))), inference(demodulation, [status(thm), theory('equality')], [c_1551, c_18])).
% 3.38/1.59  tff(c_1708, plain, (![A_195, B_196]: (k4_xboole_0(k1_tarski(A_195), B_196)='#skF_2' | ~r2_hidden(A_195, B_196))), inference(resolution, [status(thm)], [c_34, c_1568])).
% 3.38/1.59  tff(c_1719, plain, (![A_195]: (k1_tarski(A_195)='#skF_2' | ~r2_hidden(A_195, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1708, c_1553])).
% 3.38/1.59  tff(c_2216, plain, (k1_tarski('#skF_3')='#skF_2'), inference(resolution, [status(thm)], [c_2143, c_1719])).
% 3.38/1.59  tff(c_2217, plain, (k4_xboole_0('#skF_2', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2216, c_1651])).
% 3.38/1.59  tff(c_2221, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1553, c_2217])).
% 3.38/1.59  tff(c_2222, plain, (k1_tarski('#skF_3')='#skF_2'), inference(splitRight, [status(thm)], [c_1550])).
% 3.38/1.59  tff(c_2225, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2222, c_1506])).
% 3.38/1.59  tff(c_2228, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_2225])).
% 3.38/1.59  tff(c_2230, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_42])).
% 3.38/1.59  tff(c_2276, plain, (![A_230, B_231]: (k4_xboole_0(A_230, B_231)='#skF_4' | ~r1_tarski(A_230, B_231))), inference(demodulation, [status(thm), theory('equality')], [c_2230, c_18])).
% 3.38/1.59  tff(c_2284, plain, (![B_9]: (k4_xboole_0(B_9, B_9)='#skF_4')), inference(resolution, [status(thm)], [c_14, c_2276])).
% 3.38/1.59  tff(c_2231, plain, (![A_12]: (k4_xboole_0(A_12, '#skF_4')=A_12)), inference(demodulation, [status(thm), theory('equality')], [c_2230, c_20])).
% 3.38/1.59  tff(c_2256, plain, (![A_225, B_226]: (r1_xboole_0(A_225, B_226) | k4_xboole_0(A_225, B_226)!=A_225)), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.38/1.59  tff(c_2339, plain, (![B_237, A_238]: (r1_xboole_0(B_237, A_238) | k4_xboole_0(A_238, B_237)!=A_238)), inference(resolution, [status(thm)], [c_2256, c_2])).
% 3.38/1.59  tff(c_2434, plain, (![B_253, A_254]: (k4_xboole_0(B_253, A_254)=B_253 | k4_xboole_0(A_254, B_253)!=A_254)), inference(resolution, [status(thm)], [c_2339, c_22])).
% 3.38/1.59  tff(c_2442, plain, (![A_12]: (k4_xboole_0('#skF_4', A_12)='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2231, c_2434])).
% 3.38/1.59  tff(c_44, plain, (k1_tarski('#skF_3')='#skF_2' | k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.38/1.59  tff(c_2318, plain, (k1_tarski('#skF_3')='#skF_2' | '#skF_2'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2230, c_2230, c_44])).
% 3.38/1.59  tff(c_2319, plain, ('#skF_2'='#skF_4'), inference(splitLeft, [status(thm)], [c_2318])).
% 3.38/1.59  tff(c_2303, plain, (![A_233, B_234]: (r1_tarski(A_233, B_234) | k4_xboole_0(A_233, B_234)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2230, c_16])).
% 3.38/1.59  tff(c_2229, plain, (~r1_tarski('#skF_2', k1_tarski('#skF_3'))), inference(splitRight, [status(thm)], [c_42])).
% 3.38/1.59  tff(c_2316, plain, (k4_xboole_0('#skF_2', k1_tarski('#skF_3'))!='#skF_4'), inference(resolution, [status(thm)], [c_2303, c_2229])).
% 3.38/1.59  tff(c_2320, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_3'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2319, c_2316])).
% 3.38/1.59  tff(c_2458, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2442, c_2320])).
% 3.38/1.59  tff(c_2459, plain, (k1_tarski('#skF_3')='#skF_2'), inference(splitRight, [status(thm)], [c_2318])).
% 3.38/1.59  tff(c_2461, plain, (k4_xboole_0('#skF_2', '#skF_2')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2459, c_2316])).
% 3.38/1.59  tff(c_2465, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2284, c_2461])).
% 3.38/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.38/1.59  
% 3.38/1.59  Inference rules
% 3.38/1.59  ----------------------
% 3.38/1.59  #Ref     : 0
% 3.38/1.59  #Sup     : 517
% 3.38/1.59  #Fact    : 2
% 3.38/1.59  #Define  : 0
% 3.38/1.59  #Split   : 10
% 3.38/1.59  #Chain   : 0
% 3.38/1.59  #Close   : 0
% 3.38/1.59  
% 3.38/1.59  Ordering : KBO
% 3.38/1.59  
% 3.38/1.59  Simplification rules
% 3.38/1.59  ----------------------
% 3.38/1.59  #Subsume      : 79
% 3.38/1.59  #Demod        : 202
% 3.38/1.59  #Tautology    : 228
% 3.38/1.59  #SimpNegUnit  : 30
% 3.38/1.59  #BackRed      : 36
% 3.38/1.59  
% 3.38/1.59  #Partial instantiations: 0
% 3.38/1.59  #Strategies tried      : 1
% 3.38/1.59  
% 3.38/1.59  Timing (in seconds)
% 3.38/1.59  ----------------------
% 3.38/1.59  Preprocessing        : 0.30
% 3.38/1.59  Parsing              : 0.16
% 3.38/1.59  CNF conversion       : 0.02
% 3.38/1.59  Main loop            : 0.53
% 3.38/1.59  Inferencing          : 0.21
% 3.38/1.59  Reduction            : 0.15
% 3.38/1.59  Demodulation         : 0.10
% 3.38/1.59  BG Simplification    : 0.02
% 3.38/1.59  Subsumption          : 0.09
% 3.38/1.59  Abstraction          : 0.02
% 3.38/1.59  MUC search           : 0.00
% 3.38/1.59  Cooper               : 0.00
% 3.38/1.59  Total                : 0.87
% 3.38/1.59  Index Insertion      : 0.00
% 3.38/1.59  Index Deletion       : 0.00
% 3.38/1.59  Index Matching       : 0.00
% 3.38/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
