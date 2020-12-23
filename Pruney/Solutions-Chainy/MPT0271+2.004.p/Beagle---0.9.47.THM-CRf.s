%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:01 EST 2020

% Result     : Theorem 4.45s
% Output     : CNFRefutation 4.56s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 140 expanded)
%              Number of leaves         :   42 (  64 expanded)
%              Depth                    :    9
%              Number of atoms          :  106 ( 158 expanded)
%              Number of equality atoms :   61 (  93 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_8 > #skF_3

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_100,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
      <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_zfmisc_1)).

tff(f_75,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_77,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_73,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_46,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_48,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_54,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_50,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_52,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_56,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_90,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | ~ r2_hidden('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_192,plain,(
    ~ r2_hidden('#skF_7','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_90])).

tff(c_66,plain,(
    ! [A_34] : k2_tarski(A_34,A_34) = k1_tarski(A_34) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_335,plain,(
    ! [A_92,B_93] : k1_enumset1(A_92,A_92,B_93) = k2_tarski(A_92,B_93) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_48,plain,(
    ! [E_33,B_28,C_29] : r2_hidden(E_33,k1_enumset1(E_33,B_28,C_29)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_353,plain,(
    ! [A_94,B_95] : r2_hidden(A_94,k2_tarski(A_94,B_95)) ),
    inference(superposition,[status(thm),theory(equality)],[c_335,c_48])).

tff(c_362,plain,(
    ! [A_34] : r2_hidden(A_34,k1_tarski(A_34)) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_353])).

tff(c_28,plain,(
    ! [A_15] : k2_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_94,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | k4_xboole_0(k1_tarski('#skF_7'),'#skF_8') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_329,plain,(
    k4_xboole_0(k1_tarski('#skF_7'),'#skF_8') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_94])).

tff(c_511,plain,(
    ! [A_108,B_109] : k2_xboole_0(A_108,k4_xboole_0(B_109,A_108)) = k2_xboole_0(A_108,B_109) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_528,plain,(
    k2_xboole_0('#skF_8',k1_tarski('#skF_7')) = k2_xboole_0('#skF_8',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_329,c_511])).

tff(c_533,plain,(
    k2_xboole_0('#skF_8',k1_tarski('#skF_7')) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_528])).

tff(c_683,plain,(
    ! [D_121,B_122,A_123] :
      ( ~ r2_hidden(D_121,B_122)
      | r2_hidden(D_121,k2_xboole_0(A_123,B_122)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_708,plain,(
    ! [D_124] :
      ( ~ r2_hidden(D_124,k1_tarski('#skF_7'))
      | r2_hidden(D_124,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_533,c_683])).

tff(c_712,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_362,c_708])).

tff(c_716,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_192,c_712])).

tff(c_717,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_36,plain,(
    ! [A_22] : k5_xboole_0(A_22,A_22) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_194,plain,(
    ! [B_84,A_85] : k5_xboole_0(B_84,A_85) = k5_xboole_0(A_85,B_84) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_32,plain,(
    ! [A_18] : k5_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_210,plain,(
    ! [A_85] : k5_xboole_0(k1_xboole_0,A_85) = A_85 ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_32])).

tff(c_1215,plain,(
    ! [A_167,B_168,C_169] : k5_xboole_0(k5_xboole_0(A_167,B_168),C_169) = k5_xboole_0(A_167,k5_xboole_0(B_168,C_169)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1272,plain,(
    ! [A_22,C_169] : k5_xboole_0(A_22,k5_xboole_0(A_22,C_169)) = k5_xboole_0(k1_xboole_0,C_169) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_1215])).

tff(c_1293,plain,(
    ! [A_170,C_171] : k5_xboole_0(A_170,k5_xboole_0(A_170,C_171)) = C_171 ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_1272])).

tff(c_1336,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k5_xboole_0(B_2,A_1)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1293])).

tff(c_82,plain,(
    ! [A_62,B_63] :
      ( r1_tarski(k1_tarski(A_62),B_63)
      | ~ r2_hidden(A_62,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_770,plain,(
    ! [A_136,B_137] :
      ( k2_xboole_0(A_136,B_137) = B_137
      | ~ r1_tarski(A_136,B_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_774,plain,(
    ! [A_62,B_63] :
      ( k2_xboole_0(k1_tarski(A_62),B_63) = B_63
      | ~ r2_hidden(A_62,B_63) ) ),
    inference(resolution,[status(thm)],[c_82,c_770])).

tff(c_1438,plain,(
    ! [A_174,B_175] : k5_xboole_0(k5_xboole_0(A_174,B_175),k2_xboole_0(A_174,B_175)) = k3_xboole_0(A_174,B_175) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1487,plain,(
    ! [A_62,B_63] :
      ( k5_xboole_0(k5_xboole_0(k1_tarski(A_62),B_63),B_63) = k3_xboole_0(k1_tarski(A_62),B_63)
      | ~ r2_hidden(A_62,B_63) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_774,c_1438])).

tff(c_2294,plain,(
    ! [A_221,B_222] :
      ( k3_xboole_0(k1_tarski(A_221),B_222) = k1_tarski(A_221)
      | ~ r2_hidden(A_221,B_222) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1336,c_2,c_1487])).

tff(c_24,plain,(
    ! [A_11,B_12] : k5_xboole_0(A_11,k3_xboole_0(A_11,B_12)) = k4_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2313,plain,(
    ! [A_221,B_222] :
      ( k5_xboole_0(k1_tarski(A_221),k1_tarski(A_221)) = k4_xboole_0(k1_tarski(A_221),B_222)
      | ~ r2_hidden(A_221,B_222) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2294,c_24])).

tff(c_2341,plain,(
    ! [A_223,B_224] :
      ( k4_xboole_0(k1_tarski(A_223),B_224) = k1_xboole_0
      | ~ r2_hidden(A_223,B_224) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2313])).

tff(c_718,plain,(
    k4_xboole_0(k1_tarski('#skF_7'),'#skF_8') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_92,plain,
    ( k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') != k1_xboole_0
    | k4_xboole_0(k1_tarski('#skF_7'),'#skF_8') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_849,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_718,c_92])).

tff(c_2370,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_2341,c_849])).

tff(c_2397,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_717,c_2370])).

tff(c_2398,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_2406,plain,(
    ! [B_225,A_226] : k5_xboole_0(B_225,A_226) = k5_xboole_0(A_226,B_225) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_2422,plain,(
    ! [A_226] : k5_xboole_0(k1_xboole_0,A_226) = A_226 ),
    inference(superposition,[status(thm),theory(equality)],[c_2406,c_32])).

tff(c_2979,plain,(
    ! [A_274,B_275,C_276] : k5_xboole_0(k5_xboole_0(A_274,B_275),C_276) = k5_xboole_0(A_274,k5_xboole_0(B_275,C_276)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_3036,plain,(
    ! [A_22,C_276] : k5_xboole_0(A_22,k5_xboole_0(A_22,C_276)) = k5_xboole_0(k1_xboole_0,C_276) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_2979])).

tff(c_3057,plain,(
    ! [A_277,C_278] : k5_xboole_0(A_277,k5_xboole_0(A_277,C_278)) = C_278 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2422,c_3036])).

tff(c_3100,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k5_xboole_0(B_2,A_1)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_3057])).

tff(c_2506,plain,(
    ! [A_233,B_234] :
      ( k2_xboole_0(A_233,B_234) = B_234
      | ~ r1_tarski(A_233,B_234) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2510,plain,(
    ! [A_62,B_63] :
      ( k2_xboole_0(k1_tarski(A_62),B_63) = B_63
      | ~ r2_hidden(A_62,B_63) ) ),
    inference(resolution,[status(thm)],[c_82,c_2506])).

tff(c_3298,plain,(
    ! [A_283,B_284] : k5_xboole_0(k5_xboole_0(A_283,B_284),k2_xboole_0(A_283,B_284)) = k3_xboole_0(A_283,B_284) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_3350,plain,(
    ! [A_62,B_63] :
      ( k5_xboole_0(k5_xboole_0(k1_tarski(A_62),B_63),B_63) = k3_xboole_0(k1_tarski(A_62),B_63)
      | ~ r2_hidden(A_62,B_63) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2510,c_3298])).

tff(c_4121,plain,(
    ! [A_330,B_331] :
      ( k3_xboole_0(k1_tarski(A_330),B_331) = k1_tarski(A_330)
      | ~ r2_hidden(A_330,B_331) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3100,c_2,c_3350])).

tff(c_4140,plain,(
    ! [A_330,B_331] :
      ( k5_xboole_0(k1_tarski(A_330),k1_tarski(A_330)) = k4_xboole_0(k1_tarski(A_330),B_331)
      | ~ r2_hidden(A_330,B_331) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4121,c_24])).

tff(c_4177,plain,(
    ! [A_335,B_336] :
      ( k4_xboole_0(k1_tarski(A_335),B_336) = k1_xboole_0
      | ~ r2_hidden(A_335,B_336) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_4140])).

tff(c_2399,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_88,plain,
    ( k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') != k1_xboole_0
    | ~ r2_hidden('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_2400,plain,(
    ~ r2_hidden('#skF_7','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_88])).

tff(c_2402,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2399,c_2400])).

tff(c_2403,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_4206,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_4177,c_2403])).

tff(c_4230,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2398,c_4206])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:18:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.45/1.81  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.53/1.81  
% 4.53/1.81  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.56/1.82  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_8 > #skF_3
% 4.56/1.82  
% 4.56/1.82  %Foreground sorts:
% 4.56/1.82  
% 4.56/1.82  
% 4.56/1.82  %Background operators:
% 4.56/1.82  
% 4.56/1.82  
% 4.56/1.82  %Foreground operators:
% 4.56/1.82  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.56/1.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.56/1.82  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.56/1.82  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.56/1.82  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.56/1.82  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.56/1.82  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.56/1.82  tff('#skF_7', type, '#skF_7': $i).
% 4.56/1.82  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.56/1.82  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.56/1.82  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.56/1.82  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.56/1.82  tff('#skF_5', type, '#skF_5': $i).
% 4.56/1.82  tff('#skF_6', type, '#skF_6': $i).
% 4.56/1.82  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.56/1.82  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.56/1.82  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.56/1.82  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 4.56/1.82  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.56/1.82  tff('#skF_8', type, '#skF_8': $i).
% 4.56/1.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.56/1.82  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.56/1.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.56/1.82  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.56/1.82  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 4.56/1.82  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.56/1.82  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.56/1.82  
% 4.56/1.83  tff(f_100, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_zfmisc_1)).
% 4.56/1.83  tff(f_75, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 4.56/1.83  tff(f_77, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 4.56/1.83  tff(f_73, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 4.56/1.83  tff(f_46, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 4.56/1.83  tff(f_48, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 4.56/1.83  tff(f_36, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 4.56/1.83  tff(f_54, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 4.56/1.83  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 4.56/1.83  tff(f_50, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 4.56/1.83  tff(f_52, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 4.56/1.83  tff(f_91, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 4.56/1.83  tff(f_44, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 4.56/1.83  tff(f_56, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 4.56/1.83  tff(f_40, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.56/1.83  tff(c_90, plain, (r2_hidden('#skF_5', '#skF_6') | ~r2_hidden('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.56/1.83  tff(c_192, plain, (~r2_hidden('#skF_7', '#skF_8')), inference(splitLeft, [status(thm)], [c_90])).
% 4.56/1.83  tff(c_66, plain, (![A_34]: (k2_tarski(A_34, A_34)=k1_tarski(A_34))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.56/1.83  tff(c_335, plain, (![A_92, B_93]: (k1_enumset1(A_92, A_92, B_93)=k2_tarski(A_92, B_93))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.56/1.83  tff(c_48, plain, (![E_33, B_28, C_29]: (r2_hidden(E_33, k1_enumset1(E_33, B_28, C_29)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.56/1.83  tff(c_353, plain, (![A_94, B_95]: (r2_hidden(A_94, k2_tarski(A_94, B_95)))), inference(superposition, [status(thm), theory('equality')], [c_335, c_48])).
% 4.56/1.83  tff(c_362, plain, (![A_34]: (r2_hidden(A_34, k1_tarski(A_34)))), inference(superposition, [status(thm), theory('equality')], [c_66, c_353])).
% 4.56/1.83  tff(c_28, plain, (![A_15]: (k2_xboole_0(A_15, k1_xboole_0)=A_15)), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.56/1.83  tff(c_94, plain, (r2_hidden('#skF_5', '#skF_6') | k4_xboole_0(k1_tarski('#skF_7'), '#skF_8')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.56/1.83  tff(c_329, plain, (k4_xboole_0(k1_tarski('#skF_7'), '#skF_8')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_94])).
% 4.56/1.83  tff(c_511, plain, (![A_108, B_109]: (k2_xboole_0(A_108, k4_xboole_0(B_109, A_108))=k2_xboole_0(A_108, B_109))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.56/1.83  tff(c_528, plain, (k2_xboole_0('#skF_8', k1_tarski('#skF_7'))=k2_xboole_0('#skF_8', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_329, c_511])).
% 4.56/1.83  tff(c_533, plain, (k2_xboole_0('#skF_8', k1_tarski('#skF_7'))='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_528])).
% 4.56/1.83  tff(c_683, plain, (![D_121, B_122, A_123]: (~r2_hidden(D_121, B_122) | r2_hidden(D_121, k2_xboole_0(A_123, B_122)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.56/1.83  tff(c_708, plain, (![D_124]: (~r2_hidden(D_124, k1_tarski('#skF_7')) | r2_hidden(D_124, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_533, c_683])).
% 4.56/1.83  tff(c_712, plain, (r2_hidden('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_362, c_708])).
% 4.56/1.83  tff(c_716, plain, $false, inference(negUnitSimplification, [status(thm)], [c_192, c_712])).
% 4.56/1.83  tff(c_717, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_94])).
% 4.56/1.83  tff(c_36, plain, (![A_22]: (k5_xboole_0(A_22, A_22)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.56/1.83  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.56/1.83  tff(c_194, plain, (![B_84, A_85]: (k5_xboole_0(B_84, A_85)=k5_xboole_0(A_85, B_84))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.56/1.83  tff(c_32, plain, (![A_18]: (k5_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.56/1.83  tff(c_210, plain, (![A_85]: (k5_xboole_0(k1_xboole_0, A_85)=A_85)), inference(superposition, [status(thm), theory('equality')], [c_194, c_32])).
% 4.56/1.83  tff(c_1215, plain, (![A_167, B_168, C_169]: (k5_xboole_0(k5_xboole_0(A_167, B_168), C_169)=k5_xboole_0(A_167, k5_xboole_0(B_168, C_169)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.56/1.83  tff(c_1272, plain, (![A_22, C_169]: (k5_xboole_0(A_22, k5_xboole_0(A_22, C_169))=k5_xboole_0(k1_xboole_0, C_169))), inference(superposition, [status(thm), theory('equality')], [c_36, c_1215])).
% 4.56/1.83  tff(c_1293, plain, (![A_170, C_171]: (k5_xboole_0(A_170, k5_xboole_0(A_170, C_171))=C_171)), inference(demodulation, [status(thm), theory('equality')], [c_210, c_1272])).
% 4.56/1.83  tff(c_1336, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k5_xboole_0(B_2, A_1))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_1293])).
% 4.56/1.83  tff(c_82, plain, (![A_62, B_63]: (r1_tarski(k1_tarski(A_62), B_63) | ~r2_hidden(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.56/1.83  tff(c_770, plain, (![A_136, B_137]: (k2_xboole_0(A_136, B_137)=B_137 | ~r1_tarski(A_136, B_137))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.56/1.83  tff(c_774, plain, (![A_62, B_63]: (k2_xboole_0(k1_tarski(A_62), B_63)=B_63 | ~r2_hidden(A_62, B_63))), inference(resolution, [status(thm)], [c_82, c_770])).
% 4.56/1.83  tff(c_1438, plain, (![A_174, B_175]: (k5_xboole_0(k5_xboole_0(A_174, B_175), k2_xboole_0(A_174, B_175))=k3_xboole_0(A_174, B_175))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.56/1.83  tff(c_1487, plain, (![A_62, B_63]: (k5_xboole_0(k5_xboole_0(k1_tarski(A_62), B_63), B_63)=k3_xboole_0(k1_tarski(A_62), B_63) | ~r2_hidden(A_62, B_63))), inference(superposition, [status(thm), theory('equality')], [c_774, c_1438])).
% 4.56/1.83  tff(c_2294, plain, (![A_221, B_222]: (k3_xboole_0(k1_tarski(A_221), B_222)=k1_tarski(A_221) | ~r2_hidden(A_221, B_222))), inference(demodulation, [status(thm), theory('equality')], [c_1336, c_2, c_1487])).
% 4.56/1.83  tff(c_24, plain, (![A_11, B_12]: (k5_xboole_0(A_11, k3_xboole_0(A_11, B_12))=k4_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.56/1.83  tff(c_2313, plain, (![A_221, B_222]: (k5_xboole_0(k1_tarski(A_221), k1_tarski(A_221))=k4_xboole_0(k1_tarski(A_221), B_222) | ~r2_hidden(A_221, B_222))), inference(superposition, [status(thm), theory('equality')], [c_2294, c_24])).
% 4.56/1.83  tff(c_2341, plain, (![A_223, B_224]: (k4_xboole_0(k1_tarski(A_223), B_224)=k1_xboole_0 | ~r2_hidden(A_223, B_224))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_2313])).
% 4.56/1.83  tff(c_718, plain, (k4_xboole_0(k1_tarski('#skF_7'), '#skF_8')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_94])).
% 4.56/1.83  tff(c_92, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')!=k1_xboole_0 | k4_xboole_0(k1_tarski('#skF_7'), '#skF_8')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.56/1.83  tff(c_849, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_718, c_92])).
% 4.56/1.83  tff(c_2370, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_2341, c_849])).
% 4.56/1.83  tff(c_2397, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_717, c_2370])).
% 4.56/1.83  tff(c_2398, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_90])).
% 4.56/1.83  tff(c_2406, plain, (![B_225, A_226]: (k5_xboole_0(B_225, A_226)=k5_xboole_0(A_226, B_225))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.56/1.83  tff(c_2422, plain, (![A_226]: (k5_xboole_0(k1_xboole_0, A_226)=A_226)), inference(superposition, [status(thm), theory('equality')], [c_2406, c_32])).
% 4.56/1.83  tff(c_2979, plain, (![A_274, B_275, C_276]: (k5_xboole_0(k5_xboole_0(A_274, B_275), C_276)=k5_xboole_0(A_274, k5_xboole_0(B_275, C_276)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.56/1.83  tff(c_3036, plain, (![A_22, C_276]: (k5_xboole_0(A_22, k5_xboole_0(A_22, C_276))=k5_xboole_0(k1_xboole_0, C_276))), inference(superposition, [status(thm), theory('equality')], [c_36, c_2979])).
% 4.56/1.83  tff(c_3057, plain, (![A_277, C_278]: (k5_xboole_0(A_277, k5_xboole_0(A_277, C_278))=C_278)), inference(demodulation, [status(thm), theory('equality')], [c_2422, c_3036])).
% 4.56/1.83  tff(c_3100, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k5_xboole_0(B_2, A_1))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_3057])).
% 4.56/1.83  tff(c_2506, plain, (![A_233, B_234]: (k2_xboole_0(A_233, B_234)=B_234 | ~r1_tarski(A_233, B_234))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.56/1.83  tff(c_2510, plain, (![A_62, B_63]: (k2_xboole_0(k1_tarski(A_62), B_63)=B_63 | ~r2_hidden(A_62, B_63))), inference(resolution, [status(thm)], [c_82, c_2506])).
% 4.56/1.83  tff(c_3298, plain, (![A_283, B_284]: (k5_xboole_0(k5_xboole_0(A_283, B_284), k2_xboole_0(A_283, B_284))=k3_xboole_0(A_283, B_284))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.56/1.83  tff(c_3350, plain, (![A_62, B_63]: (k5_xboole_0(k5_xboole_0(k1_tarski(A_62), B_63), B_63)=k3_xboole_0(k1_tarski(A_62), B_63) | ~r2_hidden(A_62, B_63))), inference(superposition, [status(thm), theory('equality')], [c_2510, c_3298])).
% 4.56/1.83  tff(c_4121, plain, (![A_330, B_331]: (k3_xboole_0(k1_tarski(A_330), B_331)=k1_tarski(A_330) | ~r2_hidden(A_330, B_331))), inference(demodulation, [status(thm), theory('equality')], [c_3100, c_2, c_3350])).
% 4.56/1.83  tff(c_4140, plain, (![A_330, B_331]: (k5_xboole_0(k1_tarski(A_330), k1_tarski(A_330))=k4_xboole_0(k1_tarski(A_330), B_331) | ~r2_hidden(A_330, B_331))), inference(superposition, [status(thm), theory('equality')], [c_4121, c_24])).
% 4.56/1.83  tff(c_4177, plain, (![A_335, B_336]: (k4_xboole_0(k1_tarski(A_335), B_336)=k1_xboole_0 | ~r2_hidden(A_335, B_336))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_4140])).
% 4.56/1.83  tff(c_2399, plain, (r2_hidden('#skF_7', '#skF_8')), inference(splitRight, [status(thm)], [c_90])).
% 4.56/1.83  tff(c_88, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')!=k1_xboole_0 | ~r2_hidden('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.56/1.83  tff(c_2400, plain, (~r2_hidden('#skF_7', '#skF_8')), inference(splitLeft, [status(thm)], [c_88])).
% 4.56/1.83  tff(c_2402, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2399, c_2400])).
% 4.56/1.83  tff(c_2403, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_88])).
% 4.56/1.83  tff(c_4206, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_4177, c_2403])).
% 4.56/1.83  tff(c_4230, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2398, c_4206])).
% 4.56/1.83  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.56/1.83  
% 4.56/1.83  Inference rules
% 4.56/1.83  ----------------------
% 4.56/1.83  #Ref     : 0
% 4.56/1.83  #Sup     : 994
% 4.56/1.83  #Fact    : 0
% 4.56/1.83  #Define  : 0
% 4.56/1.83  #Split   : 3
% 4.56/1.83  #Chain   : 0
% 4.56/1.83  #Close   : 0
% 4.56/1.83  
% 4.56/1.83  Ordering : KBO
% 4.56/1.83  
% 4.56/1.83  Simplification rules
% 4.56/1.83  ----------------------
% 4.56/1.83  #Subsume      : 72
% 4.56/1.83  #Demod        : 552
% 4.56/1.83  #Tautology    : 693
% 4.56/1.83  #SimpNegUnit  : 2
% 4.56/1.83  #BackRed      : 4
% 4.56/1.83  
% 4.56/1.83  #Partial instantiations: 0
% 4.56/1.83  #Strategies tried      : 1
% 4.56/1.83  
% 4.56/1.83  Timing (in seconds)
% 4.56/1.83  ----------------------
% 4.56/1.84  Preprocessing        : 0.35
% 4.56/1.84  Parsing              : 0.18
% 4.56/1.84  CNF conversion       : 0.03
% 4.56/1.84  Main loop            : 0.71
% 4.56/1.84  Inferencing          : 0.24
% 4.56/1.84  Reduction            : 0.29
% 4.56/1.84  Demodulation         : 0.24
% 4.56/1.84  BG Simplification    : 0.04
% 4.56/1.84  Subsumption          : 0.10
% 4.56/1.84  Abstraction          : 0.04
% 4.56/1.84  MUC search           : 0.00
% 4.56/1.84  Cooper               : 0.00
% 4.56/1.84  Total                : 1.10
% 4.56/1.84  Index Insertion      : 0.00
% 4.56/1.84  Index Deletion       : 0.00
% 4.56/1.84  Index Matching       : 0.00
% 4.56/1.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
