%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:52 EST 2020

% Result     : Theorem 11.24s
% Output     : CNFRefutation 11.47s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 191 expanded)
%              Number of leaves         :   35 (  78 expanded)
%              Depth                    :   14
%              Number of atoms          :  157 ( 354 expanded)
%              Number of equality atoms :   60 ( 100 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_11 > #skF_4 > #skF_10 > #skF_5 > #skF_2 > #skF_7 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_100,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
      <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_zfmisc_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_68,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_64,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_66,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_85,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_87,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_83,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_94,plain,
    ( ~ r2_hidden('#skF_8','#skF_9')
    | r2_hidden('#skF_10','#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_110,plain,(
    ~ r2_hidden('#skF_8','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_94])).

tff(c_90,plain,(
    ! [A_41,B_42] :
      ( k4_xboole_0(A_41,k1_tarski(B_42)) = A_41
      | r2_hidden(B_42,A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_269,plain,(
    ! [A_99,B_100] : k4_xboole_0(A_99,k4_xboole_0(A_99,B_100)) = k3_xboole_0(A_99,B_100) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_290,plain,(
    ! [A_41,B_42] :
      ( k4_xboole_0(A_41,A_41) = k3_xboole_0(A_41,k1_tarski(B_42))
      | r2_hidden(B_42,A_41) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_269])).

tff(c_300,plain,(
    ! [A_103,B_104] :
      ( r2_hidden('#skF_1'(A_103,B_104),A_103)
      | r1_tarski(A_103,B_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_34,plain,(
    ! [D_21,A_16,B_17] :
      ( r2_hidden(D_21,A_16)
      | ~ r2_hidden(D_21,k4_xboole_0(A_16,B_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_328,plain,(
    ! [A_16,B_17,B_104] :
      ( r2_hidden('#skF_1'(k4_xboole_0(A_16,B_17),B_104),A_16)
      | r1_tarski(k4_xboole_0(A_16,B_17),B_104) ) ),
    inference(resolution,[status(thm)],[c_300,c_34])).

tff(c_32,plain,(
    ! [D_21,B_17,A_16] :
      ( ~ r2_hidden(D_21,B_17)
      | ~ r2_hidden(D_21,k4_xboole_0(A_16,B_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2612,plain,(
    ! [A_285,B_286,B_287] :
      ( ~ r2_hidden('#skF_1'(k4_xboole_0(A_285,B_286),B_287),B_286)
      | r1_tarski(k4_xboole_0(A_285,B_286),B_287) ) ),
    inference(resolution,[status(thm)],[c_300,c_32])).

tff(c_2655,plain,(
    ! [A_288,B_289] : r1_tarski(k4_xboole_0(A_288,A_288),B_289) ),
    inference(resolution,[status(thm)],[c_328,c_2612])).

tff(c_6957,plain,(
    ! [A_419,B_420,B_421] :
      ( r1_tarski(k3_xboole_0(A_419,k1_tarski(B_420)),B_421)
      | r2_hidden(B_420,A_419) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_290,c_2655])).

tff(c_48,plain,(
    ! [B_23,A_22] :
      ( B_23 = A_22
      | ~ r1_tarski(B_23,A_22)
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2696,plain,(
    ! [A_288,B_289] :
      ( k4_xboole_0(A_288,A_288) = B_289
      | ~ r1_tarski(B_289,k4_xboole_0(A_288,A_288)) ) ),
    inference(resolution,[status(thm)],[c_2655,c_48])).

tff(c_7015,plain,(
    ! [A_288,A_419,B_420] :
      ( k4_xboole_0(A_288,A_288) = k3_xboole_0(A_419,k1_tarski(B_420))
      | r2_hidden(B_420,A_419) ) ),
    inference(resolution,[status(thm)],[c_6957,c_2696])).

tff(c_1379,plain,(
    ! [A_194,B_195,C_196] :
      ( r2_hidden('#skF_2'(A_194,B_195,C_196),B_195)
      | r2_hidden('#skF_3'(A_194,B_195,C_196),C_196)
      | k3_xboole_0(A_194,B_195) = C_196 ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_24,plain,(
    ! [A_10,B_11,C_12] :
      ( ~ r2_hidden('#skF_2'(A_10,B_11,C_12),C_12)
      | r2_hidden('#skF_3'(A_10,B_11,C_12),C_12)
      | k3_xboole_0(A_10,B_11) = C_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1462,plain,(
    ! [A_194,B_195] :
      ( r2_hidden('#skF_3'(A_194,B_195,B_195),B_195)
      | k3_xboole_0(A_194,B_195) = B_195 ) ),
    inference(resolution,[status(thm)],[c_1379,c_24])).

tff(c_28,plain,(
    ! [A_10,B_11,C_12] :
      ( r2_hidden('#skF_2'(A_10,B_11,C_12),A_10)
      | r2_hidden('#skF_3'(A_10,B_11,C_12),C_12)
      | k3_xboole_0(A_10,B_11) = C_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2195,plain,(
    ! [A_249,B_250,C_251] :
      ( r2_hidden('#skF_2'(A_249,B_250,C_251),A_249)
      | ~ r2_hidden('#skF_3'(A_249,B_250,C_251),B_250)
      | ~ r2_hidden('#skF_3'(A_249,B_250,C_251),A_249)
      | k3_xboole_0(A_249,B_250) = C_251 ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_6513,plain,(
    ! [A_399,C_400] :
      ( ~ r2_hidden('#skF_3'(A_399,C_400,C_400),A_399)
      | r2_hidden('#skF_2'(A_399,C_400,C_400),A_399)
      | k3_xboole_0(A_399,C_400) = C_400 ) ),
    inference(resolution,[status(thm)],[c_28,c_2195])).

tff(c_18,plain,(
    ! [A_10,B_11,C_12] :
      ( ~ r2_hidden('#skF_2'(A_10,B_11,C_12),C_12)
      | ~ r2_hidden('#skF_3'(A_10,B_11,C_12),B_11)
      | ~ r2_hidden('#skF_3'(A_10,B_11,C_12),A_10)
      | k3_xboole_0(A_10,B_11) = C_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_7561,plain,(
    ! [A_443] :
      ( ~ r2_hidden('#skF_3'(A_443,A_443,A_443),A_443)
      | k3_xboole_0(A_443,A_443) = A_443 ) ),
    inference(resolution,[status(thm)],[c_6513,c_18])).

tff(c_7592,plain,(
    ! [B_195] : k3_xboole_0(B_195,B_195) = B_195 ),
    inference(resolution,[status(thm)],[c_1462,c_7561])).

tff(c_46,plain,(
    ! [A_16,B_17,C_18] :
      ( r2_hidden('#skF_4'(A_16,B_17,C_18),A_16)
      | r2_hidden('#skF_5'(A_16,B_17,C_18),C_18)
      | k4_xboole_0(A_16,B_17) = C_18 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1126,plain,(
    ! [A_171,B_172,C_173] :
      ( ~ r2_hidden('#skF_4'(A_171,B_172,C_173),B_172)
      | r2_hidden('#skF_5'(A_171,B_172,C_173),C_173)
      | k4_xboole_0(A_171,B_172) = C_173 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1136,plain,(
    ! [A_16,C_18] :
      ( r2_hidden('#skF_5'(A_16,A_16,C_18),C_18)
      | k4_xboole_0(A_16,A_16) = C_18 ) ),
    inference(resolution,[status(thm)],[c_46,c_1126])).

tff(c_2468,plain,(
    ! [A_278,B_279,B_280] :
      ( r2_hidden('#skF_1'(k4_xboole_0(A_278,B_279),B_280),A_278)
      | r1_tarski(k4_xboole_0(A_278,B_279),B_280) ) ),
    inference(resolution,[status(thm)],[c_300,c_34])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_1'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2551,plain,(
    ! [A_281,B_282] : r1_tarski(k4_xboole_0(A_281,B_282),A_281) ),
    inference(resolution,[status(thm)],[c_2468,c_8])).

tff(c_2576,plain,(
    ! [A_281,B_282] :
      ( k4_xboole_0(A_281,B_282) = A_281
      | ~ r1_tarski(A_281,k4_xboole_0(A_281,B_282)) ) ),
    inference(resolution,[status(thm)],[c_2551,c_48])).

tff(c_2827,plain,(
    ! [A_293,B_294] : k4_xboole_0(k4_xboole_0(A_293,A_293),B_294) = k4_xboole_0(A_293,A_293) ),
    inference(resolution,[status(thm)],[c_2655,c_2576])).

tff(c_88,plain,(
    ! [B_42,A_41] :
      ( ~ r2_hidden(B_42,A_41)
      | k4_xboole_0(A_41,k1_tarski(B_42)) != A_41 ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_2956,plain,(
    ! [B_295,A_296] : ~ r2_hidden(B_295,k4_xboole_0(A_296,A_296)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2827,c_88])).

tff(c_3069,plain,(
    ! [A_298,A_297] : k4_xboole_0(A_298,A_298) = k4_xboole_0(A_297,A_297) ),
    inference(resolution,[status(thm)],[c_1136,c_2956])).

tff(c_56,plain,(
    ! [A_26,B_27] : k4_xboole_0(A_26,k4_xboole_0(A_26,B_27)) = k3_xboole_0(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_3154,plain,(
    ! [A_297,A_298] : k4_xboole_0(A_297,k4_xboole_0(A_298,A_298)) = k3_xboole_0(A_297,A_297) ),
    inference(superposition,[status(thm),theory(equality)],[c_3069,c_56])).

tff(c_7605,plain,(
    ! [A_297,A_298] : k4_xboole_0(A_297,k4_xboole_0(A_298,A_298)) = A_297 ),
    inference(demodulation,[status(thm),theory(equality)],[c_7592,c_3154])).

tff(c_14,plain,(
    ! [D_15,B_11,A_10] :
      ( r2_hidden(D_15,B_11)
      | ~ r2_hidden(D_15,k3_xboole_0(A_10,B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1818,plain,(
    ! [A_227,B_228,B_229] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_227,B_228),B_229),B_228)
      | r1_tarski(k3_xboole_0(A_227,B_228),B_229) ) ),
    inference(resolution,[status(thm)],[c_300,c_14])).

tff(c_1902,plain,(
    ! [A_234,B_235] : r1_tarski(k3_xboole_0(A_234,B_235),B_235) ),
    inference(resolution,[status(thm)],[c_1818,c_8])).

tff(c_1921,plain,(
    ! [A_234,B_235] :
      ( k3_xboole_0(A_234,B_235) = B_235
      | ~ r1_tarski(B_235,k3_xboole_0(A_234,B_235)) ) ),
    inference(resolution,[status(thm)],[c_1902,c_48])).

tff(c_3429,plain,(
    ! [A_317,A_318] : k3_xboole_0(A_317,k4_xboole_0(A_318,A_318)) = k4_xboole_0(A_318,A_318) ),
    inference(resolution,[status(thm)],[c_2655,c_1921])).

tff(c_54,plain,(
    ! [A_24,B_25] : k5_xboole_0(A_24,k3_xboole_0(A_24,B_25)) = k4_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_3487,plain,(
    ! [A_317,A_318] : k5_xboole_0(A_317,k4_xboole_0(A_318,A_318)) = k4_xboole_0(A_317,k4_xboole_0(A_318,A_318)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3429,c_54])).

tff(c_19731,plain,(
    ! [A_662,A_663] : k5_xboole_0(A_662,k4_xboole_0(A_663,A_663)) = A_662 ),
    inference(demodulation,[status(thm),theory(equality)],[c_7605,c_3487])).

tff(c_23658,plain,(
    ! [A_711,A_712,B_713] :
      ( k5_xboole_0(A_711,k3_xboole_0(A_712,k1_tarski(B_713))) = A_711
      | r2_hidden(B_713,A_712) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7015,c_19731])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_235,plain,(
    ! [A_86,B_87] : k5_xboole_0(A_86,k3_xboole_0(A_86,B_87)) = k4_xboole_0(A_86,B_87) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_244,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(B_4,A_3)) = k4_xboole_0(A_3,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_235])).

tff(c_23743,plain,(
    ! [B_714,A_715] :
      ( k4_xboole_0(k1_tarski(B_714),A_715) = k1_tarski(B_714)
      | r2_hidden(B_714,A_715) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_23658,c_244])).

tff(c_92,plain,
    ( k4_xboole_0(k1_tarski('#skF_8'),'#skF_9') != k1_tarski('#skF_8')
    | r2_hidden('#skF_10','#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_157,plain,(
    k4_xboole_0(k1_tarski('#skF_8'),'#skF_9') != k1_tarski('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_92])).

tff(c_24124,plain,(
    r2_hidden('#skF_8','#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_23743,c_157])).

tff(c_24290,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_24124])).

tff(c_24291,plain,(
    r2_hidden('#skF_10','#skF_11') ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_82,plain,(
    ! [A_35] : k2_tarski(A_35,A_35) = k1_tarski(A_35) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_24302,plain,(
    ! [A_722,B_723] : k1_enumset1(A_722,A_722,B_723) = k2_tarski(A_722,B_723) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_60,plain,(
    ! [E_34,A_28,B_29] : r2_hidden(E_34,k1_enumset1(A_28,B_29,E_34)) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_24326,plain,(
    ! [B_724,A_725] : r2_hidden(B_724,k2_tarski(A_725,B_724)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24302,c_60])).

tff(c_24331,plain,(
    ! [A_35] : r2_hidden(A_35,k1_tarski(A_35)) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_24326])).

tff(c_24292,plain,(
    k4_xboole_0(k1_tarski('#skF_8'),'#skF_9') = k1_tarski('#skF_8') ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_96,plain,
    ( k4_xboole_0(k1_tarski('#skF_8'),'#skF_9') != k1_tarski('#skF_8')
    | k4_xboole_0(k1_tarski('#skF_10'),'#skF_11') = k1_tarski('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_24339,plain,(
    k4_xboole_0(k1_tarski('#skF_10'),'#skF_11') = k1_tarski('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24292,c_96])).

tff(c_24361,plain,(
    ! [D_734,B_735,A_736] :
      ( ~ r2_hidden(D_734,B_735)
      | ~ r2_hidden(D_734,k4_xboole_0(A_736,B_735)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_24372,plain,(
    ! [D_740] :
      ( ~ r2_hidden(D_740,'#skF_11')
      | ~ r2_hidden(D_740,k1_tarski('#skF_10')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24339,c_24361])).

tff(c_24376,plain,(
    ~ r2_hidden('#skF_10','#skF_11') ),
    inference(resolution,[status(thm)],[c_24331,c_24372])).

tff(c_24380,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24291,c_24376])).

tff(c_24381,plain,(
    r2_hidden('#skF_10','#skF_11') ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_24445,plain,(
    ! [A_763,B_764] : k1_enumset1(A_763,A_763,B_764) = k2_tarski(A_763,B_764) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_24487,plain,(
    ! [B_767,A_768] : r2_hidden(B_767,k2_tarski(A_768,B_767)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24445,c_60])).

tff(c_24492,plain,(
    ! [A_35] : r2_hidden(A_35,k1_tarski(A_35)) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_24487])).

tff(c_24382,plain,(
    r2_hidden('#skF_8','#skF_9') ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_98,plain,
    ( ~ r2_hidden('#skF_8','#skF_9')
    | k4_xboole_0(k1_tarski('#skF_10'),'#skF_11') = k1_tarski('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_24437,plain,(
    k4_xboole_0(k1_tarski('#skF_10'),'#skF_11') = k1_tarski('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24382,c_98])).

tff(c_24531,plain,(
    ! [D_784,B_785,A_786] :
      ( ~ r2_hidden(D_784,B_785)
      | ~ r2_hidden(D_784,k4_xboole_0(A_786,B_785)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_24540,plain,(
    ! [D_787] :
      ( ~ r2_hidden(D_787,'#skF_11')
      | ~ r2_hidden(D_787,k1_tarski('#skF_10')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24437,c_24531])).

tff(c_24548,plain,(
    ~ r2_hidden('#skF_10','#skF_11') ),
    inference(resolution,[status(thm)],[c_24492,c_24540])).

tff(c_24553,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24381,c_24548])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:43:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.24/4.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.24/4.36  
% 11.24/4.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.24/4.36  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_11 > #skF_4 > #skF_10 > #skF_5 > #skF_2 > #skF_7 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_1
% 11.24/4.36  
% 11.24/4.36  %Foreground sorts:
% 11.24/4.36  
% 11.24/4.36  
% 11.24/4.36  %Background operators:
% 11.24/4.36  
% 11.24/4.36  
% 11.24/4.36  %Foreground operators:
% 11.24/4.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.24/4.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.24/4.36  tff('#skF_11', type, '#skF_11': $i).
% 11.24/4.36  tff(k1_tarski, type, k1_tarski: $i > $i).
% 11.24/4.36  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.24/4.36  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 11.24/4.36  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 11.24/4.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.24/4.36  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 11.24/4.36  tff('#skF_10', type, '#skF_10': $i).
% 11.24/4.36  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.24/4.36  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 11.24/4.36  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 11.24/4.36  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 11.24/4.36  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 11.24/4.36  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 11.24/4.36  tff('#skF_9', type, '#skF_9': $i).
% 11.24/4.36  tff('#skF_8', type, '#skF_8': $i).
% 11.24/4.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.24/4.36  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 11.24/4.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.24/4.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.24/4.36  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 11.24/4.36  
% 11.47/4.38  tff(f_100, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_zfmisc_1)).
% 11.47/4.38  tff(f_94, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 11.47/4.38  tff(f_68, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 11.47/4.38  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 11.47/4.38  tff(f_58, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 11.47/4.38  tff(f_64, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 11.47/4.38  tff(f_48, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 11.47/4.38  tff(f_66, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 11.47/4.38  tff(f_32, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 11.47/4.38  tff(f_85, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 11.47/4.38  tff(f_87, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 11.47/4.38  tff(f_83, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 11.47/4.38  tff(c_94, plain, (~r2_hidden('#skF_8', '#skF_9') | r2_hidden('#skF_10', '#skF_11')), inference(cnfTransformation, [status(thm)], [f_100])).
% 11.47/4.38  tff(c_110, plain, (~r2_hidden('#skF_8', '#skF_9')), inference(splitLeft, [status(thm)], [c_94])).
% 11.47/4.38  tff(c_90, plain, (![A_41, B_42]: (k4_xboole_0(A_41, k1_tarski(B_42))=A_41 | r2_hidden(B_42, A_41))), inference(cnfTransformation, [status(thm)], [f_94])).
% 11.47/4.38  tff(c_269, plain, (![A_99, B_100]: (k4_xboole_0(A_99, k4_xboole_0(A_99, B_100))=k3_xboole_0(A_99, B_100))), inference(cnfTransformation, [status(thm)], [f_68])).
% 11.47/4.38  tff(c_290, plain, (![A_41, B_42]: (k4_xboole_0(A_41, A_41)=k3_xboole_0(A_41, k1_tarski(B_42)) | r2_hidden(B_42, A_41))), inference(superposition, [status(thm), theory('equality')], [c_90, c_269])).
% 11.47/4.38  tff(c_300, plain, (![A_103, B_104]: (r2_hidden('#skF_1'(A_103, B_104), A_103) | r1_tarski(A_103, B_104))), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.47/4.38  tff(c_34, plain, (![D_21, A_16, B_17]: (r2_hidden(D_21, A_16) | ~r2_hidden(D_21, k4_xboole_0(A_16, B_17)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 11.47/4.38  tff(c_328, plain, (![A_16, B_17, B_104]: (r2_hidden('#skF_1'(k4_xboole_0(A_16, B_17), B_104), A_16) | r1_tarski(k4_xboole_0(A_16, B_17), B_104))), inference(resolution, [status(thm)], [c_300, c_34])).
% 11.47/4.38  tff(c_32, plain, (![D_21, B_17, A_16]: (~r2_hidden(D_21, B_17) | ~r2_hidden(D_21, k4_xboole_0(A_16, B_17)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 11.47/4.38  tff(c_2612, plain, (![A_285, B_286, B_287]: (~r2_hidden('#skF_1'(k4_xboole_0(A_285, B_286), B_287), B_286) | r1_tarski(k4_xboole_0(A_285, B_286), B_287))), inference(resolution, [status(thm)], [c_300, c_32])).
% 11.47/4.38  tff(c_2655, plain, (![A_288, B_289]: (r1_tarski(k4_xboole_0(A_288, A_288), B_289))), inference(resolution, [status(thm)], [c_328, c_2612])).
% 11.47/4.38  tff(c_6957, plain, (![A_419, B_420, B_421]: (r1_tarski(k3_xboole_0(A_419, k1_tarski(B_420)), B_421) | r2_hidden(B_420, A_419))), inference(superposition, [status(thm), theory('equality')], [c_290, c_2655])).
% 11.47/4.38  tff(c_48, plain, (![B_23, A_22]: (B_23=A_22 | ~r1_tarski(B_23, A_22) | ~r1_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_64])).
% 11.47/4.38  tff(c_2696, plain, (![A_288, B_289]: (k4_xboole_0(A_288, A_288)=B_289 | ~r1_tarski(B_289, k4_xboole_0(A_288, A_288)))), inference(resolution, [status(thm)], [c_2655, c_48])).
% 11.47/4.38  tff(c_7015, plain, (![A_288, A_419, B_420]: (k4_xboole_0(A_288, A_288)=k3_xboole_0(A_419, k1_tarski(B_420)) | r2_hidden(B_420, A_419))), inference(resolution, [status(thm)], [c_6957, c_2696])).
% 11.47/4.38  tff(c_1379, plain, (![A_194, B_195, C_196]: (r2_hidden('#skF_2'(A_194, B_195, C_196), B_195) | r2_hidden('#skF_3'(A_194, B_195, C_196), C_196) | k3_xboole_0(A_194, B_195)=C_196)), inference(cnfTransformation, [status(thm)], [f_48])).
% 11.47/4.38  tff(c_24, plain, (![A_10, B_11, C_12]: (~r2_hidden('#skF_2'(A_10, B_11, C_12), C_12) | r2_hidden('#skF_3'(A_10, B_11, C_12), C_12) | k3_xboole_0(A_10, B_11)=C_12)), inference(cnfTransformation, [status(thm)], [f_48])).
% 11.47/4.38  tff(c_1462, plain, (![A_194, B_195]: (r2_hidden('#skF_3'(A_194, B_195, B_195), B_195) | k3_xboole_0(A_194, B_195)=B_195)), inference(resolution, [status(thm)], [c_1379, c_24])).
% 11.47/4.38  tff(c_28, plain, (![A_10, B_11, C_12]: (r2_hidden('#skF_2'(A_10, B_11, C_12), A_10) | r2_hidden('#skF_3'(A_10, B_11, C_12), C_12) | k3_xboole_0(A_10, B_11)=C_12)), inference(cnfTransformation, [status(thm)], [f_48])).
% 11.47/4.38  tff(c_2195, plain, (![A_249, B_250, C_251]: (r2_hidden('#skF_2'(A_249, B_250, C_251), A_249) | ~r2_hidden('#skF_3'(A_249, B_250, C_251), B_250) | ~r2_hidden('#skF_3'(A_249, B_250, C_251), A_249) | k3_xboole_0(A_249, B_250)=C_251)), inference(cnfTransformation, [status(thm)], [f_48])).
% 11.47/4.38  tff(c_6513, plain, (![A_399, C_400]: (~r2_hidden('#skF_3'(A_399, C_400, C_400), A_399) | r2_hidden('#skF_2'(A_399, C_400, C_400), A_399) | k3_xboole_0(A_399, C_400)=C_400)), inference(resolution, [status(thm)], [c_28, c_2195])).
% 11.47/4.38  tff(c_18, plain, (![A_10, B_11, C_12]: (~r2_hidden('#skF_2'(A_10, B_11, C_12), C_12) | ~r2_hidden('#skF_3'(A_10, B_11, C_12), B_11) | ~r2_hidden('#skF_3'(A_10, B_11, C_12), A_10) | k3_xboole_0(A_10, B_11)=C_12)), inference(cnfTransformation, [status(thm)], [f_48])).
% 11.47/4.38  tff(c_7561, plain, (![A_443]: (~r2_hidden('#skF_3'(A_443, A_443, A_443), A_443) | k3_xboole_0(A_443, A_443)=A_443)), inference(resolution, [status(thm)], [c_6513, c_18])).
% 11.47/4.38  tff(c_7592, plain, (![B_195]: (k3_xboole_0(B_195, B_195)=B_195)), inference(resolution, [status(thm)], [c_1462, c_7561])).
% 11.47/4.38  tff(c_46, plain, (![A_16, B_17, C_18]: (r2_hidden('#skF_4'(A_16, B_17, C_18), A_16) | r2_hidden('#skF_5'(A_16, B_17, C_18), C_18) | k4_xboole_0(A_16, B_17)=C_18)), inference(cnfTransformation, [status(thm)], [f_58])).
% 11.47/4.38  tff(c_1126, plain, (![A_171, B_172, C_173]: (~r2_hidden('#skF_4'(A_171, B_172, C_173), B_172) | r2_hidden('#skF_5'(A_171, B_172, C_173), C_173) | k4_xboole_0(A_171, B_172)=C_173)), inference(cnfTransformation, [status(thm)], [f_58])).
% 11.47/4.38  tff(c_1136, plain, (![A_16, C_18]: (r2_hidden('#skF_5'(A_16, A_16, C_18), C_18) | k4_xboole_0(A_16, A_16)=C_18)), inference(resolution, [status(thm)], [c_46, c_1126])).
% 11.47/4.38  tff(c_2468, plain, (![A_278, B_279, B_280]: (r2_hidden('#skF_1'(k4_xboole_0(A_278, B_279), B_280), A_278) | r1_tarski(k4_xboole_0(A_278, B_279), B_280))), inference(resolution, [status(thm)], [c_300, c_34])).
% 11.47/4.38  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_1'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.47/4.38  tff(c_2551, plain, (![A_281, B_282]: (r1_tarski(k4_xboole_0(A_281, B_282), A_281))), inference(resolution, [status(thm)], [c_2468, c_8])).
% 11.47/4.38  tff(c_2576, plain, (![A_281, B_282]: (k4_xboole_0(A_281, B_282)=A_281 | ~r1_tarski(A_281, k4_xboole_0(A_281, B_282)))), inference(resolution, [status(thm)], [c_2551, c_48])).
% 11.47/4.38  tff(c_2827, plain, (![A_293, B_294]: (k4_xboole_0(k4_xboole_0(A_293, A_293), B_294)=k4_xboole_0(A_293, A_293))), inference(resolution, [status(thm)], [c_2655, c_2576])).
% 11.47/4.38  tff(c_88, plain, (![B_42, A_41]: (~r2_hidden(B_42, A_41) | k4_xboole_0(A_41, k1_tarski(B_42))!=A_41)), inference(cnfTransformation, [status(thm)], [f_94])).
% 11.47/4.38  tff(c_2956, plain, (![B_295, A_296]: (~r2_hidden(B_295, k4_xboole_0(A_296, A_296)))), inference(superposition, [status(thm), theory('equality')], [c_2827, c_88])).
% 11.47/4.38  tff(c_3069, plain, (![A_298, A_297]: (k4_xboole_0(A_298, A_298)=k4_xboole_0(A_297, A_297))), inference(resolution, [status(thm)], [c_1136, c_2956])).
% 11.47/4.38  tff(c_56, plain, (![A_26, B_27]: (k4_xboole_0(A_26, k4_xboole_0(A_26, B_27))=k3_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_68])).
% 11.47/4.38  tff(c_3154, plain, (![A_297, A_298]: (k4_xboole_0(A_297, k4_xboole_0(A_298, A_298))=k3_xboole_0(A_297, A_297))), inference(superposition, [status(thm), theory('equality')], [c_3069, c_56])).
% 11.47/4.38  tff(c_7605, plain, (![A_297, A_298]: (k4_xboole_0(A_297, k4_xboole_0(A_298, A_298))=A_297)), inference(demodulation, [status(thm), theory('equality')], [c_7592, c_3154])).
% 11.47/4.38  tff(c_14, plain, (![D_15, B_11, A_10]: (r2_hidden(D_15, B_11) | ~r2_hidden(D_15, k3_xboole_0(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 11.47/4.38  tff(c_1818, plain, (![A_227, B_228, B_229]: (r2_hidden('#skF_1'(k3_xboole_0(A_227, B_228), B_229), B_228) | r1_tarski(k3_xboole_0(A_227, B_228), B_229))), inference(resolution, [status(thm)], [c_300, c_14])).
% 11.47/4.38  tff(c_1902, plain, (![A_234, B_235]: (r1_tarski(k3_xboole_0(A_234, B_235), B_235))), inference(resolution, [status(thm)], [c_1818, c_8])).
% 11.47/4.38  tff(c_1921, plain, (![A_234, B_235]: (k3_xboole_0(A_234, B_235)=B_235 | ~r1_tarski(B_235, k3_xboole_0(A_234, B_235)))), inference(resolution, [status(thm)], [c_1902, c_48])).
% 11.47/4.38  tff(c_3429, plain, (![A_317, A_318]: (k3_xboole_0(A_317, k4_xboole_0(A_318, A_318))=k4_xboole_0(A_318, A_318))), inference(resolution, [status(thm)], [c_2655, c_1921])).
% 11.47/4.38  tff(c_54, plain, (![A_24, B_25]: (k5_xboole_0(A_24, k3_xboole_0(A_24, B_25))=k4_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_66])).
% 11.47/4.38  tff(c_3487, plain, (![A_317, A_318]: (k5_xboole_0(A_317, k4_xboole_0(A_318, A_318))=k4_xboole_0(A_317, k4_xboole_0(A_318, A_318)))), inference(superposition, [status(thm), theory('equality')], [c_3429, c_54])).
% 11.47/4.38  tff(c_19731, plain, (![A_662, A_663]: (k5_xboole_0(A_662, k4_xboole_0(A_663, A_663))=A_662)), inference(demodulation, [status(thm), theory('equality')], [c_7605, c_3487])).
% 11.47/4.38  tff(c_23658, plain, (![A_711, A_712, B_713]: (k5_xboole_0(A_711, k3_xboole_0(A_712, k1_tarski(B_713)))=A_711 | r2_hidden(B_713, A_712))), inference(superposition, [status(thm), theory('equality')], [c_7015, c_19731])).
% 11.47/4.38  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.47/4.38  tff(c_235, plain, (![A_86, B_87]: (k5_xboole_0(A_86, k3_xboole_0(A_86, B_87))=k4_xboole_0(A_86, B_87))), inference(cnfTransformation, [status(thm)], [f_66])).
% 11.47/4.38  tff(c_244, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(B_4, A_3))=k4_xboole_0(A_3, B_4))), inference(superposition, [status(thm), theory('equality')], [c_4, c_235])).
% 11.47/4.38  tff(c_23743, plain, (![B_714, A_715]: (k4_xboole_0(k1_tarski(B_714), A_715)=k1_tarski(B_714) | r2_hidden(B_714, A_715))), inference(superposition, [status(thm), theory('equality')], [c_23658, c_244])).
% 11.47/4.38  tff(c_92, plain, (k4_xboole_0(k1_tarski('#skF_8'), '#skF_9')!=k1_tarski('#skF_8') | r2_hidden('#skF_10', '#skF_11')), inference(cnfTransformation, [status(thm)], [f_100])).
% 11.47/4.38  tff(c_157, plain, (k4_xboole_0(k1_tarski('#skF_8'), '#skF_9')!=k1_tarski('#skF_8')), inference(splitLeft, [status(thm)], [c_92])).
% 11.47/4.38  tff(c_24124, plain, (r2_hidden('#skF_8', '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_23743, c_157])).
% 11.47/4.38  tff(c_24290, plain, $false, inference(negUnitSimplification, [status(thm)], [c_110, c_24124])).
% 11.47/4.38  tff(c_24291, plain, (r2_hidden('#skF_10', '#skF_11')), inference(splitRight, [status(thm)], [c_92])).
% 11.47/4.38  tff(c_82, plain, (![A_35]: (k2_tarski(A_35, A_35)=k1_tarski(A_35))), inference(cnfTransformation, [status(thm)], [f_85])).
% 11.47/4.38  tff(c_24302, plain, (![A_722, B_723]: (k1_enumset1(A_722, A_722, B_723)=k2_tarski(A_722, B_723))), inference(cnfTransformation, [status(thm)], [f_87])).
% 11.47/4.38  tff(c_60, plain, (![E_34, A_28, B_29]: (r2_hidden(E_34, k1_enumset1(A_28, B_29, E_34)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 11.47/4.38  tff(c_24326, plain, (![B_724, A_725]: (r2_hidden(B_724, k2_tarski(A_725, B_724)))), inference(superposition, [status(thm), theory('equality')], [c_24302, c_60])).
% 11.47/4.38  tff(c_24331, plain, (![A_35]: (r2_hidden(A_35, k1_tarski(A_35)))), inference(superposition, [status(thm), theory('equality')], [c_82, c_24326])).
% 11.47/4.38  tff(c_24292, plain, (k4_xboole_0(k1_tarski('#skF_8'), '#skF_9')=k1_tarski('#skF_8')), inference(splitRight, [status(thm)], [c_92])).
% 11.47/4.38  tff(c_96, plain, (k4_xboole_0(k1_tarski('#skF_8'), '#skF_9')!=k1_tarski('#skF_8') | k4_xboole_0(k1_tarski('#skF_10'), '#skF_11')=k1_tarski('#skF_10')), inference(cnfTransformation, [status(thm)], [f_100])).
% 11.47/4.38  tff(c_24339, plain, (k4_xboole_0(k1_tarski('#skF_10'), '#skF_11')=k1_tarski('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_24292, c_96])).
% 11.47/4.38  tff(c_24361, plain, (![D_734, B_735, A_736]: (~r2_hidden(D_734, B_735) | ~r2_hidden(D_734, k4_xboole_0(A_736, B_735)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 11.47/4.38  tff(c_24372, plain, (![D_740]: (~r2_hidden(D_740, '#skF_11') | ~r2_hidden(D_740, k1_tarski('#skF_10')))), inference(superposition, [status(thm), theory('equality')], [c_24339, c_24361])).
% 11.47/4.38  tff(c_24376, plain, (~r2_hidden('#skF_10', '#skF_11')), inference(resolution, [status(thm)], [c_24331, c_24372])).
% 11.47/4.38  tff(c_24380, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24291, c_24376])).
% 11.47/4.38  tff(c_24381, plain, (r2_hidden('#skF_10', '#skF_11')), inference(splitRight, [status(thm)], [c_94])).
% 11.47/4.38  tff(c_24445, plain, (![A_763, B_764]: (k1_enumset1(A_763, A_763, B_764)=k2_tarski(A_763, B_764))), inference(cnfTransformation, [status(thm)], [f_87])).
% 11.47/4.38  tff(c_24487, plain, (![B_767, A_768]: (r2_hidden(B_767, k2_tarski(A_768, B_767)))), inference(superposition, [status(thm), theory('equality')], [c_24445, c_60])).
% 11.47/4.38  tff(c_24492, plain, (![A_35]: (r2_hidden(A_35, k1_tarski(A_35)))), inference(superposition, [status(thm), theory('equality')], [c_82, c_24487])).
% 11.47/4.38  tff(c_24382, plain, (r2_hidden('#skF_8', '#skF_9')), inference(splitRight, [status(thm)], [c_94])).
% 11.47/4.38  tff(c_98, plain, (~r2_hidden('#skF_8', '#skF_9') | k4_xboole_0(k1_tarski('#skF_10'), '#skF_11')=k1_tarski('#skF_10')), inference(cnfTransformation, [status(thm)], [f_100])).
% 11.47/4.38  tff(c_24437, plain, (k4_xboole_0(k1_tarski('#skF_10'), '#skF_11')=k1_tarski('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_24382, c_98])).
% 11.47/4.38  tff(c_24531, plain, (![D_784, B_785, A_786]: (~r2_hidden(D_784, B_785) | ~r2_hidden(D_784, k4_xboole_0(A_786, B_785)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 11.47/4.38  tff(c_24540, plain, (![D_787]: (~r2_hidden(D_787, '#skF_11') | ~r2_hidden(D_787, k1_tarski('#skF_10')))), inference(superposition, [status(thm), theory('equality')], [c_24437, c_24531])).
% 11.47/4.38  tff(c_24548, plain, (~r2_hidden('#skF_10', '#skF_11')), inference(resolution, [status(thm)], [c_24492, c_24540])).
% 11.47/4.38  tff(c_24553, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24381, c_24548])).
% 11.47/4.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.47/4.38  
% 11.47/4.38  Inference rules
% 11.47/4.38  ----------------------
% 11.47/4.38  #Ref     : 0
% 11.47/4.38  #Sup     : 6006
% 11.47/4.38  #Fact    : 0
% 11.47/4.38  #Define  : 0
% 11.47/4.38  #Split   : 3
% 11.47/4.38  #Chain   : 0
% 11.47/4.38  #Close   : 0
% 11.47/4.38  
% 11.47/4.38  Ordering : KBO
% 11.47/4.38  
% 11.47/4.38  Simplification rules
% 11.47/4.38  ----------------------
% 11.47/4.38  #Subsume      : 1574
% 11.47/4.38  #Demod        : 1564
% 11.47/4.38  #Tautology    : 1266
% 11.47/4.38  #SimpNegUnit  : 402
% 11.47/4.38  #BackRed      : 14
% 11.47/4.38  
% 11.47/4.38  #Partial instantiations: 0
% 11.47/4.38  #Strategies tried      : 1
% 11.47/4.38  
% 11.47/4.38  Timing (in seconds)
% 11.47/4.38  ----------------------
% 11.47/4.39  Preprocessing        : 0.35
% 11.47/4.39  Parsing              : 0.18
% 11.47/4.39  CNF conversion       : 0.03
% 11.47/4.39  Main loop            : 3.21
% 11.47/4.39  Inferencing          : 0.76
% 11.47/4.39  Reduction            : 1.23
% 11.47/4.39  Demodulation         : 0.90
% 11.47/4.39  BG Simplification    : 0.11
% 11.47/4.39  Subsumption          : 0.88
% 11.47/4.39  Abstraction          : 0.15
% 11.47/4.39  MUC search           : 0.00
% 11.47/4.39  Cooper               : 0.00
% 11.47/4.39  Total                : 3.60
% 11.47/4.39  Index Insertion      : 0.00
% 11.47/4.39  Index Deletion       : 0.00
% 11.47/4.39  Index Matching       : 0.00
% 11.47/4.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
