%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:15 EST 2020

% Result     : Theorem 3.74s
% Output     : CNFRefutation 3.74s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 232 expanded)
%              Number of leaves         :   42 (  93 expanded)
%              Depth                    :   11
%              Number of atoms          :  133 ( 397 expanded)
%              Number of equality atoms :   86 ( 345 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_125,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_78,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_104,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_76,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_82,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_80,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_84,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_74,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_62,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_72,axiom,(
    ! [A,B] :
      ~ ( r2_xboole_0(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ~ r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_0)).

tff(c_66,plain,
    ( k1_tarski('#skF_4') != '#skF_6'
    | k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_127,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_64,plain,
    ( k1_xboole_0 != '#skF_6'
    | k1_tarski('#skF_4') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_133,plain,(
    k1_tarski('#skF_4') != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_70,plain,(
    k2_xboole_0('#skF_5','#skF_6') = k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_134,plain,(
    ! [A_76,B_77] : r1_tarski(A_76,k2_xboole_0(A_76,B_77)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_137,plain,(
    r1_tarski('#skF_5',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_134])).

tff(c_399,plain,(
    ! [B_122,A_123] :
      ( k1_tarski(B_122) = A_123
      | k1_xboole_0 = A_123
      | ~ r1_tarski(A_123,k1_tarski(B_122)) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_402,plain,
    ( k1_tarski('#skF_4') = '#skF_5'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_137,c_399])).

tff(c_417,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_127,c_133,c_402])).

tff(c_418,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_419,plain,(
    k1_tarski('#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_68,plain,
    ( k1_tarski('#skF_4') != '#skF_6'
    | k1_tarski('#skF_4') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_436,plain,(
    '#skF_5' != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_419,c_419,c_68])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_459,plain,(
    ! [B_131,A_132] : k5_xboole_0(B_131,A_132) = k5_xboole_0(A_132,B_131) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_32,plain,(
    ! [A_25] : k5_xboole_0(A_25,k1_xboole_0) = A_25 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_475,plain,(
    ! [A_132] : k5_xboole_0(k1_xboole_0,A_132) = A_132 ),
    inference(superposition,[status(thm),theory(equality)],[c_459,c_32])).

tff(c_38,plain,(
    ! [A_31] : k5_xboole_0(A_31,A_31) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1056,plain,(
    ! [A_194,B_195,C_196] : k5_xboole_0(k5_xboole_0(A_194,B_195),C_196) = k5_xboole_0(A_194,k5_xboole_0(B_195,C_196)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1150,plain,(
    ! [A_31,C_196] : k5_xboole_0(A_31,k5_xboole_0(A_31,C_196)) = k5_xboole_0(k1_xboole_0,C_196) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_1056])).

tff(c_1166,plain,(
    ! [A_197,C_198] : k5_xboole_0(A_197,k5_xboole_0(A_197,C_198)) = C_198 ),
    inference(demodulation,[status(thm),theory(equality)],[c_475,c_1150])).

tff(c_1224,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k5_xboole_0(B_2,A_1)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1166])).

tff(c_420,plain,(
    k2_xboole_0('#skF_5','#skF_6') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_419,c_70])).

tff(c_920,plain,(
    ! [A_190,B_191] : k5_xboole_0(k5_xboole_0(A_190,B_191),k2_xboole_0(A_190,B_191)) = k3_xboole_0(A_190,B_191) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_956,plain,(
    k5_xboole_0(k5_xboole_0('#skF_5','#skF_6'),'#skF_5') = k3_xboole_0('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_420,c_920])).

tff(c_969,plain,(
    k5_xboole_0('#skF_5',k5_xboole_0('#skF_6','#skF_5')) = k3_xboole_0('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_956])).

tff(c_1345,plain,(
    k3_xboole_0('#skF_5','#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1224,c_969])).

tff(c_30,plain,(
    ! [A_23,B_24] : r1_tarski(k3_xboole_0(A_23,B_24),A_23) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_676,plain,(
    ! [B_164,A_165] :
      ( k1_tarski(B_164) = A_165
      | k1_xboole_0 = A_165
      | ~ r1_tarski(A_165,k1_tarski(B_164)) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_687,plain,(
    ! [A_165] :
      ( k1_tarski('#skF_4') = A_165
      | k1_xboole_0 = A_165
      | ~ r1_tarski(A_165,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_419,c_676])).

tff(c_704,plain,(
    ! [A_167] :
      ( A_167 = '#skF_5'
      | k1_xboole_0 = A_167
      | ~ r1_tarski(A_167,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_419,c_687])).

tff(c_716,plain,(
    ! [B_24] :
      ( k3_xboole_0('#skF_5',B_24) = '#skF_5'
      | k3_xboole_0('#skF_5',B_24) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_30,c_704])).

tff(c_1444,plain,
    ( k3_xboole_0('#skF_5','#skF_6') = '#skF_5'
    | k1_xboole_0 = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_1345,c_716])).

tff(c_1465,plain,
    ( '#skF_5' = '#skF_6'
    | k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1345,c_1444])).

tff(c_1467,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_418,c_436,c_1465])).

tff(c_1468,plain,(
    k1_tarski('#skF_4') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_1526,plain,(
    ! [B_218,A_219] : k5_xboole_0(B_218,A_219) = k5_xboole_0(A_219,B_218) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1469,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_1472,plain,(
    ! [A_25] : k5_xboole_0(A_25,'#skF_5') = A_25 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1469,c_32])).

tff(c_1542,plain,(
    ! [A_219] : k5_xboole_0('#skF_5',A_219) = A_219 ),
    inference(superposition,[status(thm),theory(equality)],[c_1526,c_1472])).

tff(c_6,plain,(
    ! [A_3] :
      ( v1_xboole_0(A_3)
      | r2_hidden('#skF_1'(A_3),A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_20,plain,(
    ! [A_13] : k3_xboole_0(A_13,A_13) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( r1_xboole_0(A_7,B_8)
      | k3_xboole_0(A_7,B_8) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1661,plain,(
    ! [A_7,B_8] :
      ( r1_xboole_0(A_7,B_8)
      | k3_xboole_0(A_7,B_8) != '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1469,c_10])).

tff(c_1716,plain,(
    ! [A_244,B_245,C_246] :
      ( ~ r1_xboole_0(A_244,B_245)
      | ~ r2_hidden(C_246,k3_xboole_0(A_244,B_245)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1730,plain,(
    ! [A_247,C_248] :
      ( ~ r1_xboole_0(A_247,A_247)
      | ~ r2_hidden(C_248,A_247) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_1716])).

tff(c_1733,plain,(
    ! [C_248,B_8] :
      ( ~ r2_hidden(C_248,B_8)
      | k3_xboole_0(B_8,B_8) != '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_1661,c_1730])).

tff(c_1737,plain,(
    ! [C_249,B_250] :
      ( ~ r2_hidden(C_249,B_250)
      | B_250 != '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1733])).

tff(c_1747,plain,(
    ! [A_251] :
      ( A_251 != '#skF_5'
      | v1_xboole_0(A_251) ) ),
    inference(resolution,[status(thm)],[c_6,c_1737])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( r2_xboole_0(A_9,B_10)
      | B_10 = A_9
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1667,plain,(
    ! [A_231,B_232] :
      ( r2_hidden('#skF_3'(A_231,B_232),B_232)
      | ~ r2_xboole_0(A_231,B_232) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_4,plain,(
    ! [B_6,A_3] :
      ( ~ r2_hidden(B_6,A_3)
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1685,plain,(
    ! [B_235,A_236] :
      ( ~ v1_xboole_0(B_235)
      | ~ r2_xboole_0(A_236,B_235) ) ),
    inference(resolution,[status(thm)],[c_1667,c_4])).

tff(c_1690,plain,(
    ! [B_237,A_238] :
      ( ~ v1_xboole_0(B_237)
      | B_237 = A_238
      | ~ r1_tarski(A_238,B_237) ) ),
    inference(resolution,[status(thm)],[c_12,c_1685])).

tff(c_1703,plain,(
    ! [A_23,B_24] :
      ( ~ v1_xboole_0(A_23)
      | k3_xboole_0(A_23,B_24) = A_23 ) ),
    inference(resolution,[status(thm)],[c_30,c_1690])).

tff(c_1779,plain,(
    ! [B_24] : k3_xboole_0('#skF_5',B_24) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_1747,c_1703])).

tff(c_2243,plain,(
    ! [A_288,B_289] : k5_xboole_0(k5_xboole_0(A_288,B_289),k2_xboole_0(A_288,B_289)) = k3_xboole_0(A_288,B_289) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2310,plain,(
    k5_xboole_0(k5_xboole_0('#skF_5','#skF_6'),k1_tarski('#skF_4')) = k3_xboole_0('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_2243])).

tff(c_2323,plain,(
    k5_xboole_0('#skF_6',k1_tarski('#skF_4')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1779,c_1472,c_2,c_2310])).

tff(c_1473,plain,(
    ! [A_31] : k5_xboole_0(A_31,A_31) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1469,c_38])).

tff(c_1936,plain,(
    ! [A_278,B_279,C_280] : k5_xboole_0(k5_xboole_0(A_278,B_279),C_280) = k5_xboole_0(A_278,k5_xboole_0(B_279,C_280)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1982,plain,(
    ! [A_31,C_280] : k5_xboole_0(A_31,k5_xboole_0(A_31,C_280)) = k5_xboole_0('#skF_5',C_280) ),
    inference(superposition,[status(thm),theory(equality)],[c_1473,c_1936])).

tff(c_2012,plain,(
    ! [A_282,C_283] : k5_xboole_0(A_282,k5_xboole_0(A_282,C_283)) = C_283 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1542,c_1982])).

tff(c_2074,plain,(
    ! [A_284,B_285] : k5_xboole_0(A_284,k5_xboole_0(B_285,A_284)) = B_285 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2012])).

tff(c_2052,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k5_xboole_0(B_2,A_1)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2012])).

tff(c_2077,plain,(
    ! [B_285,A_284] : k5_xboole_0(k5_xboole_0(B_285,A_284),B_285) = A_284 ),
    inference(superposition,[status(thm),theory(equality)],[c_2074,c_2052])).

tff(c_2332,plain,(
    k5_xboole_0('#skF_5','#skF_6') = k1_tarski('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2323,c_2077])).

tff(c_2345,plain,(
    k1_tarski('#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1542,c_2332])).

tff(c_2347,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1468,c_2345])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:30:50 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.74/1.63  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.74/1.64  
% 3.74/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.74/1.64  %$ r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 3.74/1.64  
% 3.74/1.64  %Foreground sorts:
% 3.74/1.64  
% 3.74/1.64  
% 3.74/1.64  %Background operators:
% 3.74/1.64  
% 3.74/1.64  
% 3.74/1.64  %Foreground operators:
% 3.74/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.74/1.64  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.74/1.64  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.74/1.64  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.74/1.64  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.74/1.64  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.74/1.64  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.74/1.64  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.74/1.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.74/1.64  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.74/1.64  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.74/1.64  tff('#skF_5', type, '#skF_5': $i).
% 3.74/1.64  tff('#skF_6', type, '#skF_6': $i).
% 3.74/1.64  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.74/1.64  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.74/1.64  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.74/1.64  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 3.74/1.64  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.74/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.74/1.64  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.74/1.64  tff('#skF_4', type, '#skF_4': $i).
% 3.74/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.74/1.64  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.74/1.64  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.74/1.64  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.74/1.64  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.74/1.64  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.74/1.64  
% 3.74/1.66  tff(f_125, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 3.74/1.66  tff(f_78, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.74/1.66  tff(f_104, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 3.74/1.66  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 3.74/1.66  tff(f_76, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 3.74/1.66  tff(f_82, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.74/1.66  tff(f_80, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 3.74/1.66  tff(f_84, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 3.74/1.66  tff(f_74, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.74/1.66  tff(f_33, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.74/1.66  tff(f_48, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 3.74/1.66  tff(f_37, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.74/1.66  tff(f_62, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.74/1.66  tff(f_44, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 3.74/1.66  tff(f_72, axiom, (![A, B]: ~(r2_xboole_0(A, B) & (![C]: ~(r2_hidden(C, B) & ~r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_xboole_0)).
% 3.74/1.66  tff(c_66, plain, (k1_tarski('#skF_4')!='#skF_6' | k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.74/1.66  tff(c_127, plain, (k1_xboole_0!='#skF_5'), inference(splitLeft, [status(thm)], [c_66])).
% 3.74/1.66  tff(c_64, plain, (k1_xboole_0!='#skF_6' | k1_tarski('#skF_4')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.74/1.66  tff(c_133, plain, (k1_tarski('#skF_4')!='#skF_5'), inference(splitLeft, [status(thm)], [c_64])).
% 3.74/1.66  tff(c_70, plain, (k2_xboole_0('#skF_5', '#skF_6')=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.74/1.66  tff(c_134, plain, (![A_76, B_77]: (r1_tarski(A_76, k2_xboole_0(A_76, B_77)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.74/1.66  tff(c_137, plain, (r1_tarski('#skF_5', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_70, c_134])).
% 3.74/1.66  tff(c_399, plain, (![B_122, A_123]: (k1_tarski(B_122)=A_123 | k1_xboole_0=A_123 | ~r1_tarski(A_123, k1_tarski(B_122)))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.74/1.66  tff(c_402, plain, (k1_tarski('#skF_4')='#skF_5' | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_137, c_399])).
% 3.74/1.66  tff(c_417, plain, $false, inference(negUnitSimplification, [status(thm)], [c_127, c_133, c_402])).
% 3.74/1.66  tff(c_418, plain, (k1_xboole_0!='#skF_6'), inference(splitRight, [status(thm)], [c_64])).
% 3.74/1.66  tff(c_419, plain, (k1_tarski('#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_64])).
% 3.74/1.66  tff(c_68, plain, (k1_tarski('#skF_4')!='#skF_6' | k1_tarski('#skF_4')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.74/1.66  tff(c_436, plain, ('#skF_5'!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_419, c_419, c_68])).
% 3.74/1.66  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.74/1.66  tff(c_459, plain, (![B_131, A_132]: (k5_xboole_0(B_131, A_132)=k5_xboole_0(A_132, B_131))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.74/1.66  tff(c_32, plain, (![A_25]: (k5_xboole_0(A_25, k1_xboole_0)=A_25)), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.74/1.66  tff(c_475, plain, (![A_132]: (k5_xboole_0(k1_xboole_0, A_132)=A_132)), inference(superposition, [status(thm), theory('equality')], [c_459, c_32])).
% 3.74/1.66  tff(c_38, plain, (![A_31]: (k5_xboole_0(A_31, A_31)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.74/1.66  tff(c_1056, plain, (![A_194, B_195, C_196]: (k5_xboole_0(k5_xboole_0(A_194, B_195), C_196)=k5_xboole_0(A_194, k5_xboole_0(B_195, C_196)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.74/1.66  tff(c_1150, plain, (![A_31, C_196]: (k5_xboole_0(A_31, k5_xboole_0(A_31, C_196))=k5_xboole_0(k1_xboole_0, C_196))), inference(superposition, [status(thm), theory('equality')], [c_38, c_1056])).
% 3.74/1.66  tff(c_1166, plain, (![A_197, C_198]: (k5_xboole_0(A_197, k5_xboole_0(A_197, C_198))=C_198)), inference(demodulation, [status(thm), theory('equality')], [c_475, c_1150])).
% 3.74/1.66  tff(c_1224, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k5_xboole_0(B_2, A_1))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_1166])).
% 3.74/1.66  tff(c_420, plain, (k2_xboole_0('#skF_5', '#skF_6')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_419, c_70])).
% 3.74/1.66  tff(c_920, plain, (![A_190, B_191]: (k5_xboole_0(k5_xboole_0(A_190, B_191), k2_xboole_0(A_190, B_191))=k3_xboole_0(A_190, B_191))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.74/1.66  tff(c_956, plain, (k5_xboole_0(k5_xboole_0('#skF_5', '#skF_6'), '#skF_5')=k3_xboole_0('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_420, c_920])).
% 3.74/1.66  tff(c_969, plain, (k5_xboole_0('#skF_5', k5_xboole_0('#skF_6', '#skF_5'))=k3_xboole_0('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2, c_956])).
% 3.74/1.66  tff(c_1345, plain, (k3_xboole_0('#skF_5', '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1224, c_969])).
% 3.74/1.66  tff(c_30, plain, (![A_23, B_24]: (r1_tarski(k3_xboole_0(A_23, B_24), A_23))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.74/1.66  tff(c_676, plain, (![B_164, A_165]: (k1_tarski(B_164)=A_165 | k1_xboole_0=A_165 | ~r1_tarski(A_165, k1_tarski(B_164)))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.74/1.66  tff(c_687, plain, (![A_165]: (k1_tarski('#skF_4')=A_165 | k1_xboole_0=A_165 | ~r1_tarski(A_165, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_419, c_676])).
% 3.74/1.66  tff(c_704, plain, (![A_167]: (A_167='#skF_5' | k1_xboole_0=A_167 | ~r1_tarski(A_167, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_419, c_687])).
% 3.74/1.66  tff(c_716, plain, (![B_24]: (k3_xboole_0('#skF_5', B_24)='#skF_5' | k3_xboole_0('#skF_5', B_24)=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_704])).
% 3.74/1.66  tff(c_1444, plain, (k3_xboole_0('#skF_5', '#skF_6')='#skF_5' | k1_xboole_0='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_1345, c_716])).
% 3.74/1.66  tff(c_1465, plain, ('#skF_5'='#skF_6' | k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1345, c_1444])).
% 3.74/1.66  tff(c_1467, plain, $false, inference(negUnitSimplification, [status(thm)], [c_418, c_436, c_1465])).
% 3.74/1.66  tff(c_1468, plain, (k1_tarski('#skF_4')!='#skF_6'), inference(splitRight, [status(thm)], [c_66])).
% 3.74/1.66  tff(c_1526, plain, (![B_218, A_219]: (k5_xboole_0(B_218, A_219)=k5_xboole_0(A_219, B_218))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.74/1.66  tff(c_1469, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_66])).
% 3.74/1.66  tff(c_1472, plain, (![A_25]: (k5_xboole_0(A_25, '#skF_5')=A_25)), inference(demodulation, [status(thm), theory('equality')], [c_1469, c_32])).
% 3.74/1.66  tff(c_1542, plain, (![A_219]: (k5_xboole_0('#skF_5', A_219)=A_219)), inference(superposition, [status(thm), theory('equality')], [c_1526, c_1472])).
% 3.74/1.66  tff(c_6, plain, (![A_3]: (v1_xboole_0(A_3) | r2_hidden('#skF_1'(A_3), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.74/1.66  tff(c_20, plain, (![A_13]: (k3_xboole_0(A_13, A_13)=A_13)), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.74/1.66  tff(c_10, plain, (![A_7, B_8]: (r1_xboole_0(A_7, B_8) | k3_xboole_0(A_7, B_8)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.74/1.66  tff(c_1661, plain, (![A_7, B_8]: (r1_xboole_0(A_7, B_8) | k3_xboole_0(A_7, B_8)!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1469, c_10])).
% 3.74/1.66  tff(c_1716, plain, (![A_244, B_245, C_246]: (~r1_xboole_0(A_244, B_245) | ~r2_hidden(C_246, k3_xboole_0(A_244, B_245)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.74/1.66  tff(c_1730, plain, (![A_247, C_248]: (~r1_xboole_0(A_247, A_247) | ~r2_hidden(C_248, A_247))), inference(superposition, [status(thm), theory('equality')], [c_20, c_1716])).
% 3.74/1.66  tff(c_1733, plain, (![C_248, B_8]: (~r2_hidden(C_248, B_8) | k3_xboole_0(B_8, B_8)!='#skF_5')), inference(resolution, [status(thm)], [c_1661, c_1730])).
% 3.74/1.66  tff(c_1737, plain, (![C_249, B_250]: (~r2_hidden(C_249, B_250) | B_250!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1733])).
% 3.74/1.66  tff(c_1747, plain, (![A_251]: (A_251!='#skF_5' | v1_xboole_0(A_251))), inference(resolution, [status(thm)], [c_6, c_1737])).
% 3.74/1.66  tff(c_12, plain, (![A_9, B_10]: (r2_xboole_0(A_9, B_10) | B_10=A_9 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.74/1.66  tff(c_1667, plain, (![A_231, B_232]: (r2_hidden('#skF_3'(A_231, B_232), B_232) | ~r2_xboole_0(A_231, B_232))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.74/1.66  tff(c_4, plain, (![B_6, A_3]: (~r2_hidden(B_6, A_3) | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.74/1.66  tff(c_1685, plain, (![B_235, A_236]: (~v1_xboole_0(B_235) | ~r2_xboole_0(A_236, B_235))), inference(resolution, [status(thm)], [c_1667, c_4])).
% 3.74/1.66  tff(c_1690, plain, (![B_237, A_238]: (~v1_xboole_0(B_237) | B_237=A_238 | ~r1_tarski(A_238, B_237))), inference(resolution, [status(thm)], [c_12, c_1685])).
% 3.74/1.66  tff(c_1703, plain, (![A_23, B_24]: (~v1_xboole_0(A_23) | k3_xboole_0(A_23, B_24)=A_23)), inference(resolution, [status(thm)], [c_30, c_1690])).
% 3.74/1.66  tff(c_1779, plain, (![B_24]: (k3_xboole_0('#skF_5', B_24)='#skF_5')), inference(resolution, [status(thm)], [c_1747, c_1703])).
% 3.74/1.66  tff(c_2243, plain, (![A_288, B_289]: (k5_xboole_0(k5_xboole_0(A_288, B_289), k2_xboole_0(A_288, B_289))=k3_xboole_0(A_288, B_289))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.74/1.66  tff(c_2310, plain, (k5_xboole_0(k5_xboole_0('#skF_5', '#skF_6'), k1_tarski('#skF_4'))=k3_xboole_0('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_70, c_2243])).
% 3.74/1.66  tff(c_2323, plain, (k5_xboole_0('#skF_6', k1_tarski('#skF_4'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1779, c_1472, c_2, c_2310])).
% 3.74/1.66  tff(c_1473, plain, (![A_31]: (k5_xboole_0(A_31, A_31)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1469, c_38])).
% 3.74/1.66  tff(c_1936, plain, (![A_278, B_279, C_280]: (k5_xboole_0(k5_xboole_0(A_278, B_279), C_280)=k5_xboole_0(A_278, k5_xboole_0(B_279, C_280)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.74/1.66  tff(c_1982, plain, (![A_31, C_280]: (k5_xboole_0(A_31, k5_xboole_0(A_31, C_280))=k5_xboole_0('#skF_5', C_280))), inference(superposition, [status(thm), theory('equality')], [c_1473, c_1936])).
% 3.74/1.66  tff(c_2012, plain, (![A_282, C_283]: (k5_xboole_0(A_282, k5_xboole_0(A_282, C_283))=C_283)), inference(demodulation, [status(thm), theory('equality')], [c_1542, c_1982])).
% 3.74/1.66  tff(c_2074, plain, (![A_284, B_285]: (k5_xboole_0(A_284, k5_xboole_0(B_285, A_284))=B_285)), inference(superposition, [status(thm), theory('equality')], [c_2, c_2012])).
% 3.74/1.66  tff(c_2052, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k5_xboole_0(B_2, A_1))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_2012])).
% 3.74/1.66  tff(c_2077, plain, (![B_285, A_284]: (k5_xboole_0(k5_xboole_0(B_285, A_284), B_285)=A_284)), inference(superposition, [status(thm), theory('equality')], [c_2074, c_2052])).
% 3.74/1.66  tff(c_2332, plain, (k5_xboole_0('#skF_5', '#skF_6')=k1_tarski('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2323, c_2077])).
% 3.74/1.66  tff(c_2345, plain, (k1_tarski('#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1542, c_2332])).
% 3.74/1.66  tff(c_2347, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1468, c_2345])).
% 3.74/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.74/1.66  
% 3.74/1.66  Inference rules
% 3.74/1.66  ----------------------
% 3.74/1.66  #Ref     : 0
% 3.74/1.66  #Sup     : 533
% 3.74/1.66  #Fact    : 1
% 3.74/1.66  #Define  : 0
% 3.74/1.66  #Split   : 3
% 3.74/1.66  #Chain   : 0
% 3.74/1.66  #Close   : 0
% 3.74/1.66  
% 3.74/1.66  Ordering : KBO
% 3.74/1.66  
% 3.74/1.66  Simplification rules
% 3.74/1.66  ----------------------
% 3.74/1.66  #Subsume      : 42
% 3.74/1.66  #Demod        : 192
% 3.74/1.66  #Tautology    : 294
% 3.74/1.66  #SimpNegUnit  : 16
% 3.74/1.66  #BackRed      : 7
% 3.74/1.66  
% 3.74/1.66  #Partial instantiations: 0
% 3.74/1.66  #Strategies tried      : 1
% 3.74/1.66  
% 3.74/1.66  Timing (in seconds)
% 3.74/1.66  ----------------------
% 3.74/1.67  Preprocessing        : 0.35
% 3.74/1.67  Parsing              : 0.19
% 3.74/1.67  CNF conversion       : 0.02
% 3.74/1.67  Main loop            : 0.54
% 3.74/1.67  Inferencing          : 0.19
% 3.74/1.67  Reduction            : 0.19
% 3.74/1.67  Demodulation         : 0.15
% 3.74/1.67  BG Simplification    : 0.03
% 3.74/1.67  Subsumption          : 0.08
% 3.74/1.67  Abstraction          : 0.02
% 3.74/1.67  MUC search           : 0.00
% 3.74/1.67  Cooper               : 0.00
% 3.74/1.67  Total                : 0.93
% 3.74/1.67  Index Insertion      : 0.00
% 3.74/1.67  Index Deletion       : 0.00
% 3.74/1.67  Index Matching       : 0.00
% 3.74/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
