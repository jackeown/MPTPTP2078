%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:15 EST 2020

% Result     : Theorem 3.75s
% Output     : CNFRefutation 3.75s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 194 expanded)
%              Number of leaves         :   46 (  85 expanded)
%              Depth                    :    9
%              Number of atoms          :  121 ( 270 expanded)
%              Number of equality atoms :   66 ( 184 expanded)
%              Maximal formula depth    :   24 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k7_enumset1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_3 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k7_enumset1,type,(
    k7_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_72,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_74,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_123,axiom,(
    ! [A,B,C,D,E,F,G] :
      ( G = k4_enumset1(A,B,C,D,E,F)
    <=> ! [H] :
          ( r2_hidden(H,G)
        <=> ~ ( H != A
              & H != B
              & H != C
              & H != D
              & H != E
              & H != F ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_enumset1)).

tff(f_66,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_68,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_70,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_64,axiom,(
    ! [A,B,C,D,E,F,G,H,I,J] :
      ( J = k7_enumset1(A,B,C,D,E,F,G,H,I)
    <=> ! [K] :
          ( r2_hidden(K,J)
        <=> ~ ( K != A
              & K != B
              & K != C
              & K != D
              & K != E
              & K != F
              & K != G
              & K != H
              & K != I ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_enumset1)).

tff(f_137,negated_conjecture,(
    ~ ! [A] :
        ( ? [B,C] : A = k4_tarski(B,C)
       => ( A != k1_mcart_1(A)
          & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_127,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_90,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_29,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_27,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_99,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_96,axiom,(
    ! [A,B] :
      ( ( r1_tarski(A,k2_zfmisc_1(A,B))
        | r1_tarski(A,k2_zfmisc_1(B,A)) )
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t135_zfmisc_1)).

tff(c_74,plain,(
    ! [A_24,B_25,C_26,D_27] : k3_enumset1(A_24,A_24,B_25,C_26,D_27) = k2_enumset1(A_24,B_25,C_26,D_27) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_783,plain,(
    ! [C_457,B_458,D_459,A_456,E_455] : k4_enumset1(A_456,A_456,B_458,C_457,D_459,E_455) = k3_enumset1(A_456,B_458,C_457,D_459,E_455) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_108,plain,(
    ! [B_59,A_58,F_63,E_62,H_67,D_61] : r2_hidden(H_67,k4_enumset1(A_58,B_59,H_67,D_61,E_62,F_63)) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_849,plain,(
    ! [C_482,B_480,A_479,D_483,E_481] : r2_hidden(B_480,k3_enumset1(A_479,B_480,C_482,D_483,E_481)) ),
    inference(superposition,[status(thm),theory(equality)],[c_783,c_108])).

tff(c_852,plain,(
    ! [A_24,B_25,C_26,D_27] : r2_hidden(A_24,k2_enumset1(A_24,B_25,C_26,D_27)) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_849])).

tff(c_68,plain,(
    ! [A_18] : k2_tarski(A_18,A_18) = k1_tarski(A_18) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_70,plain,(
    ! [A_19,B_20] : k1_enumset1(A_19,A_19,B_20) = k2_tarski(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_72,plain,(
    ! [A_21,B_22,C_23] : k2_enumset1(A_21,A_21,B_22,C_23) = k1_enumset1(A_21,B_22,C_23) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_106,plain,(
    ! [B_59,A_58,F_63,E_62,H_67,C_60] : r2_hidden(H_67,k4_enumset1(A_58,B_59,C_60,H_67,E_62,F_63)) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_810,plain,(
    ! [A_460,D_464,B_461,C_463,E_462] : r2_hidden(C_463,k3_enumset1(A_460,B_461,C_463,D_464,E_462)) ),
    inference(superposition,[status(thm),theory(equality)],[c_783,c_106])).

tff(c_814,plain,(
    ! [B_465,A_466,C_467,D_468] : r2_hidden(B_465,k2_enumset1(A_466,B_465,C_467,D_468)) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_810])).

tff(c_818,plain,(
    ! [A_469,B_470,C_471] : r2_hidden(A_469,k1_enumset1(A_469,B_470,C_471)) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_814])).

tff(c_822,plain,(
    ! [A_472,B_473] : r2_hidden(A_472,k2_tarski(A_472,B_473)) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_818])).

tff(c_825,plain,(
    ! [A_18] : r2_hidden(A_18,k1_tarski(A_18)) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_822])).

tff(c_14,plain,(
    ! [B_6,H_12,C_7,I_13,E_9,D_8,A_5,K_17,F_10] : r2_hidden(K_17,k7_enumset1(A_5,B_6,C_7,D_8,E_9,F_10,K_17,H_12,I_13)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_470,plain,(
    ! [B_251,E_248,C_250,A_249,D_252] : k4_enumset1(A_249,A_249,B_251,C_250,D_252,E_248) = k3_enumset1(A_249,B_251,C_250,D_252,E_248) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_112,plain,(
    ! [B_59,F_63,E_62,H_67,D_61,C_60] : r2_hidden(H_67,k4_enumset1(H_67,B_59,C_60,D_61,E_62,F_63)) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_519,plain,(
    ! [A_272,D_270,E_269,C_268,B_271] : r2_hidden(A_272,k3_enumset1(A_272,B_271,C_268,D_270,E_269)) ),
    inference(superposition,[status(thm),theory(equality)],[c_470,c_112])).

tff(c_557,plain,(
    ! [A_280,B_281,C_282,D_283] : r2_hidden(A_280,k2_enumset1(A_280,B_281,C_282,D_283)) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_519])).

tff(c_561,plain,(
    ! [A_284,B_285,C_286] : r2_hidden(A_284,k1_enumset1(A_284,B_285,C_286)) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_557])).

tff(c_565,plain,(
    ! [A_287,B_288] : r2_hidden(A_287,k2_tarski(A_287,B_288)) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_561])).

tff(c_568,plain,(
    ! [A_18] : r2_hidden(A_18,k1_tarski(A_18)) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_565])).

tff(c_148,plain,(
    k4_tarski('#skF_6','#skF_7') = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_169,plain,(
    ! [A_74,B_75] : k1_mcart_1(k4_tarski(A_74,B_75)) = A_74 ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_178,plain,(
    k1_mcart_1('#skF_5') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_169])).

tff(c_195,plain,(
    ! [A_79,B_80] : k2_mcart_1(k4_tarski(A_79,B_80)) = B_80 ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_204,plain,(
    k2_mcart_1('#skF_5') = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_195])).

tff(c_146,plain,
    ( k2_mcart_1('#skF_5') = '#skF_5'
    | k1_mcart_1('#skF_5') = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_211,plain,
    ( '#skF_7' = '#skF_5'
    | '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_204,c_146])).

tff(c_212,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_211])).

tff(c_215,plain,(
    k4_tarski('#skF_6','#skF_7') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_148])).

tff(c_375,plain,(
    ! [A_239,B_240,C_241,D_242] :
      ( r2_hidden(k4_tarski(A_239,B_240),k2_zfmisc_1(C_241,D_242))
      | ~ r2_hidden(B_240,D_242)
      | ~ r2_hidden(A_239,C_241) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_397,plain,(
    ! [C_243,D_244] :
      ( r2_hidden('#skF_6',k2_zfmisc_1(C_243,D_244))
      | ~ r2_hidden('#skF_7',D_244)
      | ~ r2_hidden('#skF_6',C_243) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_375])).

tff(c_4,plain,(
    ! [A_2] : k5_xboole_0(A_2,k1_xboole_0) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [A_1] : k4_xboole_0(k1_xboole_0,A_1) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_301,plain,(
    ! [A_95,B_96] : k5_xboole_0(A_95,k4_xboole_0(B_96,A_95)) = k2_xboole_0(A_95,B_96) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_310,plain,(
    ! [A_1] : k5_xboole_0(A_1,k1_xboole_0) = k2_xboole_0(A_1,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_301])).

tff(c_314,plain,(
    ! [A_97] : k2_xboole_0(A_97,k1_xboole_0) = A_97 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_310])).

tff(c_98,plain,(
    ! [A_56,B_57] : k2_xboole_0(k1_tarski(A_56),B_57) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_321,plain,(
    ! [A_56] : k1_tarski(A_56) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_314,c_98])).

tff(c_84,plain,(
    ! [A_46,B_47] :
      ( r1_tarski(k1_tarski(A_46),B_47)
      | ~ r2_hidden(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_261,plain,(
    ! [A_89,B_90] :
      ( ~ r1_tarski(A_89,k2_zfmisc_1(A_89,B_90))
      | k1_xboole_0 = A_89 ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_266,plain,(
    ! [A_46,B_90] :
      ( k1_tarski(A_46) = k1_xboole_0
      | ~ r2_hidden(A_46,k2_zfmisc_1(k1_tarski(A_46),B_90)) ) ),
    inference(resolution,[status(thm)],[c_84,c_261])).

tff(c_345,plain,(
    ! [A_46,B_90] : ~ r2_hidden(A_46,k2_zfmisc_1(k1_tarski(A_46),B_90)) ),
    inference(negUnitSimplification,[status(thm)],[c_321,c_266])).

tff(c_414,plain,(
    ! [D_244] :
      ( ~ r2_hidden('#skF_7',D_244)
      | ~ r2_hidden('#skF_6',k1_tarski('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_397,c_345])).

tff(c_416,plain,(
    ~ r2_hidden('#skF_6',k1_tarski('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_414])).

tff(c_572,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_568,c_416])).

tff(c_576,plain,(
    ! [D_296] : ~ r2_hidden('#skF_7',D_296) ),
    inference(splitRight,[status(thm)],[c_414])).

tff(c_623,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_14,c_576])).

tff(c_624,plain,(
    '#skF_7' = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_211])).

tff(c_627,plain,(
    k4_tarski('#skF_6','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_624,c_148])).

tff(c_826,plain,(
    ! [A_474,B_475,C_476,D_477] :
      ( r2_hidden(k4_tarski(A_474,B_475),k2_zfmisc_1(C_476,D_477))
      | ~ r2_hidden(B_475,D_477)
      | ~ r2_hidden(A_474,C_476) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_858,plain,(
    ! [C_488,D_489] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(C_488,D_489))
      | ~ r2_hidden('#skF_5',D_489)
      | ~ r2_hidden('#skF_6',C_488) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_627,c_826])).

tff(c_709,plain,(
    ! [A_311,B_312] : k5_xboole_0(A_311,k4_xboole_0(B_312,A_311)) = k2_xboole_0(A_311,B_312) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_718,plain,(
    ! [A_1] : k5_xboole_0(A_1,k1_xboole_0) = k2_xboole_0(A_1,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_709])).

tff(c_723,plain,(
    ! [A_319] : k2_xboole_0(A_319,k1_xboole_0) = A_319 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_718])).

tff(c_730,plain,(
    ! [A_56] : k1_tarski(A_56) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_723,c_98])).

tff(c_683,plain,(
    ! [A_303,B_304] :
      ( ~ r1_tarski(A_303,k2_zfmisc_1(B_304,A_303))
      | k1_xboole_0 = A_303 ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_688,plain,(
    ! [A_46,B_304] :
      ( k1_tarski(A_46) = k1_xboole_0
      | ~ r2_hidden(A_46,k2_zfmisc_1(B_304,k1_tarski(A_46))) ) ),
    inference(resolution,[status(thm)],[c_84,c_683])).

tff(c_751,plain,(
    ! [A_46,B_304] : ~ r2_hidden(A_46,k2_zfmisc_1(B_304,k1_tarski(A_46))) ),
    inference(negUnitSimplification,[status(thm)],[c_730,c_688])).

tff(c_872,plain,(
    ! [C_488] :
      ( ~ r2_hidden('#skF_5',k1_tarski('#skF_5'))
      | ~ r2_hidden('#skF_6',C_488) ) ),
    inference(resolution,[status(thm)],[c_858,c_751])).

tff(c_880,plain,(
    ! [C_490] : ~ r2_hidden('#skF_6',C_490) ),
    inference(demodulation,[status(thm),theory(equality)],[c_825,c_872])).

tff(c_948,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_852,c_880])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:16:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.75/1.57  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.75/1.58  
% 3.75/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.75/1.58  %$ r2_hidden > r1_tarski > k7_enumset1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_3 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_1 > #skF_4
% 3.75/1.58  
% 3.75/1.58  %Foreground sorts:
% 3.75/1.58  
% 3.75/1.58  
% 3.75/1.58  %Background operators:
% 3.75/1.58  
% 3.75/1.58  
% 3.75/1.58  %Foreground operators:
% 3.75/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.75/1.58  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.75/1.58  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.75/1.58  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.75/1.58  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.75/1.58  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.75/1.58  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.75/1.58  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.75/1.58  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.75/1.58  tff(k7_enumset1, type, k7_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.75/1.58  tff('#skF_7', type, '#skF_7': $i).
% 3.75/1.58  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.75/1.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.75/1.58  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.75/1.58  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.75/1.58  tff('#skF_5', type, '#skF_5': $i).
% 3.75/1.58  tff('#skF_6', type, '#skF_6': $i).
% 3.75/1.58  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.75/1.58  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.75/1.58  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.75/1.58  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.75/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.75/1.58  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 3.75/1.58  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.75/1.58  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.75/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.75/1.58  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 3.75/1.58  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.75/1.58  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.75/1.58  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.75/1.58  
% 3.75/1.60  tff(f_72, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 3.75/1.60  tff(f_74, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 3.75/1.60  tff(f_123, axiom, (![A, B, C, D, E, F, G]: ((G = k4_enumset1(A, B, C, D, E, F)) <=> (![H]: (r2_hidden(H, G) <=> ~(((((~(H = A) & ~(H = B)) & ~(H = C)) & ~(H = D)) & ~(H = E)) & ~(H = F)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_enumset1)).
% 3.75/1.60  tff(f_66, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.75/1.60  tff(f_68, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.75/1.60  tff(f_70, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 3.75/1.60  tff(f_64, axiom, (![A, B, C, D, E, F, G, H, I, J]: ((J = k7_enumset1(A, B, C, D, E, F, G, H, I)) <=> (![K]: (r2_hidden(K, J) <=> ~((((((((~(K = A) & ~(K = B)) & ~(K = C)) & ~(K = D)) & ~(K = E)) & ~(K = F)) & ~(K = G)) & ~(K = H)) & ~(K = I)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_enumset1)).
% 3.75/1.60  tff(f_137, negated_conjecture, ~(![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_mcart_1)).
% 3.75/1.60  tff(f_127, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 3.75/1.60  tff(f_90, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 3.75/1.60  tff(f_29, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 3.75/1.60  tff(f_27, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 3.75/1.60  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.75/1.60  tff(f_99, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 3.75/1.60  tff(f_82, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.75/1.60  tff(f_96, axiom, (![A, B]: ((r1_tarski(A, k2_zfmisc_1(A, B)) | r1_tarski(A, k2_zfmisc_1(B, A))) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t135_zfmisc_1)).
% 3.75/1.60  tff(c_74, plain, (![A_24, B_25, C_26, D_27]: (k3_enumset1(A_24, A_24, B_25, C_26, D_27)=k2_enumset1(A_24, B_25, C_26, D_27))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.75/1.60  tff(c_783, plain, (![C_457, B_458, D_459, A_456, E_455]: (k4_enumset1(A_456, A_456, B_458, C_457, D_459, E_455)=k3_enumset1(A_456, B_458, C_457, D_459, E_455))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.75/1.60  tff(c_108, plain, (![B_59, A_58, F_63, E_62, H_67, D_61]: (r2_hidden(H_67, k4_enumset1(A_58, B_59, H_67, D_61, E_62, F_63)))), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.75/1.60  tff(c_849, plain, (![C_482, B_480, A_479, D_483, E_481]: (r2_hidden(B_480, k3_enumset1(A_479, B_480, C_482, D_483, E_481)))), inference(superposition, [status(thm), theory('equality')], [c_783, c_108])).
% 3.75/1.60  tff(c_852, plain, (![A_24, B_25, C_26, D_27]: (r2_hidden(A_24, k2_enumset1(A_24, B_25, C_26, D_27)))), inference(superposition, [status(thm), theory('equality')], [c_74, c_849])).
% 3.75/1.60  tff(c_68, plain, (![A_18]: (k2_tarski(A_18, A_18)=k1_tarski(A_18))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.75/1.60  tff(c_70, plain, (![A_19, B_20]: (k1_enumset1(A_19, A_19, B_20)=k2_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.75/1.60  tff(c_72, plain, (![A_21, B_22, C_23]: (k2_enumset1(A_21, A_21, B_22, C_23)=k1_enumset1(A_21, B_22, C_23))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.75/1.60  tff(c_106, plain, (![B_59, A_58, F_63, E_62, H_67, C_60]: (r2_hidden(H_67, k4_enumset1(A_58, B_59, C_60, H_67, E_62, F_63)))), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.75/1.60  tff(c_810, plain, (![A_460, D_464, B_461, C_463, E_462]: (r2_hidden(C_463, k3_enumset1(A_460, B_461, C_463, D_464, E_462)))), inference(superposition, [status(thm), theory('equality')], [c_783, c_106])).
% 3.75/1.60  tff(c_814, plain, (![B_465, A_466, C_467, D_468]: (r2_hidden(B_465, k2_enumset1(A_466, B_465, C_467, D_468)))), inference(superposition, [status(thm), theory('equality')], [c_74, c_810])).
% 3.75/1.60  tff(c_818, plain, (![A_469, B_470, C_471]: (r2_hidden(A_469, k1_enumset1(A_469, B_470, C_471)))), inference(superposition, [status(thm), theory('equality')], [c_72, c_814])).
% 3.75/1.60  tff(c_822, plain, (![A_472, B_473]: (r2_hidden(A_472, k2_tarski(A_472, B_473)))), inference(superposition, [status(thm), theory('equality')], [c_70, c_818])).
% 3.75/1.60  tff(c_825, plain, (![A_18]: (r2_hidden(A_18, k1_tarski(A_18)))), inference(superposition, [status(thm), theory('equality')], [c_68, c_822])).
% 3.75/1.60  tff(c_14, plain, (![B_6, H_12, C_7, I_13, E_9, D_8, A_5, K_17, F_10]: (r2_hidden(K_17, k7_enumset1(A_5, B_6, C_7, D_8, E_9, F_10, K_17, H_12, I_13)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.75/1.60  tff(c_470, plain, (![B_251, E_248, C_250, A_249, D_252]: (k4_enumset1(A_249, A_249, B_251, C_250, D_252, E_248)=k3_enumset1(A_249, B_251, C_250, D_252, E_248))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.75/1.60  tff(c_112, plain, (![B_59, F_63, E_62, H_67, D_61, C_60]: (r2_hidden(H_67, k4_enumset1(H_67, B_59, C_60, D_61, E_62, F_63)))), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.75/1.60  tff(c_519, plain, (![A_272, D_270, E_269, C_268, B_271]: (r2_hidden(A_272, k3_enumset1(A_272, B_271, C_268, D_270, E_269)))), inference(superposition, [status(thm), theory('equality')], [c_470, c_112])).
% 3.75/1.60  tff(c_557, plain, (![A_280, B_281, C_282, D_283]: (r2_hidden(A_280, k2_enumset1(A_280, B_281, C_282, D_283)))), inference(superposition, [status(thm), theory('equality')], [c_74, c_519])).
% 3.75/1.60  tff(c_561, plain, (![A_284, B_285, C_286]: (r2_hidden(A_284, k1_enumset1(A_284, B_285, C_286)))), inference(superposition, [status(thm), theory('equality')], [c_72, c_557])).
% 3.75/1.60  tff(c_565, plain, (![A_287, B_288]: (r2_hidden(A_287, k2_tarski(A_287, B_288)))), inference(superposition, [status(thm), theory('equality')], [c_70, c_561])).
% 3.75/1.60  tff(c_568, plain, (![A_18]: (r2_hidden(A_18, k1_tarski(A_18)))), inference(superposition, [status(thm), theory('equality')], [c_68, c_565])).
% 3.75/1.60  tff(c_148, plain, (k4_tarski('#skF_6', '#skF_7')='#skF_5'), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.75/1.60  tff(c_169, plain, (![A_74, B_75]: (k1_mcart_1(k4_tarski(A_74, B_75))=A_74)), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.75/1.60  tff(c_178, plain, (k1_mcart_1('#skF_5')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_148, c_169])).
% 3.75/1.60  tff(c_195, plain, (![A_79, B_80]: (k2_mcart_1(k4_tarski(A_79, B_80))=B_80)), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.75/1.60  tff(c_204, plain, (k2_mcart_1('#skF_5')='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_148, c_195])).
% 3.75/1.60  tff(c_146, plain, (k2_mcart_1('#skF_5')='#skF_5' | k1_mcart_1('#skF_5')='#skF_5'), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.75/1.60  tff(c_211, plain, ('#skF_7'='#skF_5' | '#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_178, c_204, c_146])).
% 3.75/1.60  tff(c_212, plain, ('#skF_5'='#skF_6'), inference(splitLeft, [status(thm)], [c_211])).
% 3.75/1.60  tff(c_215, plain, (k4_tarski('#skF_6', '#skF_7')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_212, c_148])).
% 3.75/1.60  tff(c_375, plain, (![A_239, B_240, C_241, D_242]: (r2_hidden(k4_tarski(A_239, B_240), k2_zfmisc_1(C_241, D_242)) | ~r2_hidden(B_240, D_242) | ~r2_hidden(A_239, C_241))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.75/1.60  tff(c_397, plain, (![C_243, D_244]: (r2_hidden('#skF_6', k2_zfmisc_1(C_243, D_244)) | ~r2_hidden('#skF_7', D_244) | ~r2_hidden('#skF_6', C_243))), inference(superposition, [status(thm), theory('equality')], [c_215, c_375])).
% 3.75/1.60  tff(c_4, plain, (![A_2]: (k5_xboole_0(A_2, k1_xboole_0)=A_2)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.75/1.60  tff(c_2, plain, (![A_1]: (k4_xboole_0(k1_xboole_0, A_1)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.75/1.60  tff(c_301, plain, (![A_95, B_96]: (k5_xboole_0(A_95, k4_xboole_0(B_96, A_95))=k2_xboole_0(A_95, B_96))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.75/1.60  tff(c_310, plain, (![A_1]: (k5_xboole_0(A_1, k1_xboole_0)=k2_xboole_0(A_1, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2, c_301])).
% 3.75/1.60  tff(c_314, plain, (![A_97]: (k2_xboole_0(A_97, k1_xboole_0)=A_97)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_310])).
% 3.75/1.60  tff(c_98, plain, (![A_56, B_57]: (k2_xboole_0(k1_tarski(A_56), B_57)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.75/1.60  tff(c_321, plain, (![A_56]: (k1_tarski(A_56)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_314, c_98])).
% 3.75/1.60  tff(c_84, plain, (![A_46, B_47]: (r1_tarski(k1_tarski(A_46), B_47) | ~r2_hidden(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.75/1.60  tff(c_261, plain, (![A_89, B_90]: (~r1_tarski(A_89, k2_zfmisc_1(A_89, B_90)) | k1_xboole_0=A_89)), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.75/1.60  tff(c_266, plain, (![A_46, B_90]: (k1_tarski(A_46)=k1_xboole_0 | ~r2_hidden(A_46, k2_zfmisc_1(k1_tarski(A_46), B_90)))), inference(resolution, [status(thm)], [c_84, c_261])).
% 3.75/1.60  tff(c_345, plain, (![A_46, B_90]: (~r2_hidden(A_46, k2_zfmisc_1(k1_tarski(A_46), B_90)))), inference(negUnitSimplification, [status(thm)], [c_321, c_266])).
% 3.75/1.60  tff(c_414, plain, (![D_244]: (~r2_hidden('#skF_7', D_244) | ~r2_hidden('#skF_6', k1_tarski('#skF_6')))), inference(resolution, [status(thm)], [c_397, c_345])).
% 3.75/1.60  tff(c_416, plain, (~r2_hidden('#skF_6', k1_tarski('#skF_6'))), inference(splitLeft, [status(thm)], [c_414])).
% 3.75/1.60  tff(c_572, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_568, c_416])).
% 3.75/1.60  tff(c_576, plain, (![D_296]: (~r2_hidden('#skF_7', D_296))), inference(splitRight, [status(thm)], [c_414])).
% 3.75/1.60  tff(c_623, plain, $false, inference(resolution, [status(thm)], [c_14, c_576])).
% 3.75/1.60  tff(c_624, plain, ('#skF_7'='#skF_5'), inference(splitRight, [status(thm)], [c_211])).
% 3.75/1.60  tff(c_627, plain, (k4_tarski('#skF_6', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_624, c_148])).
% 3.75/1.60  tff(c_826, plain, (![A_474, B_475, C_476, D_477]: (r2_hidden(k4_tarski(A_474, B_475), k2_zfmisc_1(C_476, D_477)) | ~r2_hidden(B_475, D_477) | ~r2_hidden(A_474, C_476))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.75/1.60  tff(c_858, plain, (![C_488, D_489]: (r2_hidden('#skF_5', k2_zfmisc_1(C_488, D_489)) | ~r2_hidden('#skF_5', D_489) | ~r2_hidden('#skF_6', C_488))), inference(superposition, [status(thm), theory('equality')], [c_627, c_826])).
% 3.75/1.60  tff(c_709, plain, (![A_311, B_312]: (k5_xboole_0(A_311, k4_xboole_0(B_312, A_311))=k2_xboole_0(A_311, B_312))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.75/1.60  tff(c_718, plain, (![A_1]: (k5_xboole_0(A_1, k1_xboole_0)=k2_xboole_0(A_1, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2, c_709])).
% 3.75/1.60  tff(c_723, plain, (![A_319]: (k2_xboole_0(A_319, k1_xboole_0)=A_319)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_718])).
% 3.75/1.60  tff(c_730, plain, (![A_56]: (k1_tarski(A_56)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_723, c_98])).
% 3.75/1.60  tff(c_683, plain, (![A_303, B_304]: (~r1_tarski(A_303, k2_zfmisc_1(B_304, A_303)) | k1_xboole_0=A_303)), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.75/1.60  tff(c_688, plain, (![A_46, B_304]: (k1_tarski(A_46)=k1_xboole_0 | ~r2_hidden(A_46, k2_zfmisc_1(B_304, k1_tarski(A_46))))), inference(resolution, [status(thm)], [c_84, c_683])).
% 3.75/1.60  tff(c_751, plain, (![A_46, B_304]: (~r2_hidden(A_46, k2_zfmisc_1(B_304, k1_tarski(A_46))))), inference(negUnitSimplification, [status(thm)], [c_730, c_688])).
% 3.75/1.60  tff(c_872, plain, (![C_488]: (~r2_hidden('#skF_5', k1_tarski('#skF_5')) | ~r2_hidden('#skF_6', C_488))), inference(resolution, [status(thm)], [c_858, c_751])).
% 3.75/1.60  tff(c_880, plain, (![C_490]: (~r2_hidden('#skF_6', C_490))), inference(demodulation, [status(thm), theory('equality')], [c_825, c_872])).
% 3.75/1.60  tff(c_948, plain, $false, inference(resolution, [status(thm)], [c_852, c_880])).
% 3.75/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.75/1.60  
% 3.75/1.60  Inference rules
% 3.75/1.60  ----------------------
% 3.75/1.60  #Ref     : 0
% 3.75/1.60  #Sup     : 196
% 3.75/1.60  #Fact    : 0
% 3.75/1.60  #Define  : 0
% 3.75/1.60  #Split   : 3
% 3.75/1.60  #Chain   : 0
% 3.75/1.60  #Close   : 0
% 3.75/1.60  
% 3.75/1.60  Ordering : KBO
% 3.75/1.60  
% 3.75/1.60  Simplification rules
% 3.75/1.60  ----------------------
% 3.75/1.60  #Subsume      : 19
% 3.75/1.60  #Demod        : 16
% 3.75/1.60  #Tautology    : 91
% 3.75/1.60  #SimpNegUnit  : 6
% 3.75/1.60  #BackRed      : 8
% 3.75/1.60  
% 3.75/1.60  #Partial instantiations: 0
% 3.75/1.60  #Strategies tried      : 1
% 3.75/1.60  
% 3.75/1.60  Timing (in seconds)
% 3.75/1.60  ----------------------
% 3.75/1.60  Preprocessing        : 0.39
% 3.75/1.60  Parsing              : 0.19
% 3.75/1.60  CNF conversion       : 0.03
% 3.75/1.60  Main loop            : 0.43
% 3.75/1.60  Inferencing          : 0.13
% 3.75/1.60  Reduction            : 0.12
% 3.75/1.60  Demodulation         : 0.09
% 3.75/1.60  BG Simplification    : 0.03
% 3.75/1.60  Subsumption          : 0.12
% 3.75/1.60  Abstraction          : 0.03
% 3.75/1.60  MUC search           : 0.00
% 3.75/1.60  Cooper               : 0.00
% 3.75/1.60  Total                : 0.86
% 3.75/1.60  Index Insertion      : 0.00
% 3.75/1.60  Index Deletion       : 0.00
% 3.75/1.60  Index Matching       : 0.00
% 3.75/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
