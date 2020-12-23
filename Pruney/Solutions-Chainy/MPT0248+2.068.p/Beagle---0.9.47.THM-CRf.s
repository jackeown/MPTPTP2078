%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:13 EST 2020

% Result     : Theorem 13.07s
% Output     : CNFRefutation 13.07s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 249 expanded)
%              Number of leaves         :   44 ( 100 expanded)
%              Depth                    :   12
%              Number of atoms          :  152 ( 424 expanded)
%              Number of equality atoms :   87 ( 321 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_6 > #skF_8 > #skF_3 > #skF_2 > #skF_5 > #skF_4

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_127,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_101,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_70,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_52,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_64,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_83,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_74,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_44,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_60,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_66,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_68,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_76,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_72,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(c_80,plain,
    ( k1_tarski('#skF_6') != '#skF_8'
    | k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_144,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_70,plain,(
    ! [A_68,B_69] :
      ( r1_tarski(k1_tarski(A_68),B_69)
      | ~ r2_hidden(A_68,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_78,plain,
    ( k1_xboole_0 != '#skF_8'
    | k1_tarski('#skF_6') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_143,plain,(
    k1_tarski('#skF_6') != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_84,plain,(
    k2_xboole_0('#skF_7','#skF_8') = k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_34,plain,(
    ! [A_27,B_28] : r1_tarski(A_27,k2_xboole_0(A_27,B_28)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_157,plain,(
    r1_tarski('#skF_7',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_34])).

tff(c_426,plain,(
    ! [B_114,A_115] :
      ( B_114 = A_115
      | ~ r1_tarski(B_114,A_115)
      | ~ r1_tarski(A_115,B_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_430,plain,
    ( k1_tarski('#skF_6') = '#skF_7'
    | ~ r1_tarski(k1_tarski('#skF_6'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_157,c_426])).

tff(c_438,plain,(
    ~ r1_tarski(k1_tarski('#skF_6'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_143,c_430])).

tff(c_471,plain,(
    ~ r2_hidden('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_70,c_438])).

tff(c_18,plain,(
    ! [A_16] :
      ( r2_hidden('#skF_3'(A_16),A_16)
      | k1_xboole_0 = A_16 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_312,plain,(
    ! [A_100,B_101] :
      ( k2_xboole_0(A_100,B_101) = B_101
      | ~ r1_tarski(A_100,B_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_326,plain,(
    k2_xboole_0('#skF_7',k1_tarski('#skF_6')) = k1_tarski('#skF_6') ),
    inference(resolution,[status(thm)],[c_157,c_312])).

tff(c_325,plain,(
    ! [A_68,B_69] :
      ( k2_xboole_0(k1_tarski(A_68),B_69) = B_69
      | ~ r2_hidden(A_68,B_69) ) ),
    inference(resolution,[status(thm)],[c_70,c_312])).

tff(c_338,plain,(
    ! [A_102,B_103] :
      ( r2_hidden(A_102,B_103)
      | ~ r1_tarski(k1_tarski(A_102),B_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_351,plain,(
    ! [A_102,B_28] : r2_hidden(A_102,k2_xboole_0(k1_tarski(A_102),B_28)) ),
    inference(resolution,[status(thm)],[c_34,c_338])).

tff(c_789,plain,(
    ! [C_150,B_151,A_152] :
      ( r2_hidden(C_150,B_151)
      | ~ r2_hidden(C_150,A_152)
      | ~ r1_tarski(A_152,B_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_6941,plain,(
    ! [A_305,B_306,B_307] :
      ( r2_hidden(A_305,B_306)
      | ~ r1_tarski(k2_xboole_0(k1_tarski(A_305),B_307),B_306) ) ),
    inference(resolution,[status(thm)],[c_351,c_789])).

tff(c_6973,plain,(
    ! [A_308,B_309,B_310] : r2_hidden(A_308,k2_xboole_0(k2_xboole_0(k1_tarski(A_308),B_309),B_310)) ),
    inference(resolution,[status(thm)],[c_34,c_6941])).

tff(c_7185,plain,(
    ! [A_320,B_321,B_322] :
      ( r2_hidden(A_320,k2_xboole_0(B_321,B_322))
      | ~ r2_hidden(A_320,B_321) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_325,c_6973])).

tff(c_7506,plain,(
    ! [A_325] :
      ( r2_hidden(A_325,k1_tarski('#skF_6'))
      | ~ r2_hidden(A_325,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_326,c_7185])).

tff(c_42,plain,(
    ! [C_39,A_35] :
      ( C_39 = A_35
      | ~ r2_hidden(C_39,k1_tarski(A_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_7528,plain,(
    ! [A_326] :
      ( A_326 = '#skF_6'
      | ~ r2_hidden(A_326,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_7506,c_42])).

tff(c_7556,plain,
    ( '#skF_3'('#skF_7') = '#skF_6'
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_18,c_7528])).

tff(c_7565,plain,(
    '#skF_3'('#skF_7') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_144,c_7556])).

tff(c_7572,plain,
    ( r2_hidden('#skF_6','#skF_7')
    | k1_xboole_0 = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_7565,c_18])).

tff(c_7577,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_144,c_471,c_7572])).

tff(c_7578,plain,(
    k1_tarski('#skF_6') != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_7579,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_38,plain,(
    ! [A_32] : k5_xboole_0(A_32,A_32) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_7587,plain,(
    ! [A_32] : k5_xboole_0(A_32,A_32) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7579,c_38])).

tff(c_16,plain,(
    ! [A_14] : k3_xboole_0(A_14,A_14) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_7964,plain,(
    ! [A_371,B_372] : k5_xboole_0(A_371,k3_xboole_0(A_371,B_372)) = k4_xboole_0(A_371,B_372) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_7981,plain,(
    ! [A_14] : k5_xboole_0(A_14,A_14) = k4_xboole_0(A_14,A_14) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_7964])).

tff(c_7984,plain,(
    ! [A_14] : k4_xboole_0(A_14,A_14) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7587,c_7981])).

tff(c_7873,plain,(
    ! [A_356,B_357] : k2_xboole_0(k3_xboole_0(A_356,B_357),k4_xboole_0(A_356,B_357)) = A_356 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_7885,plain,(
    ! [A_14] : k2_xboole_0(A_14,k4_xboole_0(A_14,A_14)) = A_14 ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_7873])).

tff(c_7985,plain,(
    ! [A_14] : k2_xboole_0(A_14,'#skF_7') = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_7984,c_7885])).

tff(c_32,plain,(
    ! [A_26] : k5_xboole_0(A_26,k1_xboole_0) = A_26 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_7588,plain,(
    ! [A_26] : k5_xboole_0(A_26,'#skF_7') = A_26 ),
    inference(demodulation,[status(thm),theory(equality)],[c_7579,c_32])).

tff(c_8335,plain,(
    ! [A_399,B_400] : k5_xboole_0(k5_xboole_0(A_399,B_400),k2_xboole_0(A_399,B_400)) = k3_xboole_0(A_399,B_400) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_8392,plain,(
    ! [A_26] : k5_xboole_0(A_26,k2_xboole_0(A_26,'#skF_7')) = k3_xboole_0(A_26,'#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_7588,c_8335])).

tff(c_8458,plain,(
    ! [A_403] : k3_xboole_0(A_403,'#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7587,c_7985,c_8392])).

tff(c_7898,plain,(
    ! [A_360,B_361] : r1_tarski(k3_xboole_0(A_360,B_361),A_360) ),
    inference(superposition,[status(thm),theory(equality)],[c_7873,c_34])).

tff(c_28,plain,(
    ! [A_22,B_23] :
      ( k2_xboole_0(A_22,B_23) = B_23
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_7905,plain,(
    ! [A_360,B_361] : k2_xboole_0(k3_xboole_0(A_360,B_361),A_360) = A_360 ),
    inference(resolution,[status(thm)],[c_7898,c_28])).

tff(c_8469,plain,(
    ! [A_403] : k2_xboole_0('#skF_7',A_403) = A_403 ),
    inference(superposition,[status(thm),theory(equality)],[c_8458,c_7905])).

tff(c_8623,plain,(
    k1_tarski('#skF_6') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8469,c_84])).

tff(c_8625,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7578,c_8623])).

tff(c_8627,plain,(
    k1_tarski('#skF_6') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_82,plain,
    ( k1_tarski('#skF_6') != '#skF_8'
    | k1_tarski('#skF_6') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_8661,plain,(
    '#skF_7' != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8627,c_8627,c_82])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8673,plain,(
    ! [B_412,A_413] : k5_xboole_0(B_412,A_413) = k5_xboole_0(A_413,B_412) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8689,plain,(
    ! [A_413] : k5_xboole_0(k1_xboole_0,A_413) = A_413 ),
    inference(superposition,[status(thm),theory(equality)],[c_8673,c_32])).

tff(c_10159,plain,(
    ! [A_509,B_510,C_511] : k5_xboole_0(k5_xboole_0(A_509,B_510),C_511) = k5_xboole_0(A_509,k5_xboole_0(B_510,C_511)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_10216,plain,(
    ! [A_32,C_511] : k5_xboole_0(A_32,k5_xboole_0(A_32,C_511)) = k5_xboole_0(k1_xboole_0,C_511) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_10159])).

tff(c_10237,plain,(
    ! [A_512,C_513] : k5_xboole_0(A_512,k5_xboole_0(A_512,C_513)) = C_513 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8689,c_10216])).

tff(c_10280,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k5_xboole_0(B_2,A_1)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_10237])).

tff(c_8642,plain,(
    k2_xboole_0('#skF_7','#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8627,c_84])).

tff(c_10624,plain,(
    ! [A_522,B_523] : k5_xboole_0(k5_xboole_0(A_522,B_523),k2_xboole_0(A_522,B_523)) = k3_xboole_0(A_522,B_523) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_10721,plain,(
    k5_xboole_0(k5_xboole_0('#skF_7','#skF_8'),'#skF_7') = k3_xboole_0('#skF_7','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_8642,c_10624])).

tff(c_10740,plain,(
    k3_xboole_0('#skF_7','#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10280,c_2,c_2,c_10721])).

tff(c_9066,plain,(
    ! [A_446,B_447] : k2_xboole_0(k3_xboole_0(A_446,B_447),k4_xboole_0(A_446,B_447)) = A_446 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_9072,plain,(
    ! [A_446,B_447] : r1_tarski(k3_xboole_0(A_446,B_447),A_446) ),
    inference(superposition,[status(thm),theory(equality)],[c_9066,c_34])).

tff(c_10794,plain,(
    r1_tarski('#skF_8','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_10740,c_9072])).

tff(c_20,plain,(
    ! [B_19,A_18] :
      ( B_19 = A_18
      | ~ r1_tarski(B_19,A_18)
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_10901,plain,
    ( '#skF_7' = '#skF_8'
    | ~ r1_tarski('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_10794,c_20])).

tff(c_10911,plain,(
    ~ r1_tarski('#skF_7','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_8661,c_10901])).

tff(c_8626,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_9447,plain,(
    ! [C_476,B_477,A_478] :
      ( r2_hidden(C_476,B_477)
      | ~ r2_hidden(C_476,A_478)
      | ~ r1_tarski(A_478,B_477) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_13342,plain,(
    ! [A_608,B_609] :
      ( r2_hidden('#skF_3'(A_608),B_609)
      | ~ r1_tarski(A_608,B_609)
      | k1_xboole_0 = A_608 ) ),
    inference(resolution,[status(thm)],[c_18,c_9447])).

tff(c_8769,plain,(
    ! [C_415,A_416] :
      ( C_415 = A_416
      | ~ r2_hidden(C_415,k1_tarski(A_416)) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_8780,plain,(
    ! [C_415] :
      ( C_415 = '#skF_6'
      | ~ r2_hidden(C_415,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8627,c_8769])).

tff(c_13473,plain,(
    ! [A_616] :
      ( '#skF_3'(A_616) = '#skF_6'
      | ~ r1_tarski(A_616,'#skF_7')
      | k1_xboole_0 = A_616 ) ),
    inference(resolution,[status(thm)],[c_13342,c_8780])).

tff(c_13476,plain,
    ( '#skF_3'('#skF_8') = '#skF_6'
    | k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_10794,c_13473])).

tff(c_13503,plain,(
    '#skF_3'('#skF_8') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_8626,c_13476])).

tff(c_13523,plain,
    ( r2_hidden('#skF_6','#skF_8')
    | k1_xboole_0 = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_13503,c_18])).

tff(c_13527,plain,(
    r2_hidden('#skF_6','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_8626,c_13523])).

tff(c_8865,plain,(
    ! [A_422,B_423] :
      ( r1_tarski(k1_tarski(A_422),B_423)
      | ~ r2_hidden(A_422,B_423) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_8871,plain,(
    ! [B_423] :
      ( r1_tarski('#skF_7',B_423)
      | ~ r2_hidden('#skF_6',B_423) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8627,c_8865])).

tff(c_13539,plain,(
    r1_tarski('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_13527,c_8871])).

tff(c_13549,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10911,c_13539])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:36:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.07/4.62  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.07/4.64  
% 13.07/4.64  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.07/4.64  %$ r2_hidden > r1_tarski > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_6 > #skF_8 > #skF_3 > #skF_2 > #skF_5 > #skF_4
% 13.07/4.64  
% 13.07/4.64  %Foreground sorts:
% 13.07/4.64  
% 13.07/4.64  
% 13.07/4.64  %Background operators:
% 13.07/4.64  
% 13.07/4.64  
% 13.07/4.64  %Foreground operators:
% 13.07/4.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.07/4.64  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 13.07/4.64  tff(k1_tarski, type, k1_tarski: $i > $i).
% 13.07/4.64  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 13.07/4.64  tff('#skF_1', type, '#skF_1': $i > $i).
% 13.07/4.64  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 13.07/4.64  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 13.07/4.64  tff('#skF_7', type, '#skF_7': $i).
% 13.07/4.64  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 13.07/4.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.07/4.64  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 13.07/4.64  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 13.07/4.64  tff('#skF_6', type, '#skF_6': $i).
% 13.07/4.64  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 13.07/4.64  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 13.07/4.64  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 13.07/4.64  tff('#skF_8', type, '#skF_8': $i).
% 13.07/4.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.07/4.64  tff(k3_tarski, type, k3_tarski: $i > $i).
% 13.07/4.64  tff('#skF_3', type, '#skF_3': $i > $i).
% 13.07/4.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.07/4.64  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 13.07/4.64  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 13.07/4.64  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 13.07/4.64  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 13.07/4.64  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 13.07/4.64  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 13.07/4.64  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 13.07/4.64  
% 13.07/4.67  tff(f_127, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 13.07/4.67  tff(f_101, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 13.07/4.67  tff(f_70, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 13.07/4.67  tff(f_58, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 13.07/4.67  tff(f_52, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 13.07/4.67  tff(f_64, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 13.07/4.67  tff(f_40, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 13.07/4.67  tff(f_83, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 13.07/4.67  tff(f_74, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 13.07/4.67  tff(f_44, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 13.07/4.67  tff(f_60, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 13.07/4.67  tff(f_66, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 13.07/4.67  tff(f_68, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 13.07/4.67  tff(f_76, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 13.07/4.67  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 13.07/4.67  tff(f_72, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 13.07/4.67  tff(c_80, plain, (k1_tarski('#skF_6')!='#skF_8' | k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_127])).
% 13.07/4.67  tff(c_144, plain, (k1_xboole_0!='#skF_7'), inference(splitLeft, [status(thm)], [c_80])).
% 13.07/4.67  tff(c_70, plain, (![A_68, B_69]: (r1_tarski(k1_tarski(A_68), B_69) | ~r2_hidden(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_101])).
% 13.07/4.67  tff(c_78, plain, (k1_xboole_0!='#skF_8' | k1_tarski('#skF_6')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_127])).
% 13.07/4.67  tff(c_143, plain, (k1_tarski('#skF_6')!='#skF_7'), inference(splitLeft, [status(thm)], [c_78])).
% 13.07/4.67  tff(c_84, plain, (k2_xboole_0('#skF_7', '#skF_8')=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_127])).
% 13.07/4.67  tff(c_34, plain, (![A_27, B_28]: (r1_tarski(A_27, k2_xboole_0(A_27, B_28)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 13.07/4.67  tff(c_157, plain, (r1_tarski('#skF_7', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_84, c_34])).
% 13.07/4.67  tff(c_426, plain, (![B_114, A_115]: (B_114=A_115 | ~r1_tarski(B_114, A_115) | ~r1_tarski(A_115, B_114))), inference(cnfTransformation, [status(thm)], [f_58])).
% 13.07/4.67  tff(c_430, plain, (k1_tarski('#skF_6')='#skF_7' | ~r1_tarski(k1_tarski('#skF_6'), '#skF_7')), inference(resolution, [status(thm)], [c_157, c_426])).
% 13.07/4.67  tff(c_438, plain, (~r1_tarski(k1_tarski('#skF_6'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_143, c_430])).
% 13.07/4.67  tff(c_471, plain, (~r2_hidden('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_70, c_438])).
% 13.07/4.67  tff(c_18, plain, (![A_16]: (r2_hidden('#skF_3'(A_16), A_16) | k1_xboole_0=A_16)), inference(cnfTransformation, [status(thm)], [f_52])).
% 13.07/4.67  tff(c_312, plain, (![A_100, B_101]: (k2_xboole_0(A_100, B_101)=B_101 | ~r1_tarski(A_100, B_101))), inference(cnfTransformation, [status(thm)], [f_64])).
% 13.07/4.67  tff(c_326, plain, (k2_xboole_0('#skF_7', k1_tarski('#skF_6'))=k1_tarski('#skF_6')), inference(resolution, [status(thm)], [c_157, c_312])).
% 13.07/4.67  tff(c_325, plain, (![A_68, B_69]: (k2_xboole_0(k1_tarski(A_68), B_69)=B_69 | ~r2_hidden(A_68, B_69))), inference(resolution, [status(thm)], [c_70, c_312])).
% 13.07/4.67  tff(c_338, plain, (![A_102, B_103]: (r2_hidden(A_102, B_103) | ~r1_tarski(k1_tarski(A_102), B_103))), inference(cnfTransformation, [status(thm)], [f_101])).
% 13.07/4.67  tff(c_351, plain, (![A_102, B_28]: (r2_hidden(A_102, k2_xboole_0(k1_tarski(A_102), B_28)))), inference(resolution, [status(thm)], [c_34, c_338])).
% 13.07/4.67  tff(c_789, plain, (![C_150, B_151, A_152]: (r2_hidden(C_150, B_151) | ~r2_hidden(C_150, A_152) | ~r1_tarski(A_152, B_151))), inference(cnfTransformation, [status(thm)], [f_40])).
% 13.07/4.67  tff(c_6941, plain, (![A_305, B_306, B_307]: (r2_hidden(A_305, B_306) | ~r1_tarski(k2_xboole_0(k1_tarski(A_305), B_307), B_306))), inference(resolution, [status(thm)], [c_351, c_789])).
% 13.07/4.67  tff(c_6973, plain, (![A_308, B_309, B_310]: (r2_hidden(A_308, k2_xboole_0(k2_xboole_0(k1_tarski(A_308), B_309), B_310)))), inference(resolution, [status(thm)], [c_34, c_6941])).
% 13.07/4.67  tff(c_7185, plain, (![A_320, B_321, B_322]: (r2_hidden(A_320, k2_xboole_0(B_321, B_322)) | ~r2_hidden(A_320, B_321))), inference(superposition, [status(thm), theory('equality')], [c_325, c_6973])).
% 13.07/4.67  tff(c_7506, plain, (![A_325]: (r2_hidden(A_325, k1_tarski('#skF_6')) | ~r2_hidden(A_325, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_326, c_7185])).
% 13.07/4.67  tff(c_42, plain, (![C_39, A_35]: (C_39=A_35 | ~r2_hidden(C_39, k1_tarski(A_35)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 13.07/4.67  tff(c_7528, plain, (![A_326]: (A_326='#skF_6' | ~r2_hidden(A_326, '#skF_7'))), inference(resolution, [status(thm)], [c_7506, c_42])).
% 13.07/4.67  tff(c_7556, plain, ('#skF_3'('#skF_7')='#skF_6' | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_18, c_7528])).
% 13.07/4.67  tff(c_7565, plain, ('#skF_3'('#skF_7')='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_144, c_7556])).
% 13.07/4.67  tff(c_7572, plain, (r2_hidden('#skF_6', '#skF_7') | k1_xboole_0='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_7565, c_18])).
% 13.07/4.67  tff(c_7577, plain, $false, inference(negUnitSimplification, [status(thm)], [c_144, c_471, c_7572])).
% 13.07/4.67  tff(c_7578, plain, (k1_tarski('#skF_6')!='#skF_8'), inference(splitRight, [status(thm)], [c_80])).
% 13.07/4.67  tff(c_7579, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_80])).
% 13.07/4.67  tff(c_38, plain, (![A_32]: (k5_xboole_0(A_32, A_32)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_74])).
% 13.07/4.67  tff(c_7587, plain, (![A_32]: (k5_xboole_0(A_32, A_32)='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_7579, c_38])).
% 13.07/4.67  tff(c_16, plain, (![A_14]: (k3_xboole_0(A_14, A_14)=A_14)), inference(cnfTransformation, [status(thm)], [f_44])).
% 13.07/4.67  tff(c_7964, plain, (![A_371, B_372]: (k5_xboole_0(A_371, k3_xboole_0(A_371, B_372))=k4_xboole_0(A_371, B_372))), inference(cnfTransformation, [status(thm)], [f_60])).
% 13.07/4.67  tff(c_7981, plain, (![A_14]: (k5_xboole_0(A_14, A_14)=k4_xboole_0(A_14, A_14))), inference(superposition, [status(thm), theory('equality')], [c_16, c_7964])).
% 13.07/4.67  tff(c_7984, plain, (![A_14]: (k4_xboole_0(A_14, A_14)='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_7587, c_7981])).
% 13.07/4.67  tff(c_7873, plain, (![A_356, B_357]: (k2_xboole_0(k3_xboole_0(A_356, B_357), k4_xboole_0(A_356, B_357))=A_356)), inference(cnfTransformation, [status(thm)], [f_66])).
% 13.07/4.67  tff(c_7885, plain, (![A_14]: (k2_xboole_0(A_14, k4_xboole_0(A_14, A_14))=A_14)), inference(superposition, [status(thm), theory('equality')], [c_16, c_7873])).
% 13.07/4.67  tff(c_7985, plain, (![A_14]: (k2_xboole_0(A_14, '#skF_7')=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_7984, c_7885])).
% 13.07/4.67  tff(c_32, plain, (![A_26]: (k5_xboole_0(A_26, k1_xboole_0)=A_26)), inference(cnfTransformation, [status(thm)], [f_68])).
% 13.07/4.67  tff(c_7588, plain, (![A_26]: (k5_xboole_0(A_26, '#skF_7')=A_26)), inference(demodulation, [status(thm), theory('equality')], [c_7579, c_32])).
% 13.07/4.67  tff(c_8335, plain, (![A_399, B_400]: (k5_xboole_0(k5_xboole_0(A_399, B_400), k2_xboole_0(A_399, B_400))=k3_xboole_0(A_399, B_400))), inference(cnfTransformation, [status(thm)], [f_76])).
% 13.07/4.67  tff(c_8392, plain, (![A_26]: (k5_xboole_0(A_26, k2_xboole_0(A_26, '#skF_7'))=k3_xboole_0(A_26, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_7588, c_8335])).
% 13.07/4.67  tff(c_8458, plain, (![A_403]: (k3_xboole_0(A_403, '#skF_7')='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_7587, c_7985, c_8392])).
% 13.07/4.67  tff(c_7898, plain, (![A_360, B_361]: (r1_tarski(k3_xboole_0(A_360, B_361), A_360))), inference(superposition, [status(thm), theory('equality')], [c_7873, c_34])).
% 13.07/4.67  tff(c_28, plain, (![A_22, B_23]: (k2_xboole_0(A_22, B_23)=B_23 | ~r1_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_64])).
% 13.07/4.67  tff(c_7905, plain, (![A_360, B_361]: (k2_xboole_0(k3_xboole_0(A_360, B_361), A_360)=A_360)), inference(resolution, [status(thm)], [c_7898, c_28])).
% 13.07/4.67  tff(c_8469, plain, (![A_403]: (k2_xboole_0('#skF_7', A_403)=A_403)), inference(superposition, [status(thm), theory('equality')], [c_8458, c_7905])).
% 13.07/4.67  tff(c_8623, plain, (k1_tarski('#skF_6')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_8469, c_84])).
% 13.07/4.67  tff(c_8625, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7578, c_8623])).
% 13.07/4.67  tff(c_8627, plain, (k1_tarski('#skF_6')='#skF_7'), inference(splitRight, [status(thm)], [c_78])).
% 13.07/4.67  tff(c_82, plain, (k1_tarski('#skF_6')!='#skF_8' | k1_tarski('#skF_6')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_127])).
% 13.07/4.67  tff(c_8661, plain, ('#skF_7'!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_8627, c_8627, c_82])).
% 13.07/4.67  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 13.07/4.67  tff(c_8673, plain, (![B_412, A_413]: (k5_xboole_0(B_412, A_413)=k5_xboole_0(A_413, B_412))), inference(cnfTransformation, [status(thm)], [f_27])).
% 13.07/4.67  tff(c_8689, plain, (![A_413]: (k5_xboole_0(k1_xboole_0, A_413)=A_413)), inference(superposition, [status(thm), theory('equality')], [c_8673, c_32])).
% 13.07/4.67  tff(c_10159, plain, (![A_509, B_510, C_511]: (k5_xboole_0(k5_xboole_0(A_509, B_510), C_511)=k5_xboole_0(A_509, k5_xboole_0(B_510, C_511)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 13.07/4.67  tff(c_10216, plain, (![A_32, C_511]: (k5_xboole_0(A_32, k5_xboole_0(A_32, C_511))=k5_xboole_0(k1_xboole_0, C_511))), inference(superposition, [status(thm), theory('equality')], [c_38, c_10159])).
% 13.07/4.67  tff(c_10237, plain, (![A_512, C_513]: (k5_xboole_0(A_512, k5_xboole_0(A_512, C_513))=C_513)), inference(demodulation, [status(thm), theory('equality')], [c_8689, c_10216])).
% 13.07/4.67  tff(c_10280, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k5_xboole_0(B_2, A_1))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_10237])).
% 13.07/4.67  tff(c_8642, plain, (k2_xboole_0('#skF_7', '#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_8627, c_84])).
% 13.07/4.67  tff(c_10624, plain, (![A_522, B_523]: (k5_xboole_0(k5_xboole_0(A_522, B_523), k2_xboole_0(A_522, B_523))=k3_xboole_0(A_522, B_523))), inference(cnfTransformation, [status(thm)], [f_76])).
% 13.07/4.67  tff(c_10721, plain, (k5_xboole_0(k5_xboole_0('#skF_7', '#skF_8'), '#skF_7')=k3_xboole_0('#skF_7', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_8642, c_10624])).
% 13.07/4.67  tff(c_10740, plain, (k3_xboole_0('#skF_7', '#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_10280, c_2, c_2, c_10721])).
% 13.07/4.67  tff(c_9066, plain, (![A_446, B_447]: (k2_xboole_0(k3_xboole_0(A_446, B_447), k4_xboole_0(A_446, B_447))=A_446)), inference(cnfTransformation, [status(thm)], [f_66])).
% 13.07/4.67  tff(c_9072, plain, (![A_446, B_447]: (r1_tarski(k3_xboole_0(A_446, B_447), A_446))), inference(superposition, [status(thm), theory('equality')], [c_9066, c_34])).
% 13.07/4.67  tff(c_10794, plain, (r1_tarski('#skF_8', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_10740, c_9072])).
% 13.07/4.67  tff(c_20, plain, (![B_19, A_18]: (B_19=A_18 | ~r1_tarski(B_19, A_18) | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_58])).
% 13.07/4.67  tff(c_10901, plain, ('#skF_7'='#skF_8' | ~r1_tarski('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_10794, c_20])).
% 13.07/4.67  tff(c_10911, plain, (~r1_tarski('#skF_7', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_8661, c_10901])).
% 13.07/4.67  tff(c_8626, plain, (k1_xboole_0!='#skF_8'), inference(splitRight, [status(thm)], [c_78])).
% 13.07/4.67  tff(c_9447, plain, (![C_476, B_477, A_478]: (r2_hidden(C_476, B_477) | ~r2_hidden(C_476, A_478) | ~r1_tarski(A_478, B_477))), inference(cnfTransformation, [status(thm)], [f_40])).
% 13.07/4.67  tff(c_13342, plain, (![A_608, B_609]: (r2_hidden('#skF_3'(A_608), B_609) | ~r1_tarski(A_608, B_609) | k1_xboole_0=A_608)), inference(resolution, [status(thm)], [c_18, c_9447])).
% 13.07/4.67  tff(c_8769, plain, (![C_415, A_416]: (C_415=A_416 | ~r2_hidden(C_415, k1_tarski(A_416)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 13.07/4.67  tff(c_8780, plain, (![C_415]: (C_415='#skF_6' | ~r2_hidden(C_415, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_8627, c_8769])).
% 13.07/4.67  tff(c_13473, plain, (![A_616]: ('#skF_3'(A_616)='#skF_6' | ~r1_tarski(A_616, '#skF_7') | k1_xboole_0=A_616)), inference(resolution, [status(thm)], [c_13342, c_8780])).
% 13.07/4.67  tff(c_13476, plain, ('#skF_3'('#skF_8')='#skF_6' | k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_10794, c_13473])).
% 13.07/4.67  tff(c_13503, plain, ('#skF_3'('#skF_8')='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_8626, c_13476])).
% 13.07/4.67  tff(c_13523, plain, (r2_hidden('#skF_6', '#skF_8') | k1_xboole_0='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_13503, c_18])).
% 13.07/4.67  tff(c_13527, plain, (r2_hidden('#skF_6', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_8626, c_13523])).
% 13.07/4.67  tff(c_8865, plain, (![A_422, B_423]: (r1_tarski(k1_tarski(A_422), B_423) | ~r2_hidden(A_422, B_423))), inference(cnfTransformation, [status(thm)], [f_101])).
% 13.07/4.67  tff(c_8871, plain, (![B_423]: (r1_tarski('#skF_7', B_423) | ~r2_hidden('#skF_6', B_423))), inference(superposition, [status(thm), theory('equality')], [c_8627, c_8865])).
% 13.07/4.67  tff(c_13539, plain, (r1_tarski('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_13527, c_8871])).
% 13.07/4.67  tff(c_13549, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10911, c_13539])).
% 13.07/4.67  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.07/4.67  
% 13.07/4.67  Inference rules
% 13.07/4.67  ----------------------
% 13.07/4.67  #Ref     : 0
% 13.07/4.67  #Sup     : 3351
% 13.07/4.67  #Fact    : 0
% 13.07/4.67  #Define  : 0
% 13.07/4.67  #Split   : 3
% 13.07/4.67  #Chain   : 0
% 13.07/4.67  #Close   : 0
% 13.07/4.67  
% 13.07/4.67  Ordering : KBO
% 13.07/4.67  
% 13.07/4.67  Simplification rules
% 13.07/4.67  ----------------------
% 13.07/4.67  #Subsume      : 456
% 13.07/4.67  #Demod        : 2541
% 13.07/4.67  #Tautology    : 1901
% 13.07/4.67  #SimpNegUnit  : 133
% 13.07/4.67  #BackRed      : 15
% 13.07/4.67  
% 13.07/4.67  #Partial instantiations: 0
% 13.07/4.67  #Strategies tried      : 1
% 13.07/4.67  
% 13.07/4.67  Timing (in seconds)
% 13.07/4.67  ----------------------
% 13.07/4.68  Preprocessing        : 0.56
% 13.07/4.68  Parsing              : 0.28
% 13.07/4.68  CNF conversion       : 0.05
% 13.07/4.68  Main loop            : 3.15
% 13.07/4.68  Inferencing          : 0.91
% 13.07/4.68  Reduction            : 1.41
% 13.07/4.68  Demodulation         : 1.13
% 13.07/4.68  BG Simplification    : 0.10
% 13.07/4.68  Subsumption          : 0.52
% 13.07/4.68  Abstraction          : 0.13
% 13.07/4.68  MUC search           : 0.00
% 13.07/4.68  Cooper               : 0.00
% 13.07/4.68  Total                : 3.78
% 13.07/4.68  Index Insertion      : 0.00
% 13.07/4.68  Index Deletion       : 0.00
% 13.07/4.68  Index Matching       : 0.00
% 13.07/4.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
