%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:03 EST 2020

% Result     : Theorem 10.16s
% Output     : CNFRefutation 10.16s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 167 expanded)
%              Number of leaves         :   41 (  73 expanded)
%              Depth                    :   11
%              Number of atoms          :  110 ( 179 expanded)
%              Number of equality atoms :   70 ( 122 expanded)
%              Maximal formula depth    :   12 (   3 average)
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

tff(f_96,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
      <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_zfmisc_1)).

tff(f_71,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_73,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_69,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_48,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_50,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_52,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_87,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(c_86,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | ~ r2_hidden('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_144,plain,(
    ~ r2_hidden('#skF_7','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_62,plain,(
    ! [A_31] : k2_tarski(A_31,A_31) = k1_tarski(A_31) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_294,plain,(
    ! [A_89,B_90] : k1_enumset1(A_89,A_89,B_90) = k2_tarski(A_89,B_90) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_42,plain,(
    ! [E_30,A_24,C_26] : r2_hidden(E_30,k1_enumset1(A_24,E_30,C_26)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_312,plain,(
    ! [A_91,B_92] : r2_hidden(A_91,k2_tarski(A_91,B_92)) ),
    inference(superposition,[status(thm),theory(equality)],[c_294,c_42])).

tff(c_315,plain,(
    ! [A_31] : r2_hidden(A_31,k1_tarski(A_31)) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_312])).

tff(c_30,plain,(
    ! [A_17] : k5_xboole_0(A_17,k1_xboole_0) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_90,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | k4_xboole_0(k1_tarski('#skF_7'),'#skF_8') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_147,plain,(
    k4_xboole_0(k1_tarski('#skF_7'),'#skF_8') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_90])).

tff(c_26,plain,(
    ! [A_13,B_14] : k5_xboole_0(A_13,k3_xboole_0(A_13,B_14)) = k4_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_690,plain,(
    ! [A_120,B_121,C_122] : k5_xboole_0(k5_xboole_0(A_120,B_121),C_122) = k5_xboole_0(A_120,k5_xboole_0(B_121,C_122)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_36,plain,(
    ! [A_22,B_23] : k5_xboole_0(k5_xboole_0(A_22,B_23),k2_xboole_0(A_22,B_23)) = k3_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_9267,plain,(
    ! [A_285,B_286] : k5_xboole_0(A_285,k5_xboole_0(B_286,k2_xboole_0(A_285,B_286))) = k3_xboole_0(A_285,B_286) ),
    inference(superposition,[status(thm),theory(equality)],[c_690,c_36])).

tff(c_186,plain,(
    ! [B_80,A_81] : k5_xboole_0(B_80,A_81) = k5_xboole_0(A_81,B_80) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_202,plain,(
    ! [A_81] : k5_xboole_0(k1_xboole_0,A_81) = A_81 ),
    inference(superposition,[status(thm),theory(equality)],[c_186,c_30])).

tff(c_34,plain,(
    ! [A_21] : k5_xboole_0(A_21,A_21) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_800,plain,(
    ! [A_21,C_122] : k5_xboole_0(A_21,k5_xboole_0(A_21,C_122)) = k5_xboole_0(k1_xboole_0,C_122) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_690])).

tff(c_817,plain,(
    ! [A_21,C_122] : k5_xboole_0(A_21,k5_xboole_0(A_21,C_122)) = C_122 ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_800])).

tff(c_9323,plain,(
    ! [B_286,A_285] : k5_xboole_0(B_286,k2_xboole_0(A_285,B_286)) = k5_xboole_0(A_285,k3_xboole_0(A_285,B_286)) ),
    inference(superposition,[status(thm),theory(equality)],[c_9267,c_817])).

tff(c_9440,plain,(
    ! [B_287,A_288] : k5_xboole_0(B_287,k2_xboole_0(A_288,B_287)) = k4_xboole_0(A_288,B_287) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_9323])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_818,plain,(
    ! [A_123,C_124] : k5_xboole_0(A_123,k5_xboole_0(A_123,C_124)) = C_124 ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_800])).

tff(c_876,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k5_xboole_0(B_4,A_3)) = B_4 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_818])).

tff(c_9749,plain,(
    ! [A_291,B_292] : k5_xboole_0(k2_xboole_0(A_291,B_292),k4_xboole_0(A_291,B_292)) = B_292 ),
    inference(superposition,[status(thm),theory(equality)],[c_9440,c_876])).

tff(c_9836,plain,(
    k5_xboole_0(k2_xboole_0(k1_tarski('#skF_7'),'#skF_8'),k1_xboole_0) = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_9749])).

tff(c_9854,plain,(
    k2_xboole_0('#skF_8',k1_tarski('#skF_7')) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_2,c_9836])).

tff(c_8,plain,(
    ! [D_10,B_6,A_5] :
      ( ~ r2_hidden(D_10,B_6)
      | r2_hidden(D_10,k2_xboole_0(A_5,B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_9900,plain,(
    ! [D_293] :
      ( ~ r2_hidden(D_293,k1_tarski('#skF_7'))
      | r2_hidden(D_293,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9854,c_8])).

tff(c_9940,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_315,c_9900])).

tff(c_9953,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_144,c_9940])).

tff(c_9954,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_10141,plain,(
    ! [A_316,B_317] :
      ( r1_tarski(k1_tarski(A_316),B_317)
      | ~ r2_hidden(A_316,B_317) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_28,plain,(
    ! [A_15,B_16] :
      ( k2_xboole_0(A_15,B_16) = B_16
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_10149,plain,(
    ! [A_316,B_317] :
      ( k2_xboole_0(k1_tarski(A_316),B_317) = B_317
      | ~ r2_hidden(A_316,B_317) ) ),
    inference(resolution,[status(thm)],[c_10141,c_28])).

tff(c_10477,plain,(
    ! [A_339,B_340,C_341] : k5_xboole_0(k5_xboole_0(A_339,B_340),C_341) = k5_xboole_0(A_339,k5_xboole_0(B_340,C_341)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_19231,plain,(
    ! [A_509,B_510] : k5_xboole_0(A_509,k5_xboole_0(B_510,k2_xboole_0(A_509,B_510))) = k3_xboole_0(A_509,B_510) ),
    inference(superposition,[status(thm),theory(equality)],[c_10477,c_36])).

tff(c_9990,plain,(
    ! [B_299,A_300] : k5_xboole_0(B_299,A_300) = k5_xboole_0(A_300,B_299) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_10006,plain,(
    ! [A_300] : k5_xboole_0(k1_xboole_0,A_300) = A_300 ),
    inference(superposition,[status(thm),theory(equality)],[c_9990,c_30])).

tff(c_10576,plain,(
    ! [A_21,C_341] : k5_xboole_0(A_21,k5_xboole_0(A_21,C_341)) = k5_xboole_0(k1_xboole_0,C_341) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_10477])).

tff(c_10591,plain,(
    ! [A_21,C_341] : k5_xboole_0(A_21,k5_xboole_0(A_21,C_341)) = C_341 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10006,c_10576])).

tff(c_19287,plain,(
    ! [B_510,A_509] : k5_xboole_0(B_510,k2_xboole_0(A_509,B_510)) = k5_xboole_0(A_509,k3_xboole_0(A_509,B_510)) ),
    inference(superposition,[status(thm),theory(equality)],[c_19231,c_10591])).

tff(c_19404,plain,(
    ! [B_511,A_512] : k5_xboole_0(B_511,k2_xboole_0(A_512,B_511)) = k4_xboole_0(A_512,B_511) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_19287])).

tff(c_19514,plain,(
    ! [B_317,A_316] :
      ( k5_xboole_0(B_317,B_317) = k4_xboole_0(k1_tarski(A_316),B_317)
      | ~ r2_hidden(A_316,B_317) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10149,c_19404])).

tff(c_20103,plain,(
    ! [A_521,B_522] :
      ( k4_xboole_0(k1_tarski(A_521),B_522) = k1_xboole_0
      | ~ r2_hidden(A_521,B_522) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_19514])).

tff(c_9955,plain,(
    k4_xboole_0(k1_tarski('#skF_7'),'#skF_8') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_88,plain,
    ( k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') != k1_xboole_0
    | k4_xboole_0(k1_tarski('#skF_7'),'#skF_8') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_10135,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_9955,c_88])).

tff(c_20151,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_20103,c_10135])).

tff(c_20188,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9954,c_20151])).

tff(c_20189,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_20358,plain,(
    ! [A_548,B_549] :
      ( r1_tarski(k1_tarski(A_548),B_549)
      | ~ r2_hidden(A_548,B_549) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_20365,plain,(
    ! [A_548,B_549] :
      ( k2_xboole_0(k1_tarski(A_548),B_549) = B_549
      | ~ r2_hidden(A_548,B_549) ) ),
    inference(resolution,[status(thm)],[c_20358,c_28])).

tff(c_20879,plain,(
    ! [A_579,B_580] : k5_xboole_0(k5_xboole_0(A_579,B_580),k2_xboole_0(A_579,B_580)) = k3_xboole_0(A_579,B_580) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_32,plain,(
    ! [A_18,B_19,C_20] : k5_xboole_0(k5_xboole_0(A_18,B_19),C_20) = k5_xboole_0(A_18,k5_xboole_0(B_19,C_20)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_24226,plain,(
    ! [A_703,B_704] : k5_xboole_0(A_703,k5_xboole_0(B_704,k2_xboole_0(A_703,B_704))) = k3_xboole_0(A_703,B_704) ),
    inference(superposition,[status(thm),theory(equality)],[c_20879,c_32])).

tff(c_20194,plain,(
    ! [B_532,A_533] : k5_xboole_0(B_532,A_533) = k5_xboole_0(A_533,B_532) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_20210,plain,(
    ! [A_533] : k5_xboole_0(k1_xboole_0,A_533) = A_533 ),
    inference(superposition,[status(thm),theory(equality)],[c_20194,c_30])).

tff(c_20560,plain,(
    ! [A_570,B_571,C_572] : k5_xboole_0(k5_xboole_0(A_570,B_571),C_572) = k5_xboole_0(A_570,k5_xboole_0(B_571,C_572)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_20624,plain,(
    ! [A_21,C_572] : k5_xboole_0(A_21,k5_xboole_0(A_21,C_572)) = k5_xboole_0(k1_xboole_0,C_572) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_20560])).

tff(c_20637,plain,(
    ! [A_21,C_572] : k5_xboole_0(A_21,k5_xboole_0(A_21,C_572)) = C_572 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20210,c_20624])).

tff(c_24244,plain,(
    ! [B_704,A_703] : k5_xboole_0(B_704,k2_xboole_0(A_703,B_704)) = k5_xboole_0(A_703,k3_xboole_0(A_703,B_704)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24226,c_20637])).

tff(c_24330,plain,(
    ! [B_705,A_706] : k5_xboole_0(B_705,k2_xboole_0(A_706,B_705)) = k4_xboole_0(A_706,B_705) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24244])).

tff(c_24402,plain,(
    ! [B_549,A_548] :
      ( k5_xboole_0(B_549,B_549) = k4_xboole_0(k1_tarski(A_548),B_549)
      | ~ r2_hidden(A_548,B_549) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20365,c_24330])).

tff(c_24778,plain,(
    ! [A_714,B_715] :
      ( k4_xboole_0(k1_tarski(A_714),B_715) = k1_xboole_0
      | ~ r2_hidden(A_714,B_715) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_24402])).

tff(c_20190,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_84,plain,
    ( k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') != k1_xboole_0
    | ~ r2_hidden('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_20354,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20190,c_84])).

tff(c_24814,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_24778,c_20354])).

tff(c_24844,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20189,c_24814])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:51:47 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.16/4.06  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.16/4.07  
% 10.16/4.07  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.16/4.07  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_8 > #skF_3
% 10.16/4.07  
% 10.16/4.07  %Foreground sorts:
% 10.16/4.07  
% 10.16/4.07  
% 10.16/4.07  %Background operators:
% 10.16/4.07  
% 10.16/4.07  
% 10.16/4.07  %Foreground operators:
% 10.16/4.07  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 10.16/4.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.16/4.07  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.16/4.07  tff(k1_tarski, type, k1_tarski: $i > $i).
% 10.16/4.07  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.16/4.07  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.16/4.07  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 10.16/4.07  tff('#skF_7', type, '#skF_7': $i).
% 10.16/4.07  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 10.16/4.07  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.16/4.07  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 10.16/4.07  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.16/4.07  tff('#skF_5', type, '#skF_5': $i).
% 10.16/4.07  tff('#skF_6', type, '#skF_6': $i).
% 10.16/4.07  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 10.16/4.07  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 10.16/4.07  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 10.16/4.07  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 10.16/4.07  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 10.16/4.07  tff('#skF_8', type, '#skF_8': $i).
% 10.16/4.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.16/4.07  tff(k3_tarski, type, k3_tarski: $i > $i).
% 10.16/4.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.16/4.07  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.16/4.07  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 10.16/4.07  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 10.16/4.07  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 10.16/4.07  
% 10.16/4.09  tff(f_96, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_zfmisc_1)).
% 10.16/4.09  tff(f_71, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 10.16/4.09  tff(f_73, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 10.16/4.09  tff(f_69, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 10.16/4.09  tff(f_48, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 10.16/4.09  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 10.16/4.09  tff(f_42, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 10.16/4.09  tff(f_50, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 10.16/4.09  tff(f_54, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 10.16/4.09  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 10.16/4.09  tff(f_52, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 10.16/4.09  tff(f_38, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 10.16/4.09  tff(f_87, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 10.16/4.09  tff(f_46, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 10.16/4.09  tff(c_86, plain, (r2_hidden('#skF_5', '#skF_6') | ~r2_hidden('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_96])).
% 10.16/4.09  tff(c_144, plain, (~r2_hidden('#skF_7', '#skF_8')), inference(splitLeft, [status(thm)], [c_86])).
% 10.16/4.09  tff(c_62, plain, (![A_31]: (k2_tarski(A_31, A_31)=k1_tarski(A_31))), inference(cnfTransformation, [status(thm)], [f_71])).
% 10.16/4.09  tff(c_294, plain, (![A_89, B_90]: (k1_enumset1(A_89, A_89, B_90)=k2_tarski(A_89, B_90))), inference(cnfTransformation, [status(thm)], [f_73])).
% 10.16/4.09  tff(c_42, plain, (![E_30, A_24, C_26]: (r2_hidden(E_30, k1_enumset1(A_24, E_30, C_26)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 10.16/4.09  tff(c_312, plain, (![A_91, B_92]: (r2_hidden(A_91, k2_tarski(A_91, B_92)))), inference(superposition, [status(thm), theory('equality')], [c_294, c_42])).
% 10.16/4.09  tff(c_315, plain, (![A_31]: (r2_hidden(A_31, k1_tarski(A_31)))), inference(superposition, [status(thm), theory('equality')], [c_62, c_312])).
% 10.16/4.09  tff(c_30, plain, (![A_17]: (k5_xboole_0(A_17, k1_xboole_0)=A_17)), inference(cnfTransformation, [status(thm)], [f_48])).
% 10.16/4.09  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.16/4.09  tff(c_90, plain, (r2_hidden('#skF_5', '#skF_6') | k4_xboole_0(k1_tarski('#skF_7'), '#skF_8')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_96])).
% 10.16/4.09  tff(c_147, plain, (k4_xboole_0(k1_tarski('#skF_7'), '#skF_8')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_90])).
% 10.16/4.09  tff(c_26, plain, (![A_13, B_14]: (k5_xboole_0(A_13, k3_xboole_0(A_13, B_14))=k4_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_42])).
% 10.16/4.09  tff(c_690, plain, (![A_120, B_121, C_122]: (k5_xboole_0(k5_xboole_0(A_120, B_121), C_122)=k5_xboole_0(A_120, k5_xboole_0(B_121, C_122)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 10.16/4.09  tff(c_36, plain, (![A_22, B_23]: (k5_xboole_0(k5_xboole_0(A_22, B_23), k2_xboole_0(A_22, B_23))=k3_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_54])).
% 10.16/4.09  tff(c_9267, plain, (![A_285, B_286]: (k5_xboole_0(A_285, k5_xboole_0(B_286, k2_xboole_0(A_285, B_286)))=k3_xboole_0(A_285, B_286))), inference(superposition, [status(thm), theory('equality')], [c_690, c_36])).
% 10.16/4.09  tff(c_186, plain, (![B_80, A_81]: (k5_xboole_0(B_80, A_81)=k5_xboole_0(A_81, B_80))), inference(cnfTransformation, [status(thm)], [f_29])).
% 10.16/4.09  tff(c_202, plain, (![A_81]: (k5_xboole_0(k1_xboole_0, A_81)=A_81)), inference(superposition, [status(thm), theory('equality')], [c_186, c_30])).
% 10.16/4.09  tff(c_34, plain, (![A_21]: (k5_xboole_0(A_21, A_21)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_52])).
% 10.16/4.09  tff(c_800, plain, (![A_21, C_122]: (k5_xboole_0(A_21, k5_xboole_0(A_21, C_122))=k5_xboole_0(k1_xboole_0, C_122))), inference(superposition, [status(thm), theory('equality')], [c_34, c_690])).
% 10.16/4.09  tff(c_817, plain, (![A_21, C_122]: (k5_xboole_0(A_21, k5_xboole_0(A_21, C_122))=C_122)), inference(demodulation, [status(thm), theory('equality')], [c_202, c_800])).
% 10.16/4.09  tff(c_9323, plain, (![B_286, A_285]: (k5_xboole_0(B_286, k2_xboole_0(A_285, B_286))=k5_xboole_0(A_285, k3_xboole_0(A_285, B_286)))), inference(superposition, [status(thm), theory('equality')], [c_9267, c_817])).
% 10.16/4.09  tff(c_9440, plain, (![B_287, A_288]: (k5_xboole_0(B_287, k2_xboole_0(A_288, B_287))=k4_xboole_0(A_288, B_287))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_9323])).
% 10.16/4.09  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 10.16/4.09  tff(c_818, plain, (![A_123, C_124]: (k5_xboole_0(A_123, k5_xboole_0(A_123, C_124))=C_124)), inference(demodulation, [status(thm), theory('equality')], [c_202, c_800])).
% 10.16/4.09  tff(c_876, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k5_xboole_0(B_4, A_3))=B_4)), inference(superposition, [status(thm), theory('equality')], [c_4, c_818])).
% 10.16/4.09  tff(c_9749, plain, (![A_291, B_292]: (k5_xboole_0(k2_xboole_0(A_291, B_292), k4_xboole_0(A_291, B_292))=B_292)), inference(superposition, [status(thm), theory('equality')], [c_9440, c_876])).
% 10.16/4.09  tff(c_9836, plain, (k5_xboole_0(k2_xboole_0(k1_tarski('#skF_7'), '#skF_8'), k1_xboole_0)='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_147, c_9749])).
% 10.16/4.09  tff(c_9854, plain, (k2_xboole_0('#skF_8', k1_tarski('#skF_7'))='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_2, c_9836])).
% 10.16/4.09  tff(c_8, plain, (![D_10, B_6, A_5]: (~r2_hidden(D_10, B_6) | r2_hidden(D_10, k2_xboole_0(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 10.16/4.09  tff(c_9900, plain, (![D_293]: (~r2_hidden(D_293, k1_tarski('#skF_7')) | r2_hidden(D_293, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_9854, c_8])).
% 10.16/4.09  tff(c_9940, plain, (r2_hidden('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_315, c_9900])).
% 10.16/4.09  tff(c_9953, plain, $false, inference(negUnitSimplification, [status(thm)], [c_144, c_9940])).
% 10.16/4.09  tff(c_9954, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_90])).
% 10.16/4.09  tff(c_10141, plain, (![A_316, B_317]: (r1_tarski(k1_tarski(A_316), B_317) | ~r2_hidden(A_316, B_317))), inference(cnfTransformation, [status(thm)], [f_87])).
% 10.16/4.09  tff(c_28, plain, (![A_15, B_16]: (k2_xboole_0(A_15, B_16)=B_16 | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_46])).
% 10.16/4.09  tff(c_10149, plain, (![A_316, B_317]: (k2_xboole_0(k1_tarski(A_316), B_317)=B_317 | ~r2_hidden(A_316, B_317))), inference(resolution, [status(thm)], [c_10141, c_28])).
% 10.16/4.09  tff(c_10477, plain, (![A_339, B_340, C_341]: (k5_xboole_0(k5_xboole_0(A_339, B_340), C_341)=k5_xboole_0(A_339, k5_xboole_0(B_340, C_341)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 10.16/4.09  tff(c_19231, plain, (![A_509, B_510]: (k5_xboole_0(A_509, k5_xboole_0(B_510, k2_xboole_0(A_509, B_510)))=k3_xboole_0(A_509, B_510))), inference(superposition, [status(thm), theory('equality')], [c_10477, c_36])).
% 10.16/4.09  tff(c_9990, plain, (![B_299, A_300]: (k5_xboole_0(B_299, A_300)=k5_xboole_0(A_300, B_299))), inference(cnfTransformation, [status(thm)], [f_29])).
% 10.16/4.09  tff(c_10006, plain, (![A_300]: (k5_xboole_0(k1_xboole_0, A_300)=A_300)), inference(superposition, [status(thm), theory('equality')], [c_9990, c_30])).
% 10.16/4.09  tff(c_10576, plain, (![A_21, C_341]: (k5_xboole_0(A_21, k5_xboole_0(A_21, C_341))=k5_xboole_0(k1_xboole_0, C_341))), inference(superposition, [status(thm), theory('equality')], [c_34, c_10477])).
% 10.16/4.09  tff(c_10591, plain, (![A_21, C_341]: (k5_xboole_0(A_21, k5_xboole_0(A_21, C_341))=C_341)), inference(demodulation, [status(thm), theory('equality')], [c_10006, c_10576])).
% 10.16/4.09  tff(c_19287, plain, (![B_510, A_509]: (k5_xboole_0(B_510, k2_xboole_0(A_509, B_510))=k5_xboole_0(A_509, k3_xboole_0(A_509, B_510)))), inference(superposition, [status(thm), theory('equality')], [c_19231, c_10591])).
% 10.16/4.09  tff(c_19404, plain, (![B_511, A_512]: (k5_xboole_0(B_511, k2_xboole_0(A_512, B_511))=k4_xboole_0(A_512, B_511))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_19287])).
% 10.16/4.09  tff(c_19514, plain, (![B_317, A_316]: (k5_xboole_0(B_317, B_317)=k4_xboole_0(k1_tarski(A_316), B_317) | ~r2_hidden(A_316, B_317))), inference(superposition, [status(thm), theory('equality')], [c_10149, c_19404])).
% 10.16/4.09  tff(c_20103, plain, (![A_521, B_522]: (k4_xboole_0(k1_tarski(A_521), B_522)=k1_xboole_0 | ~r2_hidden(A_521, B_522))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_19514])).
% 10.16/4.09  tff(c_9955, plain, (k4_xboole_0(k1_tarski('#skF_7'), '#skF_8')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_90])).
% 10.16/4.09  tff(c_88, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')!=k1_xboole_0 | k4_xboole_0(k1_tarski('#skF_7'), '#skF_8')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_96])).
% 10.16/4.09  tff(c_10135, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_9955, c_88])).
% 10.16/4.09  tff(c_20151, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_20103, c_10135])).
% 10.16/4.09  tff(c_20188, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9954, c_20151])).
% 10.16/4.09  tff(c_20189, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_86])).
% 10.16/4.09  tff(c_20358, plain, (![A_548, B_549]: (r1_tarski(k1_tarski(A_548), B_549) | ~r2_hidden(A_548, B_549))), inference(cnfTransformation, [status(thm)], [f_87])).
% 10.16/4.09  tff(c_20365, plain, (![A_548, B_549]: (k2_xboole_0(k1_tarski(A_548), B_549)=B_549 | ~r2_hidden(A_548, B_549))), inference(resolution, [status(thm)], [c_20358, c_28])).
% 10.16/4.09  tff(c_20879, plain, (![A_579, B_580]: (k5_xboole_0(k5_xboole_0(A_579, B_580), k2_xboole_0(A_579, B_580))=k3_xboole_0(A_579, B_580))), inference(cnfTransformation, [status(thm)], [f_54])).
% 10.16/4.09  tff(c_32, plain, (![A_18, B_19, C_20]: (k5_xboole_0(k5_xboole_0(A_18, B_19), C_20)=k5_xboole_0(A_18, k5_xboole_0(B_19, C_20)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 10.16/4.09  tff(c_24226, plain, (![A_703, B_704]: (k5_xboole_0(A_703, k5_xboole_0(B_704, k2_xboole_0(A_703, B_704)))=k3_xboole_0(A_703, B_704))), inference(superposition, [status(thm), theory('equality')], [c_20879, c_32])).
% 10.16/4.09  tff(c_20194, plain, (![B_532, A_533]: (k5_xboole_0(B_532, A_533)=k5_xboole_0(A_533, B_532))), inference(cnfTransformation, [status(thm)], [f_29])).
% 10.16/4.09  tff(c_20210, plain, (![A_533]: (k5_xboole_0(k1_xboole_0, A_533)=A_533)), inference(superposition, [status(thm), theory('equality')], [c_20194, c_30])).
% 10.16/4.09  tff(c_20560, plain, (![A_570, B_571, C_572]: (k5_xboole_0(k5_xboole_0(A_570, B_571), C_572)=k5_xboole_0(A_570, k5_xboole_0(B_571, C_572)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 10.16/4.09  tff(c_20624, plain, (![A_21, C_572]: (k5_xboole_0(A_21, k5_xboole_0(A_21, C_572))=k5_xboole_0(k1_xboole_0, C_572))), inference(superposition, [status(thm), theory('equality')], [c_34, c_20560])).
% 10.16/4.09  tff(c_20637, plain, (![A_21, C_572]: (k5_xboole_0(A_21, k5_xboole_0(A_21, C_572))=C_572)), inference(demodulation, [status(thm), theory('equality')], [c_20210, c_20624])).
% 10.16/4.09  tff(c_24244, plain, (![B_704, A_703]: (k5_xboole_0(B_704, k2_xboole_0(A_703, B_704))=k5_xboole_0(A_703, k3_xboole_0(A_703, B_704)))), inference(superposition, [status(thm), theory('equality')], [c_24226, c_20637])).
% 10.16/4.09  tff(c_24330, plain, (![B_705, A_706]: (k5_xboole_0(B_705, k2_xboole_0(A_706, B_705))=k4_xboole_0(A_706, B_705))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24244])).
% 10.16/4.09  tff(c_24402, plain, (![B_549, A_548]: (k5_xboole_0(B_549, B_549)=k4_xboole_0(k1_tarski(A_548), B_549) | ~r2_hidden(A_548, B_549))), inference(superposition, [status(thm), theory('equality')], [c_20365, c_24330])).
% 10.16/4.09  tff(c_24778, plain, (![A_714, B_715]: (k4_xboole_0(k1_tarski(A_714), B_715)=k1_xboole_0 | ~r2_hidden(A_714, B_715))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_24402])).
% 10.16/4.09  tff(c_20190, plain, (r2_hidden('#skF_7', '#skF_8')), inference(splitRight, [status(thm)], [c_86])).
% 10.16/4.09  tff(c_84, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')!=k1_xboole_0 | ~r2_hidden('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_96])).
% 10.16/4.09  tff(c_20354, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_20190, c_84])).
% 10.16/4.09  tff(c_24814, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_24778, c_20354])).
% 10.16/4.09  tff(c_24844, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20189, c_24814])).
% 10.16/4.09  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.16/4.09  
% 10.16/4.09  Inference rules
% 10.16/4.09  ----------------------
% 10.16/4.09  #Ref     : 0
% 10.16/4.09  #Sup     : 6054
% 10.16/4.09  #Fact    : 18
% 10.16/4.09  #Define  : 0
% 10.16/4.09  #Split   : 2
% 10.16/4.09  #Chain   : 0
% 10.16/4.09  #Close   : 0
% 10.16/4.09  
% 10.16/4.09  Ordering : KBO
% 10.16/4.09  
% 10.16/4.09  Simplification rules
% 10.16/4.09  ----------------------
% 10.16/4.09  #Subsume      : 275
% 10.16/4.09  #Demod        : 5374
% 10.16/4.09  #Tautology    : 3331
% 10.16/4.09  #SimpNegUnit  : 2
% 10.16/4.09  #BackRed      : 3
% 10.16/4.09  
% 10.16/4.09  #Partial instantiations: 0
% 10.16/4.09  #Strategies tried      : 1
% 10.16/4.09  
% 10.16/4.09  Timing (in seconds)
% 10.16/4.09  ----------------------
% 10.16/4.10  Preprocessing        : 0.34
% 10.16/4.10  Parsing              : 0.18
% 10.16/4.10  CNF conversion       : 0.02
% 10.16/4.10  Main loop            : 2.98
% 10.16/4.10  Inferencing          : 0.71
% 10.16/4.10  Reduction            : 1.56
% 10.16/4.10  Demodulation         : 1.38
% 10.16/4.10  BG Simplification    : 0.10
% 10.16/4.10  Subsumption          : 0.45
% 10.16/4.10  Abstraction          : 0.15
% 10.16/4.10  MUC search           : 0.00
% 10.16/4.10  Cooper               : 0.00
% 10.16/4.10  Total                : 3.36
% 10.16/4.10  Index Insertion      : 0.00
% 10.16/4.10  Index Deletion       : 0.00
% 10.16/4.10  Index Matching       : 0.00
% 10.16/4.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
