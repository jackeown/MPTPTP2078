%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:01 EST 2020

% Result     : Theorem 15.90s
% Output     : CNFRefutation 16.01s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 156 expanded)
%              Number of leaves         :   41 (  68 expanded)
%              Depth                    :   10
%              Number of atoms          :  119 ( 176 expanded)
%              Number of equality atoms :   70 ( 109 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_105,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
      <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_zfmisc_1)).

tff(f_73,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_75,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_71,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_48,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_52,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_50,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_44,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_46,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(c_90,plain,
    ( r2_hidden('#skF_3','#skF_4')
    | ~ r2_hidden('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_190,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_90])).

tff(c_60,plain,(
    ! [A_31] : k2_tarski(A_31,A_31) = k1_tarski(A_31) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_298,plain,(
    ! [A_91,B_92] : k1_enumset1(A_91,A_91,B_92) = k2_tarski(A_91,B_92) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_42,plain,(
    ! [E_30,B_25,C_26] : r2_hidden(E_30,k1_enumset1(E_30,B_25,C_26)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_316,plain,(
    ! [A_93,B_94] : r2_hidden(A_93,k2_tarski(A_93,B_94)) ),
    inference(superposition,[status(thm),theory(equality)],[c_298,c_42])).

tff(c_325,plain,(
    ! [A_31] : r2_hidden(A_31,k1_tarski(A_31)) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_316])).

tff(c_196,plain,(
    ! [B_75,A_76] : k5_xboole_0(B_75,A_76) = k5_xboole_0(A_76,B_75) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_26,plain,(
    ! [A_15] : k5_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_212,plain,(
    ! [A_76] : k5_xboole_0(k1_xboole_0,A_76) = A_76 ),
    inference(superposition,[status(thm),theory(equality)],[c_196,c_26])).

tff(c_30,plain,(
    ! [A_19] : k5_xboole_0(A_19,A_19) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_685,plain,(
    ! [A_127,B_128,C_129] : k5_xboole_0(k5_xboole_0(A_127,B_128),C_129) = k5_xboole_0(A_127,k5_xboole_0(B_128,C_129)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_749,plain,(
    ! [A_19,C_129] : k5_xboole_0(A_19,k5_xboole_0(A_19,C_129)) = k5_xboole_0(k1_xboole_0,C_129) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_685])).

tff(c_762,plain,(
    ! [A_19,C_129] : k5_xboole_0(A_19,k5_xboole_0(A_19,C_129)) = C_129 ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_749])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_22,plain,(
    ! [A_12] : k2_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_94,plain,
    ( r2_hidden('#skF_3','#skF_4')
    | k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_191,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_94])).

tff(c_474,plain,(
    ! [A_112,B_113] : k2_xboole_0(A_112,k4_xboole_0(B_113,A_112)) = k2_xboole_0(A_112,B_113) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_489,plain,(
    k2_xboole_0('#skF_6',k1_tarski('#skF_5')) = k2_xboole_0('#skF_6',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_474])).

tff(c_494,plain,(
    k2_xboole_0('#skF_6',k1_tarski('#skF_5')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_489])).

tff(c_908,plain,(
    ! [A_134,B_135] : k5_xboole_0(k5_xboole_0(A_134,B_135),k2_xboole_0(A_134,B_135)) = k3_xboole_0(A_134,B_135) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_966,plain,(
    k5_xboole_0(k5_xboole_0('#skF_6',k1_tarski('#skF_5')),'#skF_6') = k3_xboole_0('#skF_6',k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_494,c_908])).

tff(c_28,plain,(
    ! [A_16,B_17,C_18] : k5_xboole_0(k5_xboole_0(A_16,B_17),C_18) = k5_xboole_0(A_16,k5_xboole_0(B_17,C_18)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1256,plain,(
    k5_xboole_0('#skF_6',k5_xboole_0(k1_tarski('#skF_5'),'#skF_6')) = k3_xboole_0('#skF_6',k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_966,c_28])).

tff(c_1276,plain,(
    k3_xboole_0('#skF_6',k1_tarski('#skF_5')) = k1_tarski('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_762,c_2,c_1256])).

tff(c_18,plain,(
    ! [A_8,B_9] : k5_xboole_0(A_8,k3_xboole_0(A_8,B_9)) = k4_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1416,plain,(
    ! [A_148,B_149,C_150] :
      ( r2_hidden(A_148,B_149)
      | ~ r2_hidden(A_148,C_150)
      | r2_hidden(A_148,k5_xboole_0(B_149,C_150)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_35901,plain,(
    ! [A_410,A_411,B_412] :
      ( r2_hidden(A_410,A_411)
      | ~ r2_hidden(A_410,k3_xboole_0(A_411,B_412))
      | r2_hidden(A_410,k4_xboole_0(A_411,B_412)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_1416])).

tff(c_86,plain,(
    ! [A_64,B_65,C_66] :
      ( r2_hidden(A_64,B_65)
      | ~ r2_hidden(A_64,k4_xboole_0(B_65,k1_tarski(C_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_35964,plain,(
    ! [A_413,A_414,C_415] :
      ( r2_hidden(A_413,A_414)
      | ~ r2_hidden(A_413,k3_xboole_0(A_414,k1_tarski(C_415))) ) ),
    inference(resolution,[status(thm)],[c_35901,c_86])).

tff(c_36006,plain,(
    ! [A_416] :
      ( r2_hidden(A_416,'#skF_6')
      | ~ r2_hidden(A_416,k1_tarski('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1276,c_35964])).

tff(c_36018,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_325,c_36006])).

tff(c_36024,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_190,c_36018])).

tff(c_36025,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_76,plain,(
    ! [A_59,B_60] :
      ( r1_tarski(k1_tarski(A_59),B_60)
      | ~ r2_hidden(A_59,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_36130,plain,(
    ! [A_433,B_434] :
      ( k2_xboole_0(A_433,B_434) = B_434
      | ~ r1_tarski(A_433,B_434) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_36134,plain,(
    ! [A_59,B_60] :
      ( k2_xboole_0(k1_tarski(A_59),B_60) = B_60
      | ~ r2_hidden(A_59,B_60) ) ),
    inference(resolution,[status(thm)],[c_76,c_36130])).

tff(c_36709,plain,(
    ! [A_476,B_477,C_478] : k5_xboole_0(k5_xboole_0(A_476,B_477),C_478) = k5_xboole_0(A_476,k5_xboole_0(B_477,C_478)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_32,plain,(
    ! [A_20,B_21] : k5_xboole_0(k5_xboole_0(A_20,B_21),k2_xboole_0(A_20,B_21)) = k3_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_37952,plain,(
    ! [A_532,B_533] : k5_xboole_0(A_532,k5_xboole_0(B_533,k2_xboole_0(A_532,B_533))) = k3_xboole_0(A_532,B_533) ),
    inference(superposition,[status(thm),theory(equality)],[c_36709,c_32])).

tff(c_36031,plain,(
    ! [B_428,A_429] : k5_xboole_0(B_428,A_429) = k5_xboole_0(A_429,B_428) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_36047,plain,(
    ! [A_429] : k5_xboole_0(k1_xboole_0,A_429) = A_429 ),
    inference(superposition,[status(thm),theory(equality)],[c_36031,c_26])).

tff(c_36786,plain,(
    ! [A_19,C_478] : k5_xboole_0(A_19,k5_xboole_0(A_19,C_478)) = k5_xboole_0(k1_xboole_0,C_478) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_36709])).

tff(c_36799,plain,(
    ! [A_19,C_478] : k5_xboole_0(A_19,k5_xboole_0(A_19,C_478)) = C_478 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36047,c_36786])).

tff(c_37979,plain,(
    ! [B_533,A_532] : k5_xboole_0(B_533,k2_xboole_0(A_532,B_533)) = k5_xboole_0(A_532,k3_xboole_0(A_532,B_533)) ),
    inference(superposition,[status(thm),theory(equality)],[c_37952,c_36799])).

tff(c_38063,plain,(
    ! [B_534,A_535] : k5_xboole_0(B_534,k2_xboole_0(A_535,B_534)) = k4_xboole_0(A_535,B_534) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_37979])).

tff(c_38117,plain,(
    ! [B_60,A_59] :
      ( k5_xboole_0(B_60,B_60) = k4_xboole_0(k1_tarski(A_59),B_60)
      | ~ r2_hidden(A_59,B_60) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36134,c_38063])).

tff(c_38310,plain,(
    ! [A_540,B_541] :
      ( k4_xboole_0(k1_tarski(A_540),B_541) = k1_xboole_0
      | ~ r2_hidden(A_540,B_541) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_38117])).

tff(c_36026,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_92,plain,
    ( k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') != k1_xboole_0
    | k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_36127,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_36026,c_92])).

tff(c_38353,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_38310,c_36127])).

tff(c_38387,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36025,c_38353])).

tff(c_38388,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_38567,plain,(
    ! [A_568,B_569] :
      ( k2_xboole_0(A_568,B_569) = B_569
      | ~ r1_tarski(A_568,B_569) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_38571,plain,(
    ! [A_59,B_60] :
      ( k2_xboole_0(k1_tarski(A_59),B_60) = B_60
      | ~ r2_hidden(A_59,B_60) ) ),
    inference(resolution,[status(thm)],[c_76,c_38567])).

tff(c_39131,plain,(
    ! [A_603,B_604,C_605] : k5_xboole_0(k5_xboole_0(A_603,B_604),C_605) = k5_xboole_0(A_603,k5_xboole_0(B_604,C_605)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_41371,plain,(
    ! [A_664,B_665] : k5_xboole_0(A_664,k5_xboole_0(B_665,k2_xboole_0(A_664,B_665))) = k3_xboole_0(A_664,B_665) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_39131])).

tff(c_38395,plain,(
    ! [B_553,A_554] : k5_xboole_0(B_553,A_554) = k5_xboole_0(A_554,B_553) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_38411,plain,(
    ! [A_554] : k5_xboole_0(k1_xboole_0,A_554) = A_554 ),
    inference(superposition,[status(thm),theory(equality)],[c_38395,c_26])).

tff(c_39208,plain,(
    ! [A_19,C_605] : k5_xboole_0(A_19,k5_xboole_0(A_19,C_605)) = k5_xboole_0(k1_xboole_0,C_605) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_39131])).

tff(c_39221,plain,(
    ! [A_19,C_605] : k5_xboole_0(A_19,k5_xboole_0(A_19,C_605)) = C_605 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38411,c_39208])).

tff(c_41423,plain,(
    ! [B_665,A_664] : k5_xboole_0(B_665,k2_xboole_0(A_664,B_665)) = k5_xboole_0(A_664,k3_xboole_0(A_664,B_665)) ),
    inference(superposition,[status(thm),theory(equality)],[c_41371,c_39221])).

tff(c_41533,plain,(
    ! [B_672,A_673] : k5_xboole_0(B_672,k2_xboole_0(A_673,B_672)) = k4_xboole_0(A_673,B_672) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_41423])).

tff(c_41605,plain,(
    ! [B_60,A_59] :
      ( k5_xboole_0(B_60,B_60) = k4_xboole_0(k1_tarski(A_59),B_60)
      | ~ r2_hidden(A_59,B_60) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38571,c_41533])).

tff(c_42114,plain,(
    ! [A_689,B_690] :
      ( k4_xboole_0(k1_tarski(A_689),B_690) = k1_xboole_0
      | ~ r2_hidden(A_689,B_690) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_41605])).

tff(c_38389,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_88,plain,
    ( k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') != k1_xboole_0
    | ~ r2_hidden('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_38499,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38389,c_88])).

tff(c_42157,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_42114,c_38499])).

tff(c_42188,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38388,c_42157])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n002.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 19:31:06 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 15.90/8.91  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.01/8.91  
% 16.01/8.91  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.01/8.92  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 16.01/8.92  
% 16.01/8.92  %Foreground sorts:
% 16.01/8.92  
% 16.01/8.92  
% 16.01/8.92  %Background operators:
% 16.01/8.92  
% 16.01/8.92  
% 16.01/8.92  %Foreground operators:
% 16.01/8.92  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 16.01/8.92  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 16.01/8.92  tff(k1_tarski, type, k1_tarski: $i > $i).
% 16.01/8.92  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 16.01/8.92  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 16.01/8.92  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 16.01/8.92  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 16.01/8.92  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 16.01/8.92  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 16.01/8.92  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 16.01/8.92  tff('#skF_5', type, '#skF_5': $i).
% 16.01/8.92  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 16.01/8.92  tff('#skF_6', type, '#skF_6': $i).
% 16.01/8.92  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 16.01/8.92  tff('#skF_3', type, '#skF_3': $i).
% 16.01/8.92  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 16.01/8.92  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 16.01/8.92  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 16.01/8.92  tff(k3_tarski, type, k3_tarski: $i > $i).
% 16.01/8.92  tff('#skF_4', type, '#skF_4': $i).
% 16.01/8.92  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 16.01/8.92  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 16.01/8.92  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 16.01/8.92  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 16.01/8.92  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 16.01/8.92  
% 16.01/8.93  tff(f_105, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_zfmisc_1)).
% 16.01/8.93  tff(f_73, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 16.01/8.93  tff(f_75, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 16.01/8.93  tff(f_71, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 16.01/8.93  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 16.01/8.93  tff(f_48, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 16.01/8.93  tff(f_52, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 16.01/8.93  tff(f_50, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 16.01/8.93  tff(f_44, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 16.01/8.93  tff(f_46, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 16.01/8.93  tff(f_54, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 16.01/8.93  tff(f_38, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 16.01/8.93  tff(f_36, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 16.01/8.93  tff(f_100, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 16.01/8.93  tff(f_89, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 16.01/8.93  tff(f_42, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 16.01/8.93  tff(c_90, plain, (r2_hidden('#skF_3', '#skF_4') | ~r2_hidden('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_105])).
% 16.01/8.93  tff(c_190, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_90])).
% 16.01/8.93  tff(c_60, plain, (![A_31]: (k2_tarski(A_31, A_31)=k1_tarski(A_31))), inference(cnfTransformation, [status(thm)], [f_73])).
% 16.01/8.93  tff(c_298, plain, (![A_91, B_92]: (k1_enumset1(A_91, A_91, B_92)=k2_tarski(A_91, B_92))), inference(cnfTransformation, [status(thm)], [f_75])).
% 16.01/8.93  tff(c_42, plain, (![E_30, B_25, C_26]: (r2_hidden(E_30, k1_enumset1(E_30, B_25, C_26)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 16.01/8.93  tff(c_316, plain, (![A_93, B_94]: (r2_hidden(A_93, k2_tarski(A_93, B_94)))), inference(superposition, [status(thm), theory('equality')], [c_298, c_42])).
% 16.01/8.93  tff(c_325, plain, (![A_31]: (r2_hidden(A_31, k1_tarski(A_31)))), inference(superposition, [status(thm), theory('equality')], [c_60, c_316])).
% 16.01/8.93  tff(c_196, plain, (![B_75, A_76]: (k5_xboole_0(B_75, A_76)=k5_xboole_0(A_76, B_75))), inference(cnfTransformation, [status(thm)], [f_27])).
% 16.01/8.93  tff(c_26, plain, (![A_15]: (k5_xboole_0(A_15, k1_xboole_0)=A_15)), inference(cnfTransformation, [status(thm)], [f_48])).
% 16.01/8.93  tff(c_212, plain, (![A_76]: (k5_xboole_0(k1_xboole_0, A_76)=A_76)), inference(superposition, [status(thm), theory('equality')], [c_196, c_26])).
% 16.01/8.93  tff(c_30, plain, (![A_19]: (k5_xboole_0(A_19, A_19)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_52])).
% 16.01/8.93  tff(c_685, plain, (![A_127, B_128, C_129]: (k5_xboole_0(k5_xboole_0(A_127, B_128), C_129)=k5_xboole_0(A_127, k5_xboole_0(B_128, C_129)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 16.01/8.93  tff(c_749, plain, (![A_19, C_129]: (k5_xboole_0(A_19, k5_xboole_0(A_19, C_129))=k5_xboole_0(k1_xboole_0, C_129))), inference(superposition, [status(thm), theory('equality')], [c_30, c_685])).
% 16.01/8.93  tff(c_762, plain, (![A_19, C_129]: (k5_xboole_0(A_19, k5_xboole_0(A_19, C_129))=C_129)), inference(demodulation, [status(thm), theory('equality')], [c_212, c_749])).
% 16.01/8.93  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 16.01/8.93  tff(c_22, plain, (![A_12]: (k2_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_44])).
% 16.01/8.93  tff(c_94, plain, (r2_hidden('#skF_3', '#skF_4') | k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_105])).
% 16.01/8.93  tff(c_191, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_94])).
% 16.01/8.93  tff(c_474, plain, (![A_112, B_113]: (k2_xboole_0(A_112, k4_xboole_0(B_113, A_112))=k2_xboole_0(A_112, B_113))), inference(cnfTransformation, [status(thm)], [f_46])).
% 16.01/8.93  tff(c_489, plain, (k2_xboole_0('#skF_6', k1_tarski('#skF_5'))=k2_xboole_0('#skF_6', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_191, c_474])).
% 16.01/8.93  tff(c_494, plain, (k2_xboole_0('#skF_6', k1_tarski('#skF_5'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_489])).
% 16.01/8.93  tff(c_908, plain, (![A_134, B_135]: (k5_xboole_0(k5_xboole_0(A_134, B_135), k2_xboole_0(A_134, B_135))=k3_xboole_0(A_134, B_135))), inference(cnfTransformation, [status(thm)], [f_54])).
% 16.01/8.93  tff(c_966, plain, (k5_xboole_0(k5_xboole_0('#skF_6', k1_tarski('#skF_5')), '#skF_6')=k3_xboole_0('#skF_6', k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_494, c_908])).
% 16.01/8.93  tff(c_28, plain, (![A_16, B_17, C_18]: (k5_xboole_0(k5_xboole_0(A_16, B_17), C_18)=k5_xboole_0(A_16, k5_xboole_0(B_17, C_18)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 16.01/8.93  tff(c_1256, plain, (k5_xboole_0('#skF_6', k5_xboole_0(k1_tarski('#skF_5'), '#skF_6'))=k3_xboole_0('#skF_6', k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_966, c_28])).
% 16.01/8.93  tff(c_1276, plain, (k3_xboole_0('#skF_6', k1_tarski('#skF_5'))=k1_tarski('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_762, c_2, c_1256])).
% 16.01/8.93  tff(c_18, plain, (![A_8, B_9]: (k5_xboole_0(A_8, k3_xboole_0(A_8, B_9))=k4_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_38])).
% 16.01/8.93  tff(c_1416, plain, (![A_148, B_149, C_150]: (r2_hidden(A_148, B_149) | ~r2_hidden(A_148, C_150) | r2_hidden(A_148, k5_xboole_0(B_149, C_150)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 16.01/8.93  tff(c_35901, plain, (![A_410, A_411, B_412]: (r2_hidden(A_410, A_411) | ~r2_hidden(A_410, k3_xboole_0(A_411, B_412)) | r2_hidden(A_410, k4_xboole_0(A_411, B_412)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_1416])).
% 16.01/8.93  tff(c_86, plain, (![A_64, B_65, C_66]: (r2_hidden(A_64, B_65) | ~r2_hidden(A_64, k4_xboole_0(B_65, k1_tarski(C_66))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 16.01/8.93  tff(c_35964, plain, (![A_413, A_414, C_415]: (r2_hidden(A_413, A_414) | ~r2_hidden(A_413, k3_xboole_0(A_414, k1_tarski(C_415))))), inference(resolution, [status(thm)], [c_35901, c_86])).
% 16.01/8.93  tff(c_36006, plain, (![A_416]: (r2_hidden(A_416, '#skF_6') | ~r2_hidden(A_416, k1_tarski('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_1276, c_35964])).
% 16.01/8.93  tff(c_36018, plain, (r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_325, c_36006])).
% 16.01/8.93  tff(c_36024, plain, $false, inference(negUnitSimplification, [status(thm)], [c_190, c_36018])).
% 16.01/8.93  tff(c_36025, plain, (r2_hidden('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_94])).
% 16.01/8.93  tff(c_76, plain, (![A_59, B_60]: (r1_tarski(k1_tarski(A_59), B_60) | ~r2_hidden(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_89])).
% 16.01/8.93  tff(c_36130, plain, (![A_433, B_434]: (k2_xboole_0(A_433, B_434)=B_434 | ~r1_tarski(A_433, B_434))), inference(cnfTransformation, [status(thm)], [f_42])).
% 16.01/8.93  tff(c_36134, plain, (![A_59, B_60]: (k2_xboole_0(k1_tarski(A_59), B_60)=B_60 | ~r2_hidden(A_59, B_60))), inference(resolution, [status(thm)], [c_76, c_36130])).
% 16.01/8.93  tff(c_36709, plain, (![A_476, B_477, C_478]: (k5_xboole_0(k5_xboole_0(A_476, B_477), C_478)=k5_xboole_0(A_476, k5_xboole_0(B_477, C_478)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 16.01/8.93  tff(c_32, plain, (![A_20, B_21]: (k5_xboole_0(k5_xboole_0(A_20, B_21), k2_xboole_0(A_20, B_21))=k3_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_54])).
% 16.01/8.93  tff(c_37952, plain, (![A_532, B_533]: (k5_xboole_0(A_532, k5_xboole_0(B_533, k2_xboole_0(A_532, B_533)))=k3_xboole_0(A_532, B_533))), inference(superposition, [status(thm), theory('equality')], [c_36709, c_32])).
% 16.01/8.93  tff(c_36031, plain, (![B_428, A_429]: (k5_xboole_0(B_428, A_429)=k5_xboole_0(A_429, B_428))), inference(cnfTransformation, [status(thm)], [f_27])).
% 16.01/8.93  tff(c_36047, plain, (![A_429]: (k5_xboole_0(k1_xboole_0, A_429)=A_429)), inference(superposition, [status(thm), theory('equality')], [c_36031, c_26])).
% 16.01/8.93  tff(c_36786, plain, (![A_19, C_478]: (k5_xboole_0(A_19, k5_xboole_0(A_19, C_478))=k5_xboole_0(k1_xboole_0, C_478))), inference(superposition, [status(thm), theory('equality')], [c_30, c_36709])).
% 16.01/8.93  tff(c_36799, plain, (![A_19, C_478]: (k5_xboole_0(A_19, k5_xboole_0(A_19, C_478))=C_478)), inference(demodulation, [status(thm), theory('equality')], [c_36047, c_36786])).
% 16.01/8.93  tff(c_37979, plain, (![B_533, A_532]: (k5_xboole_0(B_533, k2_xboole_0(A_532, B_533))=k5_xboole_0(A_532, k3_xboole_0(A_532, B_533)))), inference(superposition, [status(thm), theory('equality')], [c_37952, c_36799])).
% 16.01/8.93  tff(c_38063, plain, (![B_534, A_535]: (k5_xboole_0(B_534, k2_xboole_0(A_535, B_534))=k4_xboole_0(A_535, B_534))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_37979])).
% 16.01/8.93  tff(c_38117, plain, (![B_60, A_59]: (k5_xboole_0(B_60, B_60)=k4_xboole_0(k1_tarski(A_59), B_60) | ~r2_hidden(A_59, B_60))), inference(superposition, [status(thm), theory('equality')], [c_36134, c_38063])).
% 16.01/8.93  tff(c_38310, plain, (![A_540, B_541]: (k4_xboole_0(k1_tarski(A_540), B_541)=k1_xboole_0 | ~r2_hidden(A_540, B_541))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_38117])).
% 16.01/8.93  tff(c_36026, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_94])).
% 16.01/8.93  tff(c_92, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')!=k1_xboole_0 | k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_105])).
% 16.01/8.93  tff(c_36127, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_36026, c_92])).
% 16.01/8.93  tff(c_38353, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_38310, c_36127])).
% 16.01/8.93  tff(c_38387, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36025, c_38353])).
% 16.01/8.93  tff(c_38388, plain, (r2_hidden('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_90])).
% 16.01/8.93  tff(c_38567, plain, (![A_568, B_569]: (k2_xboole_0(A_568, B_569)=B_569 | ~r1_tarski(A_568, B_569))), inference(cnfTransformation, [status(thm)], [f_42])).
% 16.01/8.93  tff(c_38571, plain, (![A_59, B_60]: (k2_xboole_0(k1_tarski(A_59), B_60)=B_60 | ~r2_hidden(A_59, B_60))), inference(resolution, [status(thm)], [c_76, c_38567])).
% 16.01/8.93  tff(c_39131, plain, (![A_603, B_604, C_605]: (k5_xboole_0(k5_xboole_0(A_603, B_604), C_605)=k5_xboole_0(A_603, k5_xboole_0(B_604, C_605)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 16.01/8.93  tff(c_41371, plain, (![A_664, B_665]: (k5_xboole_0(A_664, k5_xboole_0(B_665, k2_xboole_0(A_664, B_665)))=k3_xboole_0(A_664, B_665))), inference(superposition, [status(thm), theory('equality')], [c_32, c_39131])).
% 16.01/8.93  tff(c_38395, plain, (![B_553, A_554]: (k5_xboole_0(B_553, A_554)=k5_xboole_0(A_554, B_553))), inference(cnfTransformation, [status(thm)], [f_27])).
% 16.01/8.93  tff(c_38411, plain, (![A_554]: (k5_xboole_0(k1_xboole_0, A_554)=A_554)), inference(superposition, [status(thm), theory('equality')], [c_38395, c_26])).
% 16.01/8.93  tff(c_39208, plain, (![A_19, C_605]: (k5_xboole_0(A_19, k5_xboole_0(A_19, C_605))=k5_xboole_0(k1_xboole_0, C_605))), inference(superposition, [status(thm), theory('equality')], [c_30, c_39131])).
% 16.01/8.93  tff(c_39221, plain, (![A_19, C_605]: (k5_xboole_0(A_19, k5_xboole_0(A_19, C_605))=C_605)), inference(demodulation, [status(thm), theory('equality')], [c_38411, c_39208])).
% 16.01/8.93  tff(c_41423, plain, (![B_665, A_664]: (k5_xboole_0(B_665, k2_xboole_0(A_664, B_665))=k5_xboole_0(A_664, k3_xboole_0(A_664, B_665)))), inference(superposition, [status(thm), theory('equality')], [c_41371, c_39221])).
% 16.01/8.93  tff(c_41533, plain, (![B_672, A_673]: (k5_xboole_0(B_672, k2_xboole_0(A_673, B_672))=k4_xboole_0(A_673, B_672))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_41423])).
% 16.01/8.93  tff(c_41605, plain, (![B_60, A_59]: (k5_xboole_0(B_60, B_60)=k4_xboole_0(k1_tarski(A_59), B_60) | ~r2_hidden(A_59, B_60))), inference(superposition, [status(thm), theory('equality')], [c_38571, c_41533])).
% 16.01/8.93  tff(c_42114, plain, (![A_689, B_690]: (k4_xboole_0(k1_tarski(A_689), B_690)=k1_xboole_0 | ~r2_hidden(A_689, B_690))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_41605])).
% 16.01/8.93  tff(c_38389, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_90])).
% 16.01/8.93  tff(c_88, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')!=k1_xboole_0 | ~r2_hidden('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_105])).
% 16.01/8.93  tff(c_38499, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_38389, c_88])).
% 16.01/8.93  tff(c_42157, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_42114, c_38499])).
% 16.01/8.93  tff(c_42188, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38388, c_42157])).
% 16.01/8.93  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.01/8.93  
% 16.01/8.93  Inference rules
% 16.01/8.93  ----------------------
% 16.01/8.93  #Ref     : 0
% 16.01/8.93  #Sup     : 10926
% 16.01/8.93  #Fact    : 0
% 16.01/8.93  #Define  : 0
% 16.01/8.93  #Split   : 2
% 16.01/8.93  #Chain   : 0
% 16.01/8.93  #Close   : 0
% 16.01/8.93  
% 16.01/8.93  Ordering : KBO
% 16.01/8.93  
% 16.01/8.93  Simplification rules
% 16.01/8.93  ----------------------
% 16.01/8.93  #Subsume      : 1011
% 16.01/8.93  #Demod        : 12942
% 16.01/8.93  #Tautology    : 4326
% 16.01/8.93  #SimpNegUnit  : 72
% 16.01/8.93  #BackRed      : 15
% 16.01/8.93  
% 16.01/8.93  #Partial instantiations: 0
% 16.01/8.93  #Strategies tried      : 1
% 16.01/8.93  
% 16.01/8.93  Timing (in seconds)
% 16.01/8.93  ----------------------
% 16.01/8.94  Preprocessing        : 0.36
% 16.01/8.94  Parsing              : 0.19
% 16.01/8.94  CNF conversion       : 0.03
% 16.01/8.94  Main loop            : 7.77
% 16.01/8.94  Inferencing          : 1.05
% 16.01/8.94  Reduction            : 5.41
% 16.01/8.94  Demodulation         : 5.08
% 16.01/8.94  BG Simplification    : 0.17
% 16.01/8.94  Subsumption          : 0.92
% 16.01/8.94  Abstraction          : 0.25
% 16.01/8.94  MUC search           : 0.00
% 16.01/8.94  Cooper               : 0.00
% 16.01/8.94  Total                : 8.17
% 16.01/8.94  Index Insertion      : 0.00
% 16.01/8.94  Index Deletion       : 0.00
% 16.01/8.94  Index Matching       : 0.00
% 16.01/8.94  BG Taut test         : 0.00
%------------------------------------------------------------------------------
