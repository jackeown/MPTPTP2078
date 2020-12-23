%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:53 EST 2020

% Result     : Theorem 11.40s
% Output     : CNFRefutation 11.62s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 183 expanded)
%              Number of leaves         :   43 (  78 expanded)
%              Depth                    :   14
%              Number of atoms          :  107 ( 203 expanded)
%              Number of equality atoms :   58 ( 131 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1

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

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_123,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
      <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_zfmisc_1)).

tff(f_113,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_71,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_115,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_65,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_117,axiom,(
    ! [A] : k3_tarski(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_zfmisc_1)).

tff(f_96,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_67,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] : k2_xboole_0(A,k2_xboole_0(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => k4_xboole_0(k2_xboole_0(A,B),B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_xboole_1)).

tff(f_98,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_86,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_59,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(c_88,plain,
    ( ~ r2_hidden('#skF_4','#skF_5')
    | r2_hidden('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_172,plain,(
    ~ r2_hidden('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_88])).

tff(c_80,plain,(
    ! [A_88,B_89] :
      ( r1_xboole_0(k1_tarski(A_88),B_89)
      | r2_hidden(A_88,B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_32,plain,(
    ! [B_31,A_30] : k2_tarski(B_31,A_30) = k2_tarski(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_235,plain,(
    ! [A_117,B_118] : k3_tarski(k2_tarski(A_117,B_118)) = k2_xboole_0(A_117,B_118) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_293,plain,(
    ! [A_127,B_128] : k3_tarski(k2_tarski(A_127,B_128)) = k2_xboole_0(B_128,A_127) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_235])).

tff(c_82,plain,(
    ! [A_90,B_91] : k3_tarski(k2_tarski(A_90,B_91)) = k2_xboole_0(A_90,B_91) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_299,plain,(
    ! [B_128,A_127] : k2_xboole_0(B_128,A_127) = k2_xboole_0(A_127,B_128) ),
    inference(superposition,[status(thm),theory(equality)],[c_293,c_82])).

tff(c_12,plain,(
    ! [A_10,B_11] : k5_xboole_0(A_10,k3_xboole_0(A_10,B_11)) = k4_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_26,plain,(
    ! [A_24,B_25,C_26] : k5_xboole_0(k5_xboole_0(A_24,B_25),C_26) = k5_xboole_0(A_24,k5_xboole_0(B_25,C_26)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1382,plain,(
    ! [A_183,B_184] : k5_xboole_0(k5_xboole_0(A_183,B_184),k2_xboole_0(A_183,B_184)) = k3_xboole_0(A_183,B_184) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_7803,plain,(
    ! [A_14569,B_14570] : k5_xboole_0(A_14569,k5_xboole_0(B_14570,k2_xboole_0(A_14569,B_14570))) = k3_xboole_0(A_14569,B_14570) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_1382])).

tff(c_84,plain,(
    ! [A_92] : k3_tarski(k1_tarski(A_92)) = A_92 ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_66,plain,(
    ! [A_60] : k2_tarski(A_60,A_60) = k1_tarski(A_60) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_250,plain,(
    ! [A_60] : k3_tarski(k1_tarski(A_60)) = k2_xboole_0(A_60,A_60) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_235])).

tff(c_253,plain,(
    ! [A_60] : k2_xboole_0(A_60,A_60) = A_60 ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_250])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_28,plain,(
    ! [A_27] : k5_xboole_0(A_27,A_27) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1473,plain,(
    ! [A_27] : k5_xboole_0(k1_xboole_0,k2_xboole_0(A_27,A_27)) = k3_xboole_0(A_27,A_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1382])).

tff(c_1480,plain,(
    ! [A_27] : k5_xboole_0(k1_xboole_0,A_27) = A_27 ),
    inference(demodulation,[status(thm),theory(equality)],[c_253,c_4,c_1473])).

tff(c_748,plain,(
    ! [A_160,B_161,C_162] : k5_xboole_0(k5_xboole_0(A_160,B_161),C_162) = k5_xboole_0(A_160,k5_xboole_0(B_161,C_162)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_798,plain,(
    ! [A_27,C_162] : k5_xboole_0(A_27,k5_xboole_0(A_27,C_162)) = k5_xboole_0(k1_xboole_0,C_162) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_748])).

tff(c_1483,plain,(
    ! [A_27,C_162] : k5_xboole_0(A_27,k5_xboole_0(A_27,C_162)) = C_162 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1480,c_798])).

tff(c_7818,plain,(
    ! [B_14570,A_14569] : k5_xboole_0(B_14570,k2_xboole_0(A_14569,B_14570)) = k5_xboole_0(A_14569,k3_xboole_0(A_14569,B_14570)) ),
    inference(superposition,[status(thm),theory(equality)],[c_7803,c_1483])).

tff(c_8825,plain,(
    ! [B_15740,A_15741] : k5_xboole_0(B_15740,k2_xboole_0(A_15741,B_15740)) = k4_xboole_0(A_15741,B_15740) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_7818])).

tff(c_8901,plain,(
    ! [B_128,A_127] : k5_xboole_0(B_128,k2_xboole_0(B_128,A_127)) = k4_xboole_0(A_127,B_128) ),
    inference(superposition,[status(thm),theory(equality)],[c_299,c_8825])).

tff(c_494,plain,(
    ! [A_142,B_143] : k2_xboole_0(A_142,k2_xboole_0(A_142,B_143)) = k2_xboole_0(A_142,B_143) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_526,plain,(
    ! [B_128,A_127] : k2_xboole_0(B_128,k2_xboole_0(A_127,B_128)) = k2_xboole_0(B_128,A_127) ),
    inference(superposition,[status(thm),theory(equality)],[c_299,c_494])).

tff(c_10186,plain,(
    ! [B_18247,A_18248] : k5_xboole_0(B_18247,k2_xboole_0(B_18247,A_18248)) = k4_xboole_0(A_18248,B_18247) ),
    inference(superposition,[status(thm),theory(equality)],[c_299,c_8825])).

tff(c_10253,plain,(
    ! [B_128,A_127] : k5_xboole_0(B_128,k2_xboole_0(B_128,A_127)) = k4_xboole_0(k2_xboole_0(A_127,B_128),B_128) ),
    inference(superposition,[status(thm),theory(equality)],[c_526,c_10186])).

tff(c_10298,plain,(
    ! [A_127,B_128] : k4_xboole_0(k2_xboole_0(A_127,B_128),B_128) = k4_xboole_0(A_127,B_128) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8901,c_10253])).

tff(c_24,plain,(
    ! [A_22,B_23] :
      ( k4_xboole_0(k2_xboole_0(A_22,B_23),B_23) = A_22
      | ~ r1_xboole_0(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_14775,plain,(
    ! [A_22759,B_22760] :
      ( k4_xboole_0(A_22759,B_22760) = A_22759
      | ~ r1_xboole_0(A_22759,B_22760) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10298,c_24])).

tff(c_25476,plain,(
    ! [A_31135,B_31136] :
      ( k4_xboole_0(k1_tarski(A_31135),B_31136) = k1_tarski(A_31135)
      | r2_hidden(A_31135,B_31136) ) ),
    inference(resolution,[status(thm)],[c_80,c_14775])).

tff(c_86,plain,
    ( k4_xboole_0(k1_tarski('#skF_4'),'#skF_5') != k1_tarski('#skF_4')
    | r2_hidden('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_287,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),'#skF_5') != k1_tarski('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_25608,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_25476,c_287])).

tff(c_25683,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_172,c_25608])).

tff(c_25684,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_207,plain,(
    ! [A_113,B_114] : k1_enumset1(A_113,A_113,B_114) = k2_tarski(A_113,B_114) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_40,plain,(
    ! [E_38,B_33,C_34] : r2_hidden(E_38,k1_enumset1(E_38,B_33,C_34)) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_225,plain,(
    ! [A_115,B_116] : r2_hidden(A_115,k2_tarski(A_115,B_116)) ),
    inference(superposition,[status(thm),theory(equality)],[c_207,c_40])).

tff(c_234,plain,(
    ! [A_60] : r2_hidden(A_60,k1_tarski(A_60)) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_225])).

tff(c_25685,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),'#skF_5') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_90,plain,
    ( k4_xboole_0(k1_tarski('#skF_4'),'#skF_5') != k1_tarski('#skF_4')
    | k4_xboole_0(k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_25820,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_25685,c_90])).

tff(c_22,plain,(
    ! [A_20,B_21] : r1_xboole_0(k4_xboole_0(A_20,B_21),B_21) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_25824,plain,(
    r1_xboole_0(k1_tarski('#skF_6'),'#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_25820,c_22])).

tff(c_25965,plain,(
    ! [A_31323,B_31324,C_31325] :
      ( ~ r1_xboole_0(A_31323,B_31324)
      | ~ r2_hidden(C_31325,B_31324)
      | ~ r2_hidden(C_31325,A_31323) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_26050,plain,(
    ! [C_31333] :
      ( ~ r2_hidden(C_31333,'#skF_7')
      | ~ r2_hidden(C_31333,k1_tarski('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_25824,c_25965])).

tff(c_26062,plain,(
    ~ r2_hidden('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_234,c_26050])).

tff(c_26068,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_25684,c_26062])).

tff(c_26069,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_26107,plain,(
    ! [A_31341,B_31342] : k1_enumset1(A_31341,A_31341,B_31342) = k2_tarski(A_31341,B_31342) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_26163,plain,(
    ! [A_31346,B_31347] : r2_hidden(A_31346,k2_tarski(A_31346,B_31347)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26107,c_40])).

tff(c_26172,plain,(
    ! [A_60] : r2_hidden(A_60,k1_tarski(A_60)) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_26163])).

tff(c_26070,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_92,plain,
    ( ~ r2_hidden('#skF_4','#skF_5')
    | k4_xboole_0(k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_26175,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26070,c_92])).

tff(c_26179,plain,(
    r1_xboole_0(k1_tarski('#skF_6'),'#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_26175,c_22])).

tff(c_26611,plain,(
    ! [A_31378,B_31379,C_31380] :
      ( ~ r1_xboole_0(A_31378,B_31379)
      | ~ r2_hidden(C_31380,B_31379)
      | ~ r2_hidden(C_31380,A_31378) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_26834,plain,(
    ! [C_31389] :
      ( ~ r2_hidden(C_31389,'#skF_7')
      | ~ r2_hidden(C_31389,k1_tarski('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_26179,c_26611])).

tff(c_26846,plain,(
    ~ r2_hidden('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_26172,c_26834])).

tff(c_26852,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26069,c_26846])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:10:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.40/4.60  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.40/4.61  
% 11.40/4.61  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.40/4.61  %$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 11.40/4.61  
% 11.40/4.61  %Foreground sorts:
% 11.40/4.61  
% 11.40/4.61  
% 11.40/4.61  %Background operators:
% 11.40/4.61  
% 11.40/4.61  
% 11.40/4.61  %Foreground operators:
% 11.40/4.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.40/4.61  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.40/4.61  tff(k1_tarski, type, k1_tarski: $i > $i).
% 11.40/4.61  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.40/4.61  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.40/4.61  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 11.40/4.61  tff('#skF_7', type, '#skF_7': $i).
% 11.40/4.61  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 11.40/4.61  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 11.40/4.61  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.40/4.61  tff('#skF_5', type, '#skF_5': $i).
% 11.40/4.61  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 11.40/4.61  tff('#skF_6', type, '#skF_6': $i).
% 11.40/4.61  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 11.40/4.61  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 11.40/4.61  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 11.40/4.61  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 11.40/4.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.40/4.61  tff(k3_tarski, type, k3_tarski: $i > $i).
% 11.40/4.61  tff('#skF_4', type, '#skF_4': $i).
% 11.40/4.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.40/4.61  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.40/4.61  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 11.40/4.61  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 11.40/4.61  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 11.40/4.61  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 11.40/4.61  
% 11.62/4.63  tff(f_123, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_zfmisc_1)).
% 11.62/4.63  tff(f_113, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 11.62/4.63  tff(f_71, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 11.62/4.63  tff(f_115, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 11.62/4.63  tff(f_49, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 11.62/4.63  tff(f_65, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 11.62/4.63  tff(f_69, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 11.62/4.63  tff(f_117, axiom, (![A]: (k3_tarski(k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 11.62/4.63  tff(f_96, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 11.62/4.63  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 11.62/4.63  tff(f_67, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 11.62/4.63  tff(f_57, axiom, (![A, B]: (k2_xboole_0(A, k2_xboole_0(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_xboole_1)).
% 11.62/4.63  tff(f_63, axiom, (![A, B]: (r1_xboole_0(A, B) => (k4_xboole_0(k2_xboole_0(A, B), B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_xboole_1)).
% 11.62/4.63  tff(f_98, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 11.62/4.63  tff(f_86, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 11.62/4.63  tff(f_59, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 11.62/4.63  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 11.62/4.63  tff(c_88, plain, (~r2_hidden('#skF_4', '#skF_5') | r2_hidden('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_123])).
% 11.62/4.63  tff(c_172, plain, (~r2_hidden('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_88])).
% 11.62/4.63  tff(c_80, plain, (![A_88, B_89]: (r1_xboole_0(k1_tarski(A_88), B_89) | r2_hidden(A_88, B_89))), inference(cnfTransformation, [status(thm)], [f_113])).
% 11.62/4.63  tff(c_32, plain, (![B_31, A_30]: (k2_tarski(B_31, A_30)=k2_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_71])).
% 11.62/4.63  tff(c_235, plain, (![A_117, B_118]: (k3_tarski(k2_tarski(A_117, B_118))=k2_xboole_0(A_117, B_118))), inference(cnfTransformation, [status(thm)], [f_115])).
% 11.62/4.63  tff(c_293, plain, (![A_127, B_128]: (k3_tarski(k2_tarski(A_127, B_128))=k2_xboole_0(B_128, A_127))), inference(superposition, [status(thm), theory('equality')], [c_32, c_235])).
% 11.62/4.63  tff(c_82, plain, (![A_90, B_91]: (k3_tarski(k2_tarski(A_90, B_91))=k2_xboole_0(A_90, B_91))), inference(cnfTransformation, [status(thm)], [f_115])).
% 11.62/4.63  tff(c_299, plain, (![B_128, A_127]: (k2_xboole_0(B_128, A_127)=k2_xboole_0(A_127, B_128))), inference(superposition, [status(thm), theory('equality')], [c_293, c_82])).
% 11.62/4.63  tff(c_12, plain, (![A_10, B_11]: (k5_xboole_0(A_10, k3_xboole_0(A_10, B_11))=k4_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_49])).
% 11.62/4.63  tff(c_26, plain, (![A_24, B_25, C_26]: (k5_xboole_0(k5_xboole_0(A_24, B_25), C_26)=k5_xboole_0(A_24, k5_xboole_0(B_25, C_26)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 11.62/4.63  tff(c_1382, plain, (![A_183, B_184]: (k5_xboole_0(k5_xboole_0(A_183, B_184), k2_xboole_0(A_183, B_184))=k3_xboole_0(A_183, B_184))), inference(cnfTransformation, [status(thm)], [f_69])).
% 11.62/4.63  tff(c_7803, plain, (![A_14569, B_14570]: (k5_xboole_0(A_14569, k5_xboole_0(B_14570, k2_xboole_0(A_14569, B_14570)))=k3_xboole_0(A_14569, B_14570))), inference(superposition, [status(thm), theory('equality')], [c_26, c_1382])).
% 11.62/4.63  tff(c_84, plain, (![A_92]: (k3_tarski(k1_tarski(A_92))=A_92)), inference(cnfTransformation, [status(thm)], [f_117])).
% 11.62/4.63  tff(c_66, plain, (![A_60]: (k2_tarski(A_60, A_60)=k1_tarski(A_60))), inference(cnfTransformation, [status(thm)], [f_96])).
% 11.62/4.63  tff(c_250, plain, (![A_60]: (k3_tarski(k1_tarski(A_60))=k2_xboole_0(A_60, A_60))), inference(superposition, [status(thm), theory('equality')], [c_66, c_235])).
% 11.62/4.63  tff(c_253, plain, (![A_60]: (k2_xboole_0(A_60, A_60)=A_60)), inference(demodulation, [status(thm), theory('equality')], [c_84, c_250])).
% 11.62/4.63  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 11.62/4.63  tff(c_28, plain, (![A_27]: (k5_xboole_0(A_27, A_27)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_67])).
% 11.62/4.63  tff(c_1473, plain, (![A_27]: (k5_xboole_0(k1_xboole_0, k2_xboole_0(A_27, A_27))=k3_xboole_0(A_27, A_27))), inference(superposition, [status(thm), theory('equality')], [c_28, c_1382])).
% 11.62/4.63  tff(c_1480, plain, (![A_27]: (k5_xboole_0(k1_xboole_0, A_27)=A_27)), inference(demodulation, [status(thm), theory('equality')], [c_253, c_4, c_1473])).
% 11.62/4.63  tff(c_748, plain, (![A_160, B_161, C_162]: (k5_xboole_0(k5_xboole_0(A_160, B_161), C_162)=k5_xboole_0(A_160, k5_xboole_0(B_161, C_162)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 11.62/4.63  tff(c_798, plain, (![A_27, C_162]: (k5_xboole_0(A_27, k5_xboole_0(A_27, C_162))=k5_xboole_0(k1_xboole_0, C_162))), inference(superposition, [status(thm), theory('equality')], [c_28, c_748])).
% 11.62/4.63  tff(c_1483, plain, (![A_27, C_162]: (k5_xboole_0(A_27, k5_xboole_0(A_27, C_162))=C_162)), inference(demodulation, [status(thm), theory('equality')], [c_1480, c_798])).
% 11.62/4.63  tff(c_7818, plain, (![B_14570, A_14569]: (k5_xboole_0(B_14570, k2_xboole_0(A_14569, B_14570))=k5_xboole_0(A_14569, k3_xboole_0(A_14569, B_14570)))), inference(superposition, [status(thm), theory('equality')], [c_7803, c_1483])).
% 11.62/4.63  tff(c_8825, plain, (![B_15740, A_15741]: (k5_xboole_0(B_15740, k2_xboole_0(A_15741, B_15740))=k4_xboole_0(A_15741, B_15740))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_7818])).
% 11.62/4.63  tff(c_8901, plain, (![B_128, A_127]: (k5_xboole_0(B_128, k2_xboole_0(B_128, A_127))=k4_xboole_0(A_127, B_128))), inference(superposition, [status(thm), theory('equality')], [c_299, c_8825])).
% 11.62/4.63  tff(c_494, plain, (![A_142, B_143]: (k2_xboole_0(A_142, k2_xboole_0(A_142, B_143))=k2_xboole_0(A_142, B_143))), inference(cnfTransformation, [status(thm)], [f_57])).
% 11.62/4.63  tff(c_526, plain, (![B_128, A_127]: (k2_xboole_0(B_128, k2_xboole_0(A_127, B_128))=k2_xboole_0(B_128, A_127))), inference(superposition, [status(thm), theory('equality')], [c_299, c_494])).
% 11.62/4.63  tff(c_10186, plain, (![B_18247, A_18248]: (k5_xboole_0(B_18247, k2_xboole_0(B_18247, A_18248))=k4_xboole_0(A_18248, B_18247))), inference(superposition, [status(thm), theory('equality')], [c_299, c_8825])).
% 11.62/4.63  tff(c_10253, plain, (![B_128, A_127]: (k5_xboole_0(B_128, k2_xboole_0(B_128, A_127))=k4_xboole_0(k2_xboole_0(A_127, B_128), B_128))), inference(superposition, [status(thm), theory('equality')], [c_526, c_10186])).
% 11.62/4.63  tff(c_10298, plain, (![A_127, B_128]: (k4_xboole_0(k2_xboole_0(A_127, B_128), B_128)=k4_xboole_0(A_127, B_128))), inference(demodulation, [status(thm), theory('equality')], [c_8901, c_10253])).
% 11.62/4.63  tff(c_24, plain, (![A_22, B_23]: (k4_xboole_0(k2_xboole_0(A_22, B_23), B_23)=A_22 | ~r1_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_63])).
% 11.62/4.63  tff(c_14775, plain, (![A_22759, B_22760]: (k4_xboole_0(A_22759, B_22760)=A_22759 | ~r1_xboole_0(A_22759, B_22760))), inference(demodulation, [status(thm), theory('equality')], [c_10298, c_24])).
% 11.62/4.63  tff(c_25476, plain, (![A_31135, B_31136]: (k4_xboole_0(k1_tarski(A_31135), B_31136)=k1_tarski(A_31135) | r2_hidden(A_31135, B_31136))), inference(resolution, [status(thm)], [c_80, c_14775])).
% 11.62/4.63  tff(c_86, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_5')!=k1_tarski('#skF_4') | r2_hidden('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_123])).
% 11.62/4.63  tff(c_287, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_5')!=k1_tarski('#skF_4')), inference(splitLeft, [status(thm)], [c_86])).
% 11.62/4.63  tff(c_25608, plain, (r2_hidden('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_25476, c_287])).
% 11.62/4.63  tff(c_25683, plain, $false, inference(negUnitSimplification, [status(thm)], [c_172, c_25608])).
% 11.62/4.63  tff(c_25684, plain, (r2_hidden('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_86])).
% 11.62/4.63  tff(c_207, plain, (![A_113, B_114]: (k1_enumset1(A_113, A_113, B_114)=k2_tarski(A_113, B_114))), inference(cnfTransformation, [status(thm)], [f_98])).
% 11.62/4.63  tff(c_40, plain, (![E_38, B_33, C_34]: (r2_hidden(E_38, k1_enumset1(E_38, B_33, C_34)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 11.62/4.63  tff(c_225, plain, (![A_115, B_116]: (r2_hidden(A_115, k2_tarski(A_115, B_116)))), inference(superposition, [status(thm), theory('equality')], [c_207, c_40])).
% 11.62/4.63  tff(c_234, plain, (![A_60]: (r2_hidden(A_60, k1_tarski(A_60)))), inference(superposition, [status(thm), theory('equality')], [c_66, c_225])).
% 11.62/4.63  tff(c_25685, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_5')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_86])).
% 11.62/4.63  tff(c_90, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_5')!=k1_tarski('#skF_4') | k4_xboole_0(k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_123])).
% 11.62/4.63  tff(c_25820, plain, (k4_xboole_0(k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_25685, c_90])).
% 11.62/4.63  tff(c_22, plain, (![A_20, B_21]: (r1_xboole_0(k4_xboole_0(A_20, B_21), B_21))), inference(cnfTransformation, [status(thm)], [f_59])).
% 11.62/4.63  tff(c_25824, plain, (r1_xboole_0(k1_tarski('#skF_6'), '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_25820, c_22])).
% 11.62/4.63  tff(c_25965, plain, (![A_31323, B_31324, C_31325]: (~r1_xboole_0(A_31323, B_31324) | ~r2_hidden(C_31325, B_31324) | ~r2_hidden(C_31325, A_31323))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.62/4.63  tff(c_26050, plain, (![C_31333]: (~r2_hidden(C_31333, '#skF_7') | ~r2_hidden(C_31333, k1_tarski('#skF_6')))), inference(resolution, [status(thm)], [c_25824, c_25965])).
% 11.62/4.63  tff(c_26062, plain, (~r2_hidden('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_234, c_26050])).
% 11.62/4.63  tff(c_26068, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_25684, c_26062])).
% 11.62/4.63  tff(c_26069, plain, (r2_hidden('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_88])).
% 11.62/4.63  tff(c_26107, plain, (![A_31341, B_31342]: (k1_enumset1(A_31341, A_31341, B_31342)=k2_tarski(A_31341, B_31342))), inference(cnfTransformation, [status(thm)], [f_98])).
% 11.62/4.63  tff(c_26163, plain, (![A_31346, B_31347]: (r2_hidden(A_31346, k2_tarski(A_31346, B_31347)))), inference(superposition, [status(thm), theory('equality')], [c_26107, c_40])).
% 11.62/4.63  tff(c_26172, plain, (![A_60]: (r2_hidden(A_60, k1_tarski(A_60)))), inference(superposition, [status(thm), theory('equality')], [c_66, c_26163])).
% 11.62/4.63  tff(c_26070, plain, (r2_hidden('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_88])).
% 11.62/4.63  tff(c_92, plain, (~r2_hidden('#skF_4', '#skF_5') | k4_xboole_0(k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_123])).
% 11.62/4.63  tff(c_26175, plain, (k4_xboole_0(k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_26070, c_92])).
% 11.62/4.63  tff(c_26179, plain, (r1_xboole_0(k1_tarski('#skF_6'), '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_26175, c_22])).
% 11.62/4.63  tff(c_26611, plain, (![A_31378, B_31379, C_31380]: (~r1_xboole_0(A_31378, B_31379) | ~r2_hidden(C_31380, B_31379) | ~r2_hidden(C_31380, A_31378))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.62/4.63  tff(c_26834, plain, (![C_31389]: (~r2_hidden(C_31389, '#skF_7') | ~r2_hidden(C_31389, k1_tarski('#skF_6')))), inference(resolution, [status(thm)], [c_26179, c_26611])).
% 11.62/4.63  tff(c_26846, plain, (~r2_hidden('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_26172, c_26834])).
% 11.62/4.63  tff(c_26852, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26069, c_26846])).
% 11.62/4.63  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.62/4.63  
% 11.62/4.63  Inference rules
% 11.62/4.63  ----------------------
% 11.62/4.63  #Ref     : 0
% 11.62/4.63  #Sup     : 5715
% 11.62/4.63  #Fact    : 18
% 11.62/4.63  #Define  : 0
% 11.62/4.63  #Split   : 2
% 11.62/4.63  #Chain   : 0
% 11.62/4.63  #Close   : 0
% 11.62/4.63  
% 11.62/4.63  Ordering : KBO
% 11.62/4.63  
% 11.62/4.63  Simplification rules
% 11.62/4.63  ----------------------
% 11.62/4.63  #Subsume      : 497
% 11.62/4.63  #Demod        : 6373
% 11.62/4.63  #Tautology    : 3164
% 11.62/4.63  #SimpNegUnit  : 17
% 11.62/4.63  #BackRed      : 7
% 11.62/4.63  
% 11.62/4.63  #Partial instantiations: 11718
% 11.62/4.63  #Strategies tried      : 1
% 11.62/4.63  
% 11.62/4.63  Timing (in seconds)
% 11.62/4.63  ----------------------
% 11.62/4.64  Preprocessing        : 0.37
% 11.62/4.64  Parsing              : 0.20
% 11.62/4.64  CNF conversion       : 0.03
% 11.62/4.64  Main loop            : 3.47
% 11.62/4.64  Inferencing          : 1.04
% 11.62/4.64  Reduction            : 1.72
% 11.62/4.64  Demodulation         : 1.54
% 11.62/4.64  BG Simplification    : 0.10
% 11.62/4.64  Subsumption          : 0.44
% 11.62/4.64  Abstraction          : 0.16
% 11.62/4.64  MUC search           : 0.00
% 11.62/4.64  Cooper               : 0.00
% 11.62/4.64  Total                : 3.88
% 11.62/4.64  Index Insertion      : 0.00
% 11.62/4.64  Index Deletion       : 0.00
% 11.62/4.64  Index Matching       : 0.00
% 11.62/4.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
