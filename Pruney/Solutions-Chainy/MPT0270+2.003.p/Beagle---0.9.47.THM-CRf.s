%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:53 EST 2020

% Result     : Theorem 11.39s
% Output     : CNFRefutation 11.68s
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
    ! [A_90,B_91] :
      ( r1_xboole_0(k1_tarski(A_90),B_91)
      | r2_hidden(A_90,B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_32,plain,(
    ! [B_31,A_30] : k2_tarski(B_31,A_30) = k2_tarski(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_235,plain,(
    ! [A_119,B_120] : k3_tarski(k2_tarski(A_119,B_120)) = k2_xboole_0(A_119,B_120) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_293,plain,(
    ! [A_129,B_130] : k3_tarski(k2_tarski(A_129,B_130)) = k2_xboole_0(B_130,A_129) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_235])).

tff(c_82,plain,(
    ! [A_92,B_93] : k3_tarski(k2_tarski(A_92,B_93)) = k2_xboole_0(A_92,B_93) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_299,plain,(
    ! [B_130,A_129] : k2_xboole_0(B_130,A_129) = k2_xboole_0(A_129,B_130) ),
    inference(superposition,[status(thm),theory(equality)],[c_293,c_82])).

tff(c_12,plain,(
    ! [A_10,B_11] : k5_xboole_0(A_10,k3_xboole_0(A_10,B_11)) = k4_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_26,plain,(
    ! [A_24,B_25,C_26] : k5_xboole_0(k5_xboole_0(A_24,B_25),C_26) = k5_xboole_0(A_24,k5_xboole_0(B_25,C_26)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1382,plain,(
    ! [A_185,B_186] : k5_xboole_0(k5_xboole_0(A_185,B_186),k2_xboole_0(A_185,B_186)) = k3_xboole_0(A_185,B_186) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_11930,plain,(
    ! [A_18758,B_18759] : k5_xboole_0(A_18758,k5_xboole_0(B_18759,k2_xboole_0(A_18758,B_18759))) = k3_xboole_0(A_18758,B_18759) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_1382])).

tff(c_84,plain,(
    ! [A_94] : k3_tarski(k1_tarski(A_94)) = A_94 ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_66,plain,(
    ! [A_62] : k2_tarski(A_62,A_62) = k1_tarski(A_62) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_250,plain,(
    ! [A_62] : k3_tarski(k1_tarski(A_62)) = k2_xboole_0(A_62,A_62) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_235])).

tff(c_253,plain,(
    ! [A_62] : k2_xboole_0(A_62,A_62) = A_62 ),
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
    ! [A_162,B_163,C_164] : k5_xboole_0(k5_xboole_0(A_162,B_163),C_164) = k5_xboole_0(A_162,k5_xboole_0(B_163,C_164)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_798,plain,(
    ! [A_27,C_164] : k5_xboole_0(A_27,k5_xboole_0(A_27,C_164)) = k5_xboole_0(k1_xboole_0,C_164) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_748])).

tff(c_1483,plain,(
    ! [A_27,C_164] : k5_xboole_0(A_27,k5_xboole_0(A_27,C_164)) = C_164 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1480,c_798])).

tff(c_11955,plain,(
    ! [B_18759,A_18758] : k5_xboole_0(B_18759,k2_xboole_0(A_18758,B_18759)) = k5_xboole_0(A_18758,k3_xboole_0(A_18758,B_18759)) ),
    inference(superposition,[status(thm),theory(equality)],[c_11930,c_1483])).

tff(c_12092,plain,(
    ! [B_18925,A_18926] : k5_xboole_0(B_18925,k2_xboole_0(A_18926,B_18925)) = k4_xboole_0(A_18926,B_18925) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_11955])).

tff(c_12197,plain,(
    ! [B_130,A_129] : k5_xboole_0(B_130,k2_xboole_0(B_130,A_129)) = k4_xboole_0(A_129,B_130) ),
    inference(superposition,[status(thm),theory(equality)],[c_299,c_12092])).

tff(c_494,plain,(
    ! [A_144,B_145] : k2_xboole_0(A_144,k2_xboole_0(A_144,B_145)) = k2_xboole_0(A_144,B_145) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_526,plain,(
    ! [B_130,A_129] : k2_xboole_0(B_130,k2_xboole_0(A_129,B_130)) = k2_xboole_0(B_130,A_129) ),
    inference(superposition,[status(thm),theory(equality)],[c_299,c_494])).

tff(c_13168,plain,(
    ! [B_21098,A_21099] : k5_xboole_0(B_21098,k2_xboole_0(B_21098,A_21099)) = k4_xboole_0(A_21099,B_21098) ),
    inference(superposition,[status(thm),theory(equality)],[c_299,c_12092])).

tff(c_13258,plain,(
    ! [B_130,A_129] : k5_xboole_0(B_130,k2_xboole_0(B_130,A_129)) = k4_xboole_0(k2_xboole_0(A_129,B_130),B_130) ),
    inference(superposition,[status(thm),theory(equality)],[c_526,c_13168])).

tff(c_13306,plain,(
    ! [A_129,B_130] : k4_xboole_0(k2_xboole_0(A_129,B_130),B_130) = k4_xboole_0(A_129,B_130) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12197,c_13258])).

tff(c_24,plain,(
    ! [A_22,B_23] :
      ( k4_xboole_0(k2_xboole_0(A_22,B_23),B_23) = A_22
      | ~ r1_xboole_0(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_17262,plain,(
    ! [A_24775,B_24776] :
      ( k4_xboole_0(A_24775,B_24776) = A_24775
      | ~ r1_xboole_0(A_24775,B_24776) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13306,c_24])).

tff(c_24679,plain,(
    ! [A_30801,B_30802] :
      ( k4_xboole_0(k1_tarski(A_30801),B_30802) = k1_tarski(A_30801)
      | r2_hidden(A_30801,B_30802) ) ),
    inference(resolution,[status(thm)],[c_80,c_17262])).

tff(c_86,plain,
    ( k4_xboole_0(k1_tarski('#skF_4'),'#skF_5') != k1_tarski('#skF_4')
    | r2_hidden('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_287,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),'#skF_5') != k1_tarski('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_24811,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_24679,c_287])).

tff(c_24886,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_172,c_24811])).

tff(c_24887,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_207,plain,(
    ! [A_115,B_116] : k1_enumset1(A_115,A_115,B_116) = k2_tarski(A_115,B_116) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_40,plain,(
    ! [E_38,B_33,C_34] : r2_hidden(E_38,k1_enumset1(E_38,B_33,C_34)) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_225,plain,(
    ! [A_117,B_118] : r2_hidden(A_117,k2_tarski(A_117,B_118)) ),
    inference(superposition,[status(thm),theory(equality)],[c_207,c_40])).

tff(c_234,plain,(
    ! [A_62] : r2_hidden(A_62,k1_tarski(A_62)) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_225])).

tff(c_24888,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),'#skF_5') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_90,plain,
    ( k4_xboole_0(k1_tarski('#skF_4'),'#skF_5') != k1_tarski('#skF_4')
    | k4_xboole_0(k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_25050,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24888,c_90])).

tff(c_22,plain,(
    ! [A_20,B_21] : r1_xboole_0(k4_xboole_0(A_20,B_21),B_21) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_25054,plain,(
    r1_xboole_0(k1_tarski('#skF_6'),'#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_25050,c_22])).

tff(c_25140,plain,(
    ! [A_30987,B_30988,C_30989] :
      ( ~ r1_xboole_0(A_30987,B_30988)
      | ~ r2_hidden(C_30989,B_30988)
      | ~ r2_hidden(C_30989,A_30987) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_25187,plain,(
    ! [C_30992] :
      ( ~ r2_hidden(C_30992,'#skF_7')
      | ~ r2_hidden(C_30992,k1_tarski('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_25054,c_25140])).

tff(c_25199,plain,(
    ~ r2_hidden('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_234,c_25187])).

tff(c_25205,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24887,c_25199])).

tff(c_25206,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_25242,plain,(
    ! [A_30998,B_30999] : k1_enumset1(A_30998,A_30998,B_30999) = k2_tarski(A_30998,B_30999) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_25298,plain,(
    ! [A_31003,B_31004] : r2_hidden(A_31003,k2_tarski(A_31003,B_31004)) ),
    inference(superposition,[status(thm),theory(equality)],[c_25242,c_40])).

tff(c_25307,plain,(
    ! [A_62] : r2_hidden(A_62,k1_tarski(A_62)) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_25298])).

tff(c_25207,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_92,plain,
    ( ~ r2_hidden('#skF_4','#skF_5')
    | k4_xboole_0(k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_25450,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_25207,c_92])).

tff(c_25454,plain,(
    r1_xboole_0(k1_tarski('#skF_6'),'#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_25450,c_22])).

tff(c_25591,plain,(
    ! [A_31029,B_31030,C_31031] :
      ( ~ r1_xboole_0(A_31029,B_31030)
      | ~ r2_hidden(C_31031,B_31030)
      | ~ r2_hidden(C_31031,A_31029) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_25661,plain,(
    ! [C_31038] :
      ( ~ r2_hidden(C_31038,'#skF_7')
      | ~ r2_hidden(C_31038,k1_tarski('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_25454,c_25591])).

tff(c_25673,plain,(
    ~ r2_hidden('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_25307,c_25661])).

tff(c_25679,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_25206,c_25673])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:43:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.39/4.71  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.39/4.72  
% 11.39/4.72  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.39/4.72  %$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 11.39/4.72  
% 11.39/4.72  %Foreground sorts:
% 11.39/4.72  
% 11.39/4.72  
% 11.39/4.72  %Background operators:
% 11.39/4.72  
% 11.39/4.72  
% 11.39/4.72  %Foreground operators:
% 11.39/4.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.39/4.72  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.39/4.72  tff(k1_tarski, type, k1_tarski: $i > $i).
% 11.39/4.72  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.39/4.72  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.39/4.72  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 11.39/4.72  tff('#skF_7', type, '#skF_7': $i).
% 11.39/4.72  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 11.39/4.72  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 11.39/4.72  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.39/4.72  tff('#skF_5', type, '#skF_5': $i).
% 11.39/4.72  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 11.39/4.72  tff('#skF_6', type, '#skF_6': $i).
% 11.39/4.72  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 11.39/4.72  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 11.39/4.72  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 11.39/4.72  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 11.39/4.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.39/4.72  tff(k3_tarski, type, k3_tarski: $i > $i).
% 11.39/4.72  tff('#skF_4', type, '#skF_4': $i).
% 11.39/4.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.39/4.72  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.39/4.72  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 11.39/4.72  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 11.39/4.72  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 11.39/4.72  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 11.39/4.72  
% 11.68/4.73  tff(f_123, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_zfmisc_1)).
% 11.68/4.73  tff(f_113, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 11.68/4.73  tff(f_71, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 11.68/4.73  tff(f_115, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 11.68/4.73  tff(f_49, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 11.68/4.73  tff(f_65, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 11.68/4.73  tff(f_69, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 11.68/4.73  tff(f_117, axiom, (![A]: (k3_tarski(k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 11.68/4.73  tff(f_96, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 11.68/4.73  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 11.68/4.73  tff(f_67, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 11.68/4.73  tff(f_57, axiom, (![A, B]: (k2_xboole_0(A, k2_xboole_0(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_xboole_1)).
% 11.68/4.73  tff(f_63, axiom, (![A, B]: (r1_xboole_0(A, B) => (k4_xboole_0(k2_xboole_0(A, B), B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_xboole_1)).
% 11.68/4.73  tff(f_98, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 11.68/4.73  tff(f_86, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 11.68/4.73  tff(f_59, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 11.68/4.73  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 11.68/4.73  tff(c_88, plain, (~r2_hidden('#skF_4', '#skF_5') | r2_hidden('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_123])).
% 11.68/4.73  tff(c_172, plain, (~r2_hidden('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_88])).
% 11.68/4.73  tff(c_80, plain, (![A_90, B_91]: (r1_xboole_0(k1_tarski(A_90), B_91) | r2_hidden(A_90, B_91))), inference(cnfTransformation, [status(thm)], [f_113])).
% 11.68/4.73  tff(c_32, plain, (![B_31, A_30]: (k2_tarski(B_31, A_30)=k2_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_71])).
% 11.68/4.73  tff(c_235, plain, (![A_119, B_120]: (k3_tarski(k2_tarski(A_119, B_120))=k2_xboole_0(A_119, B_120))), inference(cnfTransformation, [status(thm)], [f_115])).
% 11.68/4.73  tff(c_293, plain, (![A_129, B_130]: (k3_tarski(k2_tarski(A_129, B_130))=k2_xboole_0(B_130, A_129))), inference(superposition, [status(thm), theory('equality')], [c_32, c_235])).
% 11.68/4.73  tff(c_82, plain, (![A_92, B_93]: (k3_tarski(k2_tarski(A_92, B_93))=k2_xboole_0(A_92, B_93))), inference(cnfTransformation, [status(thm)], [f_115])).
% 11.68/4.73  tff(c_299, plain, (![B_130, A_129]: (k2_xboole_0(B_130, A_129)=k2_xboole_0(A_129, B_130))), inference(superposition, [status(thm), theory('equality')], [c_293, c_82])).
% 11.68/4.73  tff(c_12, plain, (![A_10, B_11]: (k5_xboole_0(A_10, k3_xboole_0(A_10, B_11))=k4_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_49])).
% 11.68/4.73  tff(c_26, plain, (![A_24, B_25, C_26]: (k5_xboole_0(k5_xboole_0(A_24, B_25), C_26)=k5_xboole_0(A_24, k5_xboole_0(B_25, C_26)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 11.68/4.73  tff(c_1382, plain, (![A_185, B_186]: (k5_xboole_0(k5_xboole_0(A_185, B_186), k2_xboole_0(A_185, B_186))=k3_xboole_0(A_185, B_186))), inference(cnfTransformation, [status(thm)], [f_69])).
% 11.68/4.73  tff(c_11930, plain, (![A_18758, B_18759]: (k5_xboole_0(A_18758, k5_xboole_0(B_18759, k2_xboole_0(A_18758, B_18759)))=k3_xboole_0(A_18758, B_18759))), inference(superposition, [status(thm), theory('equality')], [c_26, c_1382])).
% 11.68/4.73  tff(c_84, plain, (![A_94]: (k3_tarski(k1_tarski(A_94))=A_94)), inference(cnfTransformation, [status(thm)], [f_117])).
% 11.68/4.73  tff(c_66, plain, (![A_62]: (k2_tarski(A_62, A_62)=k1_tarski(A_62))), inference(cnfTransformation, [status(thm)], [f_96])).
% 11.68/4.73  tff(c_250, plain, (![A_62]: (k3_tarski(k1_tarski(A_62))=k2_xboole_0(A_62, A_62))), inference(superposition, [status(thm), theory('equality')], [c_66, c_235])).
% 11.68/4.73  tff(c_253, plain, (![A_62]: (k2_xboole_0(A_62, A_62)=A_62)), inference(demodulation, [status(thm), theory('equality')], [c_84, c_250])).
% 11.68/4.73  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 11.68/4.73  tff(c_28, plain, (![A_27]: (k5_xboole_0(A_27, A_27)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_67])).
% 11.68/4.73  tff(c_1473, plain, (![A_27]: (k5_xboole_0(k1_xboole_0, k2_xboole_0(A_27, A_27))=k3_xboole_0(A_27, A_27))), inference(superposition, [status(thm), theory('equality')], [c_28, c_1382])).
% 11.68/4.73  tff(c_1480, plain, (![A_27]: (k5_xboole_0(k1_xboole_0, A_27)=A_27)), inference(demodulation, [status(thm), theory('equality')], [c_253, c_4, c_1473])).
% 11.68/4.73  tff(c_748, plain, (![A_162, B_163, C_164]: (k5_xboole_0(k5_xboole_0(A_162, B_163), C_164)=k5_xboole_0(A_162, k5_xboole_0(B_163, C_164)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 11.68/4.73  tff(c_798, plain, (![A_27, C_164]: (k5_xboole_0(A_27, k5_xboole_0(A_27, C_164))=k5_xboole_0(k1_xboole_0, C_164))), inference(superposition, [status(thm), theory('equality')], [c_28, c_748])).
% 11.68/4.73  tff(c_1483, plain, (![A_27, C_164]: (k5_xboole_0(A_27, k5_xboole_0(A_27, C_164))=C_164)), inference(demodulation, [status(thm), theory('equality')], [c_1480, c_798])).
% 11.68/4.73  tff(c_11955, plain, (![B_18759, A_18758]: (k5_xboole_0(B_18759, k2_xboole_0(A_18758, B_18759))=k5_xboole_0(A_18758, k3_xboole_0(A_18758, B_18759)))), inference(superposition, [status(thm), theory('equality')], [c_11930, c_1483])).
% 11.68/4.73  tff(c_12092, plain, (![B_18925, A_18926]: (k5_xboole_0(B_18925, k2_xboole_0(A_18926, B_18925))=k4_xboole_0(A_18926, B_18925))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_11955])).
% 11.68/4.73  tff(c_12197, plain, (![B_130, A_129]: (k5_xboole_0(B_130, k2_xboole_0(B_130, A_129))=k4_xboole_0(A_129, B_130))), inference(superposition, [status(thm), theory('equality')], [c_299, c_12092])).
% 11.68/4.73  tff(c_494, plain, (![A_144, B_145]: (k2_xboole_0(A_144, k2_xboole_0(A_144, B_145))=k2_xboole_0(A_144, B_145))), inference(cnfTransformation, [status(thm)], [f_57])).
% 11.68/4.73  tff(c_526, plain, (![B_130, A_129]: (k2_xboole_0(B_130, k2_xboole_0(A_129, B_130))=k2_xboole_0(B_130, A_129))), inference(superposition, [status(thm), theory('equality')], [c_299, c_494])).
% 11.68/4.73  tff(c_13168, plain, (![B_21098, A_21099]: (k5_xboole_0(B_21098, k2_xboole_0(B_21098, A_21099))=k4_xboole_0(A_21099, B_21098))), inference(superposition, [status(thm), theory('equality')], [c_299, c_12092])).
% 11.68/4.73  tff(c_13258, plain, (![B_130, A_129]: (k5_xboole_0(B_130, k2_xboole_0(B_130, A_129))=k4_xboole_0(k2_xboole_0(A_129, B_130), B_130))), inference(superposition, [status(thm), theory('equality')], [c_526, c_13168])).
% 11.68/4.73  tff(c_13306, plain, (![A_129, B_130]: (k4_xboole_0(k2_xboole_0(A_129, B_130), B_130)=k4_xboole_0(A_129, B_130))), inference(demodulation, [status(thm), theory('equality')], [c_12197, c_13258])).
% 11.68/4.73  tff(c_24, plain, (![A_22, B_23]: (k4_xboole_0(k2_xboole_0(A_22, B_23), B_23)=A_22 | ~r1_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_63])).
% 11.68/4.73  tff(c_17262, plain, (![A_24775, B_24776]: (k4_xboole_0(A_24775, B_24776)=A_24775 | ~r1_xboole_0(A_24775, B_24776))), inference(demodulation, [status(thm), theory('equality')], [c_13306, c_24])).
% 11.68/4.73  tff(c_24679, plain, (![A_30801, B_30802]: (k4_xboole_0(k1_tarski(A_30801), B_30802)=k1_tarski(A_30801) | r2_hidden(A_30801, B_30802))), inference(resolution, [status(thm)], [c_80, c_17262])).
% 11.68/4.73  tff(c_86, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_5')!=k1_tarski('#skF_4') | r2_hidden('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_123])).
% 11.68/4.73  tff(c_287, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_5')!=k1_tarski('#skF_4')), inference(splitLeft, [status(thm)], [c_86])).
% 11.68/4.73  tff(c_24811, plain, (r2_hidden('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_24679, c_287])).
% 11.68/4.73  tff(c_24886, plain, $false, inference(negUnitSimplification, [status(thm)], [c_172, c_24811])).
% 11.68/4.73  tff(c_24887, plain, (r2_hidden('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_86])).
% 11.68/4.73  tff(c_207, plain, (![A_115, B_116]: (k1_enumset1(A_115, A_115, B_116)=k2_tarski(A_115, B_116))), inference(cnfTransformation, [status(thm)], [f_98])).
% 11.68/4.73  tff(c_40, plain, (![E_38, B_33, C_34]: (r2_hidden(E_38, k1_enumset1(E_38, B_33, C_34)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 11.68/4.73  tff(c_225, plain, (![A_117, B_118]: (r2_hidden(A_117, k2_tarski(A_117, B_118)))), inference(superposition, [status(thm), theory('equality')], [c_207, c_40])).
% 11.68/4.73  tff(c_234, plain, (![A_62]: (r2_hidden(A_62, k1_tarski(A_62)))), inference(superposition, [status(thm), theory('equality')], [c_66, c_225])).
% 11.68/4.73  tff(c_24888, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_5')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_86])).
% 11.68/4.73  tff(c_90, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_5')!=k1_tarski('#skF_4') | k4_xboole_0(k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_123])).
% 11.68/4.73  tff(c_25050, plain, (k4_xboole_0(k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_24888, c_90])).
% 11.68/4.73  tff(c_22, plain, (![A_20, B_21]: (r1_xboole_0(k4_xboole_0(A_20, B_21), B_21))), inference(cnfTransformation, [status(thm)], [f_59])).
% 11.68/4.73  tff(c_25054, plain, (r1_xboole_0(k1_tarski('#skF_6'), '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_25050, c_22])).
% 11.68/4.73  tff(c_25140, plain, (![A_30987, B_30988, C_30989]: (~r1_xboole_0(A_30987, B_30988) | ~r2_hidden(C_30989, B_30988) | ~r2_hidden(C_30989, A_30987))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.68/4.73  tff(c_25187, plain, (![C_30992]: (~r2_hidden(C_30992, '#skF_7') | ~r2_hidden(C_30992, k1_tarski('#skF_6')))), inference(resolution, [status(thm)], [c_25054, c_25140])).
% 11.68/4.73  tff(c_25199, plain, (~r2_hidden('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_234, c_25187])).
% 11.68/4.73  tff(c_25205, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24887, c_25199])).
% 11.68/4.73  tff(c_25206, plain, (r2_hidden('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_88])).
% 11.68/4.73  tff(c_25242, plain, (![A_30998, B_30999]: (k1_enumset1(A_30998, A_30998, B_30999)=k2_tarski(A_30998, B_30999))), inference(cnfTransformation, [status(thm)], [f_98])).
% 11.68/4.73  tff(c_25298, plain, (![A_31003, B_31004]: (r2_hidden(A_31003, k2_tarski(A_31003, B_31004)))), inference(superposition, [status(thm), theory('equality')], [c_25242, c_40])).
% 11.68/4.73  tff(c_25307, plain, (![A_62]: (r2_hidden(A_62, k1_tarski(A_62)))), inference(superposition, [status(thm), theory('equality')], [c_66, c_25298])).
% 11.68/4.73  tff(c_25207, plain, (r2_hidden('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_88])).
% 11.68/4.73  tff(c_92, plain, (~r2_hidden('#skF_4', '#skF_5') | k4_xboole_0(k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_123])).
% 11.68/4.73  tff(c_25450, plain, (k4_xboole_0(k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_25207, c_92])).
% 11.68/4.73  tff(c_25454, plain, (r1_xboole_0(k1_tarski('#skF_6'), '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_25450, c_22])).
% 11.68/4.73  tff(c_25591, plain, (![A_31029, B_31030, C_31031]: (~r1_xboole_0(A_31029, B_31030) | ~r2_hidden(C_31031, B_31030) | ~r2_hidden(C_31031, A_31029))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.68/4.73  tff(c_25661, plain, (![C_31038]: (~r2_hidden(C_31038, '#skF_7') | ~r2_hidden(C_31038, k1_tarski('#skF_6')))), inference(resolution, [status(thm)], [c_25454, c_25591])).
% 11.68/4.73  tff(c_25673, plain, (~r2_hidden('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_25307, c_25661])).
% 11.68/4.73  tff(c_25679, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_25206, c_25673])).
% 11.68/4.73  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.68/4.73  
% 11.68/4.73  Inference rules
% 11.68/4.73  ----------------------
% 11.68/4.73  #Ref     : 0
% 11.68/4.73  #Sup     : 5418
% 11.68/4.73  #Fact    : 18
% 11.68/4.73  #Define  : 0
% 11.68/4.73  #Split   : 2
% 11.68/4.73  #Chain   : 0
% 11.68/4.73  #Close   : 0
% 11.68/4.73  
% 11.68/4.73  Ordering : KBO
% 11.68/4.73  
% 11.68/4.73  Simplification rules
% 11.68/4.73  ----------------------
% 11.68/4.73  #Subsume      : 472
% 11.68/4.73  #Demod        : 5859
% 11.68/4.73  #Tautology    : 3032
% 11.68/4.74  #SimpNegUnit  : 17
% 11.68/4.74  #BackRed      : 7
% 11.68/4.74  
% 11.68/4.74  #Partial instantiations: 11592
% 11.68/4.74  #Strategies tried      : 1
% 11.68/4.74  
% 11.68/4.74  Timing (in seconds)
% 11.68/4.74  ----------------------
% 11.68/4.74  Preprocessing        : 0.39
% 11.68/4.74  Parsing              : 0.20
% 11.68/4.74  CNF conversion       : 0.03
% 11.68/4.74  Main loop            : 3.52
% 11.68/4.74  Inferencing          : 1.09
% 11.68/4.74  Reduction            : 1.71
% 11.68/4.74  Demodulation         : 1.52
% 11.68/4.74  BG Simplification    : 0.10
% 11.68/4.74  Subsumption          : 0.45
% 11.68/4.74  Abstraction          : 0.15
% 11.68/4.74  MUC search           : 0.00
% 11.68/4.74  Cooper               : 0.00
% 11.68/4.74  Total                : 3.95
% 11.68/4.74  Index Insertion      : 0.00
% 11.68/4.74  Index Deletion       : 0.00
% 11.68/4.74  Index Matching       : 0.00
% 11.68/4.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
