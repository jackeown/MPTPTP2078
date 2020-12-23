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
% DateTime   : Thu Dec  3 09:52:56 EST 2020

% Result     : Theorem 9.08s
% Output     : CNFRefutation 9.08s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 319 expanded)
%              Number of leaves         :   34 ( 118 expanded)
%              Depth                    :   12
%              Number of atoms          :  155 ( 512 expanded)
%              Number of equality atoms :   79 ( 236 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(f_60,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_66,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_54,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_70,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_89,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
      <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_zfmisc_1)).

tff(f_68,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_62,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(c_46,plain,(
    ! [B_18] : r1_tarski(B_18,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_9290,plain,(
    ! [A_394,B_395] :
      ( k3_xboole_0(A_394,B_395) = A_394
      | ~ r1_tarski(A_394,B_395) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_9298,plain,(
    ! [B_18] : k3_xboole_0(B_18,B_18) = B_18 ),
    inference(resolution,[status(thm)],[c_46,c_9290])).

tff(c_40,plain,(
    ! [A_15] :
      ( r2_hidden('#skF_5'(A_15),A_15)
      | k1_xboole_0 = A_15 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_9371,plain,(
    ! [D_409,A_410,B_411] :
      ( r2_hidden(D_409,A_410)
      | ~ r2_hidden(D_409,k4_xboole_0(A_410,B_411)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_14027,plain,(
    ! [A_555,B_556] :
      ( r2_hidden('#skF_5'(k4_xboole_0(A_555,B_556)),A_555)
      | k4_xboole_0(A_555,B_556) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_40,c_9371])).

tff(c_9377,plain,(
    ! [D_412,B_413,A_414] :
      ( ~ r2_hidden(D_412,B_413)
      | ~ r2_hidden(D_412,k4_xboole_0(A_414,B_413)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_9382,plain,(
    ! [A_414,B_413] :
      ( ~ r2_hidden('#skF_5'(k4_xboole_0(A_414,B_413)),B_413)
      | k4_xboole_0(A_414,B_413) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_40,c_9377])).

tff(c_14080,plain,(
    ! [A_557] : k4_xboole_0(A_557,A_557) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14027,c_9382])).

tff(c_54,plain,(
    ! [A_25,B_26] : k4_xboole_0(A_25,k4_xboole_0(A_25,B_26)) = k3_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_14113,plain,(
    ! [A_557] : k4_xboole_0(A_557,k1_xboole_0) = k3_xboole_0(A_557,A_557) ),
    inference(superposition,[status(thm),theory(equality)],[c_14080,c_54])).

tff(c_14145,plain,(
    ! [A_557] : k4_xboole_0(A_557,k1_xboole_0) = A_557 ),
    inference(demodulation,[status(thm),theory(equality)],[c_9298,c_14113])).

tff(c_70,plain,
    ( ~ r2_hidden('#skF_6','#skF_7')
    | r2_hidden('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_87,plain,(
    ~ r2_hidden('#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_122,plain,(
    ! [A_46,B_47] :
      ( k3_xboole_0(A_46,B_47) = A_46
      | ~ r1_tarski(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_130,plain,(
    ! [B_18] : k3_xboole_0(B_18,B_18) = B_18 ),
    inference(resolution,[status(thm)],[c_46,c_122])).

tff(c_248,plain,(
    ! [D_64,A_65,B_66] :
      ( r2_hidden(D_64,A_65)
      | ~ r2_hidden(D_64,k4_xboole_0(A_65,B_66)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_259,plain,(
    ! [A_65,B_66] :
      ( r2_hidden('#skF_5'(k4_xboole_0(A_65,B_66)),A_65)
      | k4_xboole_0(A_65,B_66) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_40,c_248])).

tff(c_307,plain,(
    ! [D_75,B_76,A_77] :
      ( ~ r2_hidden(D_75,B_76)
      | ~ r2_hidden(D_75,k4_xboole_0(A_77,B_76)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2808,plain,(
    ! [A_189,B_190] :
      ( ~ r2_hidden('#skF_5'(k4_xboole_0(A_189,B_190)),B_190)
      | k4_xboole_0(A_189,B_190) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_40,c_307])).

tff(c_2846,plain,(
    ! [A_191] : k4_xboole_0(A_191,A_191) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_259,c_2808])).

tff(c_52,plain,(
    ! [A_23,B_24] : r1_tarski(k4_xboole_0(A_23,B_24),A_23) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_351,plain,(
    ! [A_80,B_81] : k3_xboole_0(k4_xboole_0(A_80,B_81),A_80) = k4_xboole_0(A_80,B_81) ),
    inference(resolution,[status(thm)],[c_52,c_122])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_265,plain,(
    ! [A_69,B_70] : k5_xboole_0(A_69,k3_xboole_0(A_69,B_70)) = k4_xboole_0(A_69,B_70) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_280,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_265])).

tff(c_357,plain,(
    ! [A_80,B_81] : k5_xboole_0(A_80,k4_xboole_0(A_80,B_81)) = k4_xboole_0(A_80,k4_xboole_0(A_80,B_81)) ),
    inference(superposition,[status(thm),theory(equality)],[c_351,c_280])).

tff(c_397,plain,(
    ! [A_80,B_81] : k5_xboole_0(A_80,k4_xboole_0(A_80,B_81)) = k3_xboole_0(A_80,B_81) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_357])).

tff(c_2869,plain,(
    ! [A_191] : k5_xboole_0(A_191,k1_xboole_0) = k3_xboole_0(A_191,A_191) ),
    inference(superposition,[status(thm),theory(equality)],[c_2846,c_397])).

tff(c_2905,plain,(
    ! [A_191] : k5_xboole_0(A_191,k1_xboole_0) = A_191 ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_2869])).

tff(c_2836,plain,(
    ! [A_65] : k4_xboole_0(A_65,A_65) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_259,c_2808])).

tff(c_232,plain,(
    ! [A_62,B_63] :
      ( k4_xboole_0(A_62,k1_tarski(B_63)) = A_62
      | r2_hidden(B_63,A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_238,plain,(
    ! [A_62,B_63] :
      ( k4_xboole_0(A_62,A_62) = k3_xboole_0(A_62,k1_tarski(B_63))
      | r2_hidden(B_63,A_62) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_232,c_54])).

tff(c_4313,plain,(
    ! [A_226,B_227] :
      ( k3_xboole_0(A_226,k1_tarski(B_227)) = k1_xboole_0
      | r2_hidden(B_227,A_226) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2836,c_238])).

tff(c_4406,plain,(
    ! [B_227,A_226] :
      ( k5_xboole_0(k1_tarski(B_227),k1_xboole_0) = k4_xboole_0(k1_tarski(B_227),A_226)
      | r2_hidden(B_227,A_226) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4313,c_280])).

tff(c_5210,plain,(
    ! [B_242,A_243] :
      ( k4_xboole_0(k1_tarski(B_242),A_243) = k1_tarski(B_242)
      | r2_hidden(B_242,A_243) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2905,c_4406])).

tff(c_68,plain,
    ( k4_xboole_0(k1_tarski('#skF_6'),'#skF_7') != k1_tarski('#skF_6')
    | r2_hidden('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_140,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),'#skF_7') != k1_tarski('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_5288,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_5210,c_140])).

tff(c_5333,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_5288])).

tff(c_5334,plain,(
    r2_hidden('#skF_8','#skF_9') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_5438,plain,(
    ! [D_258,A_259,B_260] :
      ( r2_hidden(D_258,A_259)
      | ~ r2_hidden(D_258,k4_xboole_0(A_259,B_260)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_5449,plain,(
    ! [A_259,B_260] :
      ( r2_hidden('#skF_5'(k4_xboole_0(A_259,B_260)),A_259)
      | k4_xboole_0(A_259,B_260) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_40,c_5438])).

tff(c_5490,plain,(
    ! [D_267,B_268,A_269] :
      ( ~ r2_hidden(D_267,B_268)
      | ~ r2_hidden(D_267,k4_xboole_0(A_269,B_268)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_7806,plain,(
    ! [A_351,B_352] :
      ( ~ r2_hidden('#skF_5'(k4_xboole_0(A_351,B_352)),B_352)
      | k4_xboole_0(A_351,B_352) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_40,c_5490])).

tff(c_7864,plain,(
    ! [A_353] : k4_xboole_0(A_353,A_353) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_5449,c_7806])).

tff(c_129,plain,(
    ! [A_23,B_24] : k3_xboole_0(k4_xboole_0(A_23,B_24),A_23) = k4_xboole_0(A_23,B_24) ),
    inference(resolution,[status(thm)],[c_52,c_122])).

tff(c_5511,plain,(
    ! [A_271,B_272] : k5_xboole_0(A_271,k3_xboole_0(A_271,B_272)) = k4_xboole_0(A_271,B_272) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_5620,plain,(
    ! [B_277,A_278] : k5_xboole_0(B_277,k3_xboole_0(A_278,B_277)) = k4_xboole_0(B_277,A_278) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_5511])).

tff(c_5633,plain,(
    ! [A_23,B_24] : k5_xboole_0(A_23,k4_xboole_0(A_23,B_24)) = k4_xboole_0(A_23,k4_xboole_0(A_23,B_24)) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_5620])).

tff(c_5650,plain,(
    ! [A_23,B_24] : k5_xboole_0(A_23,k4_xboole_0(A_23,B_24)) = k3_xboole_0(A_23,B_24) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_5633])).

tff(c_7881,plain,(
    ! [A_353] : k5_xboole_0(A_353,k1_xboole_0) = k3_xboole_0(A_353,A_353) ),
    inference(superposition,[status(thm),theory(equality)],[c_7864,c_5650])).

tff(c_7918,plain,(
    ! [A_353] : k5_xboole_0(A_353,k1_xboole_0) = A_353 ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_7881])).

tff(c_7849,plain,(
    ! [A_259] : k4_xboole_0(A_259,A_259) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_5449,c_7806])).

tff(c_5335,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_6') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_72,plain,
    ( k4_xboole_0(k1_tarski('#skF_6'),'#skF_7') != k1_tarski('#skF_6')
    | k4_xboole_0(k1_tarski('#skF_8'),'#skF_9') = k1_tarski('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_5539,plain,(
    k4_xboole_0(k1_tarski('#skF_8'),'#skF_9') = k1_tarski('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5335,c_72])).

tff(c_5549,plain,(
    k4_xboole_0(k1_tarski('#skF_8'),k1_tarski('#skF_8')) = k3_xboole_0(k1_tarski('#skF_8'),'#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_5539,c_54])).

tff(c_5555,plain,(
    k4_xboole_0(k1_tarski('#skF_8'),k1_tarski('#skF_8')) = k3_xboole_0('#skF_9',k1_tarski('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_5549])).

tff(c_7862,plain,(
    k3_xboole_0('#skF_9',k1_tarski('#skF_8')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_7849,c_5555])).

tff(c_48,plain,(
    ! [A_19,B_20] : k5_xboole_0(A_19,k3_xboole_0(A_19,B_20)) = k4_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_8895,plain,(
    k4_xboole_0('#skF_9',k1_tarski('#skF_8')) = k5_xboole_0('#skF_9',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_7862,c_48])).

tff(c_8928,plain,(
    k4_xboole_0('#skF_9',k1_tarski('#skF_8')) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7918,c_8895])).

tff(c_64,plain,(
    ! [B_38,A_37] :
      ( ~ r2_hidden(B_38,A_37)
      | k4_xboole_0(A_37,k1_tarski(B_38)) != A_37 ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_9226,plain,(
    ~ r2_hidden('#skF_8','#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_8928,c_64])).

tff(c_9253,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5334,c_9226])).

tff(c_9254,plain,(
    r2_hidden('#skF_8','#skF_9') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_9356,plain,(
    ! [D_406,B_407,A_408] :
      ( r2_hidden(D_406,B_407)
      | ~ r2_hidden(D_406,k3_xboole_0(A_408,B_407)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_9370,plain,(
    ! [A_408,B_407] :
      ( r2_hidden('#skF_5'(k3_xboole_0(A_408,B_407)),B_407)
      | k3_xboole_0(A_408,B_407) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_40,c_9356])).

tff(c_9498,plain,(
    ! [D_424,A_425,B_426] :
      ( r2_hidden(D_424,A_425)
      | ~ r2_hidden(D_424,k3_xboole_0(A_425,B_426)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_11614,plain,(
    ! [A_506,B_507] :
      ( r2_hidden('#skF_5'(k3_xboole_0(A_506,B_507)),A_506)
      | k3_xboole_0(A_506,B_507) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_40,c_9498])).

tff(c_9255,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_74,plain,
    ( ~ r2_hidden('#skF_6','#skF_7')
    | k4_xboole_0(k1_tarski('#skF_8'),'#skF_9') = k1_tarski('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_9426,plain,(
    k4_xboole_0(k1_tarski('#skF_8'),'#skF_9') = k1_tarski('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9255,c_74])).

tff(c_24,plain,(
    ! [D_14,B_10,A_9] :
      ( ~ r2_hidden(D_14,B_10)
      | ~ r2_hidden(D_14,k4_xboole_0(A_9,B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_9433,plain,(
    ! [D_14] :
      ( ~ r2_hidden(D_14,'#skF_9')
      | ~ r2_hidden(D_14,k1_tarski('#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9426,c_24])).

tff(c_11697,plain,(
    ! [B_508] :
      ( ~ r2_hidden('#skF_5'(k3_xboole_0(k1_tarski('#skF_8'),B_508)),'#skF_9')
      | k3_xboole_0(k1_tarski('#skF_8'),B_508) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_11614,c_9433])).

tff(c_11734,plain,(
    k3_xboole_0(k1_tarski('#skF_8'),'#skF_9') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_9370,c_11697])).

tff(c_11822,plain,(
    k3_xboole_0('#skF_9',k1_tarski('#skF_8')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_11734,c_2])).

tff(c_9430,plain,(
    k4_xboole_0(k1_tarski('#skF_8'),k1_tarski('#skF_8')) = k3_xboole_0(k1_tarski('#skF_8'),'#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_9426,c_54])).

tff(c_9442,plain,(
    k4_xboole_0(k1_tarski('#skF_8'),k1_tarski('#skF_8')) = k3_xboole_0('#skF_9',k1_tarski('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_9430])).

tff(c_9790,plain,
    ( ~ r2_hidden('#skF_8',k1_tarski('#skF_8'))
    | k3_xboole_0('#skF_9',k1_tarski('#skF_8')) != k1_tarski('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_9442,c_64])).

tff(c_13720,plain,
    ( ~ r2_hidden('#skF_8',k1_tarski('#skF_8'))
    | k1_tarski('#skF_8') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_11822,c_9790])).

tff(c_13721,plain,(
    k1_tarski('#skF_8') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_13720])).

tff(c_66,plain,(
    ! [A_37,B_38] :
      ( k4_xboole_0(A_37,k1_tarski(B_38)) = A_37
      | r2_hidden(B_38,A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_9797,plain,
    ( k3_xboole_0('#skF_9',k1_tarski('#skF_8')) = k1_tarski('#skF_8')
    | r2_hidden('#skF_8',k1_tarski('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_9442])).

tff(c_13922,plain,
    ( k1_tarski('#skF_8') = k1_xboole_0
    | r2_hidden('#skF_8',k1_tarski('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11822,c_9797])).

tff(c_13923,plain,(
    r2_hidden('#skF_8',k1_tarski('#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_13721,c_13922])).

tff(c_13926,plain,(
    ~ r2_hidden('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_13923,c_9433])).

tff(c_13930,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9254,c_13926])).

tff(c_13932,plain,(
    k1_tarski('#skF_8') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_13720])).

tff(c_13975,plain,(
    ! [A_37] :
      ( ~ r2_hidden('#skF_8',A_37)
      | k4_xboole_0(A_37,k1_xboole_0) != A_37 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13932,c_64])).

tff(c_14752,plain,(
    ! [A_37] : ~ r2_hidden('#skF_8',A_37) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14145,c_13975])).

tff(c_14754,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14752,c_9254])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:57:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.08/3.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.08/3.16  
% 9.08/3.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.08/3.17  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_3
% 9.08/3.17  
% 9.08/3.17  %Foreground sorts:
% 9.08/3.17  
% 9.08/3.17  
% 9.08/3.17  %Background operators:
% 9.08/3.17  
% 9.08/3.17  
% 9.08/3.17  %Foreground operators:
% 9.08/3.17  tff('#skF_5', type, '#skF_5': $i > $i).
% 9.08/3.17  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 9.08/3.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.08/3.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.08/3.17  tff(k1_tarski, type, k1_tarski: $i > $i).
% 9.08/3.17  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.08/3.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.08/3.17  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 9.08/3.17  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 9.08/3.17  tff('#skF_7', type, '#skF_7': $i).
% 9.08/3.17  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 9.08/3.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.08/3.17  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 9.08/3.17  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.08/3.17  tff('#skF_6', type, '#skF_6': $i).
% 9.08/3.17  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 9.08/3.17  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 9.08/3.17  tff('#skF_9', type, '#skF_9': $i).
% 9.08/3.17  tff('#skF_8', type, '#skF_8': $i).
% 9.08/3.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.08/3.17  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 9.08/3.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.08/3.17  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.08/3.17  
% 9.08/3.19  tff(f_60, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.08/3.19  tff(f_66, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 9.08/3.19  tff(f_54, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 9.08/3.19  tff(f_46, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 9.08/3.19  tff(f_70, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 9.08/3.19  tff(f_89, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_zfmisc_1)).
% 9.08/3.19  tff(f_68, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 9.08/3.19  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 9.08/3.19  tff(f_62, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 9.08/3.19  tff(f_83, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 9.08/3.19  tff(f_36, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 9.08/3.19  tff(c_46, plain, (![B_18]: (r1_tarski(B_18, B_18))), inference(cnfTransformation, [status(thm)], [f_60])).
% 9.08/3.19  tff(c_9290, plain, (![A_394, B_395]: (k3_xboole_0(A_394, B_395)=A_394 | ~r1_tarski(A_394, B_395))), inference(cnfTransformation, [status(thm)], [f_66])).
% 9.08/3.19  tff(c_9298, plain, (![B_18]: (k3_xboole_0(B_18, B_18)=B_18)), inference(resolution, [status(thm)], [c_46, c_9290])).
% 9.08/3.19  tff(c_40, plain, (![A_15]: (r2_hidden('#skF_5'(A_15), A_15) | k1_xboole_0=A_15)), inference(cnfTransformation, [status(thm)], [f_54])).
% 9.08/3.19  tff(c_9371, plain, (![D_409, A_410, B_411]: (r2_hidden(D_409, A_410) | ~r2_hidden(D_409, k4_xboole_0(A_410, B_411)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 9.08/3.19  tff(c_14027, plain, (![A_555, B_556]: (r2_hidden('#skF_5'(k4_xboole_0(A_555, B_556)), A_555) | k4_xboole_0(A_555, B_556)=k1_xboole_0)), inference(resolution, [status(thm)], [c_40, c_9371])).
% 9.08/3.19  tff(c_9377, plain, (![D_412, B_413, A_414]: (~r2_hidden(D_412, B_413) | ~r2_hidden(D_412, k4_xboole_0(A_414, B_413)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 9.08/3.19  tff(c_9382, plain, (![A_414, B_413]: (~r2_hidden('#skF_5'(k4_xboole_0(A_414, B_413)), B_413) | k4_xboole_0(A_414, B_413)=k1_xboole_0)), inference(resolution, [status(thm)], [c_40, c_9377])).
% 9.08/3.19  tff(c_14080, plain, (![A_557]: (k4_xboole_0(A_557, A_557)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14027, c_9382])).
% 9.08/3.19  tff(c_54, plain, (![A_25, B_26]: (k4_xboole_0(A_25, k4_xboole_0(A_25, B_26))=k3_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_70])).
% 9.08/3.19  tff(c_14113, plain, (![A_557]: (k4_xboole_0(A_557, k1_xboole_0)=k3_xboole_0(A_557, A_557))), inference(superposition, [status(thm), theory('equality')], [c_14080, c_54])).
% 9.08/3.19  tff(c_14145, plain, (![A_557]: (k4_xboole_0(A_557, k1_xboole_0)=A_557)), inference(demodulation, [status(thm), theory('equality')], [c_9298, c_14113])).
% 9.08/3.19  tff(c_70, plain, (~r2_hidden('#skF_6', '#skF_7') | r2_hidden('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_89])).
% 9.08/3.19  tff(c_87, plain, (~r2_hidden('#skF_6', '#skF_7')), inference(splitLeft, [status(thm)], [c_70])).
% 9.08/3.19  tff(c_122, plain, (![A_46, B_47]: (k3_xboole_0(A_46, B_47)=A_46 | ~r1_tarski(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_66])).
% 9.08/3.19  tff(c_130, plain, (![B_18]: (k3_xboole_0(B_18, B_18)=B_18)), inference(resolution, [status(thm)], [c_46, c_122])).
% 9.08/3.19  tff(c_248, plain, (![D_64, A_65, B_66]: (r2_hidden(D_64, A_65) | ~r2_hidden(D_64, k4_xboole_0(A_65, B_66)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 9.08/3.19  tff(c_259, plain, (![A_65, B_66]: (r2_hidden('#skF_5'(k4_xboole_0(A_65, B_66)), A_65) | k4_xboole_0(A_65, B_66)=k1_xboole_0)), inference(resolution, [status(thm)], [c_40, c_248])).
% 9.08/3.19  tff(c_307, plain, (![D_75, B_76, A_77]: (~r2_hidden(D_75, B_76) | ~r2_hidden(D_75, k4_xboole_0(A_77, B_76)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 9.08/3.19  tff(c_2808, plain, (![A_189, B_190]: (~r2_hidden('#skF_5'(k4_xboole_0(A_189, B_190)), B_190) | k4_xboole_0(A_189, B_190)=k1_xboole_0)), inference(resolution, [status(thm)], [c_40, c_307])).
% 9.08/3.19  tff(c_2846, plain, (![A_191]: (k4_xboole_0(A_191, A_191)=k1_xboole_0)), inference(resolution, [status(thm)], [c_259, c_2808])).
% 9.08/3.19  tff(c_52, plain, (![A_23, B_24]: (r1_tarski(k4_xboole_0(A_23, B_24), A_23))), inference(cnfTransformation, [status(thm)], [f_68])).
% 9.08/3.19  tff(c_351, plain, (![A_80, B_81]: (k3_xboole_0(k4_xboole_0(A_80, B_81), A_80)=k4_xboole_0(A_80, B_81))), inference(resolution, [status(thm)], [c_52, c_122])).
% 9.08/3.19  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.08/3.19  tff(c_265, plain, (![A_69, B_70]: (k5_xboole_0(A_69, k3_xboole_0(A_69, B_70))=k4_xboole_0(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_62])).
% 9.08/3.19  tff(c_280, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_265])).
% 9.08/3.19  tff(c_357, plain, (![A_80, B_81]: (k5_xboole_0(A_80, k4_xboole_0(A_80, B_81))=k4_xboole_0(A_80, k4_xboole_0(A_80, B_81)))), inference(superposition, [status(thm), theory('equality')], [c_351, c_280])).
% 9.08/3.19  tff(c_397, plain, (![A_80, B_81]: (k5_xboole_0(A_80, k4_xboole_0(A_80, B_81))=k3_xboole_0(A_80, B_81))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_357])).
% 9.08/3.19  tff(c_2869, plain, (![A_191]: (k5_xboole_0(A_191, k1_xboole_0)=k3_xboole_0(A_191, A_191))), inference(superposition, [status(thm), theory('equality')], [c_2846, c_397])).
% 9.08/3.19  tff(c_2905, plain, (![A_191]: (k5_xboole_0(A_191, k1_xboole_0)=A_191)), inference(demodulation, [status(thm), theory('equality')], [c_130, c_2869])).
% 9.08/3.19  tff(c_2836, plain, (![A_65]: (k4_xboole_0(A_65, A_65)=k1_xboole_0)), inference(resolution, [status(thm)], [c_259, c_2808])).
% 9.08/3.19  tff(c_232, plain, (![A_62, B_63]: (k4_xboole_0(A_62, k1_tarski(B_63))=A_62 | r2_hidden(B_63, A_62))), inference(cnfTransformation, [status(thm)], [f_83])).
% 9.08/3.19  tff(c_238, plain, (![A_62, B_63]: (k4_xboole_0(A_62, A_62)=k3_xboole_0(A_62, k1_tarski(B_63)) | r2_hidden(B_63, A_62))), inference(superposition, [status(thm), theory('equality')], [c_232, c_54])).
% 9.08/3.19  tff(c_4313, plain, (![A_226, B_227]: (k3_xboole_0(A_226, k1_tarski(B_227))=k1_xboole_0 | r2_hidden(B_227, A_226))), inference(demodulation, [status(thm), theory('equality')], [c_2836, c_238])).
% 9.08/3.19  tff(c_4406, plain, (![B_227, A_226]: (k5_xboole_0(k1_tarski(B_227), k1_xboole_0)=k4_xboole_0(k1_tarski(B_227), A_226) | r2_hidden(B_227, A_226))), inference(superposition, [status(thm), theory('equality')], [c_4313, c_280])).
% 9.08/3.19  tff(c_5210, plain, (![B_242, A_243]: (k4_xboole_0(k1_tarski(B_242), A_243)=k1_tarski(B_242) | r2_hidden(B_242, A_243))), inference(demodulation, [status(thm), theory('equality')], [c_2905, c_4406])).
% 9.08/3.19  tff(c_68, plain, (k4_xboole_0(k1_tarski('#skF_6'), '#skF_7')!=k1_tarski('#skF_6') | r2_hidden('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_89])).
% 9.08/3.19  tff(c_140, plain, (k4_xboole_0(k1_tarski('#skF_6'), '#skF_7')!=k1_tarski('#skF_6')), inference(splitLeft, [status(thm)], [c_68])).
% 9.08/3.19  tff(c_5288, plain, (r2_hidden('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_5210, c_140])).
% 9.08/3.19  tff(c_5333, plain, $false, inference(negUnitSimplification, [status(thm)], [c_87, c_5288])).
% 9.08/3.19  tff(c_5334, plain, (r2_hidden('#skF_8', '#skF_9')), inference(splitRight, [status(thm)], [c_68])).
% 9.08/3.19  tff(c_5438, plain, (![D_258, A_259, B_260]: (r2_hidden(D_258, A_259) | ~r2_hidden(D_258, k4_xboole_0(A_259, B_260)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 9.08/3.19  tff(c_5449, plain, (![A_259, B_260]: (r2_hidden('#skF_5'(k4_xboole_0(A_259, B_260)), A_259) | k4_xboole_0(A_259, B_260)=k1_xboole_0)), inference(resolution, [status(thm)], [c_40, c_5438])).
% 9.08/3.19  tff(c_5490, plain, (![D_267, B_268, A_269]: (~r2_hidden(D_267, B_268) | ~r2_hidden(D_267, k4_xboole_0(A_269, B_268)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 9.08/3.19  tff(c_7806, plain, (![A_351, B_352]: (~r2_hidden('#skF_5'(k4_xboole_0(A_351, B_352)), B_352) | k4_xboole_0(A_351, B_352)=k1_xboole_0)), inference(resolution, [status(thm)], [c_40, c_5490])).
% 9.08/3.19  tff(c_7864, plain, (![A_353]: (k4_xboole_0(A_353, A_353)=k1_xboole_0)), inference(resolution, [status(thm)], [c_5449, c_7806])).
% 9.08/3.19  tff(c_129, plain, (![A_23, B_24]: (k3_xboole_0(k4_xboole_0(A_23, B_24), A_23)=k4_xboole_0(A_23, B_24))), inference(resolution, [status(thm)], [c_52, c_122])).
% 9.08/3.19  tff(c_5511, plain, (![A_271, B_272]: (k5_xboole_0(A_271, k3_xboole_0(A_271, B_272))=k4_xboole_0(A_271, B_272))), inference(cnfTransformation, [status(thm)], [f_62])).
% 9.08/3.19  tff(c_5620, plain, (![B_277, A_278]: (k5_xboole_0(B_277, k3_xboole_0(A_278, B_277))=k4_xboole_0(B_277, A_278))), inference(superposition, [status(thm), theory('equality')], [c_2, c_5511])).
% 9.08/3.19  tff(c_5633, plain, (![A_23, B_24]: (k5_xboole_0(A_23, k4_xboole_0(A_23, B_24))=k4_xboole_0(A_23, k4_xboole_0(A_23, B_24)))), inference(superposition, [status(thm), theory('equality')], [c_129, c_5620])).
% 9.08/3.19  tff(c_5650, plain, (![A_23, B_24]: (k5_xboole_0(A_23, k4_xboole_0(A_23, B_24))=k3_xboole_0(A_23, B_24))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_5633])).
% 9.08/3.19  tff(c_7881, plain, (![A_353]: (k5_xboole_0(A_353, k1_xboole_0)=k3_xboole_0(A_353, A_353))), inference(superposition, [status(thm), theory('equality')], [c_7864, c_5650])).
% 9.08/3.19  tff(c_7918, plain, (![A_353]: (k5_xboole_0(A_353, k1_xboole_0)=A_353)), inference(demodulation, [status(thm), theory('equality')], [c_130, c_7881])).
% 9.08/3.19  tff(c_7849, plain, (![A_259]: (k4_xboole_0(A_259, A_259)=k1_xboole_0)), inference(resolution, [status(thm)], [c_5449, c_7806])).
% 9.08/3.19  tff(c_5335, plain, (k4_xboole_0(k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_6')), inference(splitRight, [status(thm)], [c_68])).
% 9.08/3.19  tff(c_72, plain, (k4_xboole_0(k1_tarski('#skF_6'), '#skF_7')!=k1_tarski('#skF_6') | k4_xboole_0(k1_tarski('#skF_8'), '#skF_9')=k1_tarski('#skF_8')), inference(cnfTransformation, [status(thm)], [f_89])).
% 9.08/3.19  tff(c_5539, plain, (k4_xboole_0(k1_tarski('#skF_8'), '#skF_9')=k1_tarski('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_5335, c_72])).
% 9.08/3.19  tff(c_5549, plain, (k4_xboole_0(k1_tarski('#skF_8'), k1_tarski('#skF_8'))=k3_xboole_0(k1_tarski('#skF_8'), '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_5539, c_54])).
% 9.08/3.19  tff(c_5555, plain, (k4_xboole_0(k1_tarski('#skF_8'), k1_tarski('#skF_8'))=k3_xboole_0('#skF_9', k1_tarski('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_5549])).
% 9.08/3.19  tff(c_7862, plain, (k3_xboole_0('#skF_9', k1_tarski('#skF_8'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_7849, c_5555])).
% 9.08/3.19  tff(c_48, plain, (![A_19, B_20]: (k5_xboole_0(A_19, k3_xboole_0(A_19, B_20))=k4_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_62])).
% 9.08/3.19  tff(c_8895, plain, (k4_xboole_0('#skF_9', k1_tarski('#skF_8'))=k5_xboole_0('#skF_9', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_7862, c_48])).
% 9.08/3.19  tff(c_8928, plain, (k4_xboole_0('#skF_9', k1_tarski('#skF_8'))='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_7918, c_8895])).
% 9.08/3.19  tff(c_64, plain, (![B_38, A_37]: (~r2_hidden(B_38, A_37) | k4_xboole_0(A_37, k1_tarski(B_38))!=A_37)), inference(cnfTransformation, [status(thm)], [f_83])).
% 9.08/3.19  tff(c_9226, plain, (~r2_hidden('#skF_8', '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_8928, c_64])).
% 9.08/3.19  tff(c_9253, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5334, c_9226])).
% 9.08/3.19  tff(c_9254, plain, (r2_hidden('#skF_8', '#skF_9')), inference(splitRight, [status(thm)], [c_70])).
% 9.08/3.19  tff(c_9356, plain, (![D_406, B_407, A_408]: (r2_hidden(D_406, B_407) | ~r2_hidden(D_406, k3_xboole_0(A_408, B_407)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 9.08/3.19  tff(c_9370, plain, (![A_408, B_407]: (r2_hidden('#skF_5'(k3_xboole_0(A_408, B_407)), B_407) | k3_xboole_0(A_408, B_407)=k1_xboole_0)), inference(resolution, [status(thm)], [c_40, c_9356])).
% 9.08/3.19  tff(c_9498, plain, (![D_424, A_425, B_426]: (r2_hidden(D_424, A_425) | ~r2_hidden(D_424, k3_xboole_0(A_425, B_426)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 9.08/3.19  tff(c_11614, plain, (![A_506, B_507]: (r2_hidden('#skF_5'(k3_xboole_0(A_506, B_507)), A_506) | k3_xboole_0(A_506, B_507)=k1_xboole_0)), inference(resolution, [status(thm)], [c_40, c_9498])).
% 9.08/3.19  tff(c_9255, plain, (r2_hidden('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_70])).
% 9.08/3.19  tff(c_74, plain, (~r2_hidden('#skF_6', '#skF_7') | k4_xboole_0(k1_tarski('#skF_8'), '#skF_9')=k1_tarski('#skF_8')), inference(cnfTransformation, [status(thm)], [f_89])).
% 9.08/3.19  tff(c_9426, plain, (k4_xboole_0(k1_tarski('#skF_8'), '#skF_9')=k1_tarski('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_9255, c_74])).
% 9.08/3.19  tff(c_24, plain, (![D_14, B_10, A_9]: (~r2_hidden(D_14, B_10) | ~r2_hidden(D_14, k4_xboole_0(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 9.08/3.19  tff(c_9433, plain, (![D_14]: (~r2_hidden(D_14, '#skF_9') | ~r2_hidden(D_14, k1_tarski('#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_9426, c_24])).
% 9.08/3.19  tff(c_11697, plain, (![B_508]: (~r2_hidden('#skF_5'(k3_xboole_0(k1_tarski('#skF_8'), B_508)), '#skF_9') | k3_xboole_0(k1_tarski('#skF_8'), B_508)=k1_xboole_0)), inference(resolution, [status(thm)], [c_11614, c_9433])).
% 9.08/3.19  tff(c_11734, plain, (k3_xboole_0(k1_tarski('#skF_8'), '#skF_9')=k1_xboole_0), inference(resolution, [status(thm)], [c_9370, c_11697])).
% 9.08/3.19  tff(c_11822, plain, (k3_xboole_0('#skF_9', k1_tarski('#skF_8'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_11734, c_2])).
% 9.08/3.19  tff(c_9430, plain, (k4_xboole_0(k1_tarski('#skF_8'), k1_tarski('#skF_8'))=k3_xboole_0(k1_tarski('#skF_8'), '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_9426, c_54])).
% 9.08/3.19  tff(c_9442, plain, (k4_xboole_0(k1_tarski('#skF_8'), k1_tarski('#skF_8'))=k3_xboole_0('#skF_9', k1_tarski('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_9430])).
% 9.08/3.19  tff(c_9790, plain, (~r2_hidden('#skF_8', k1_tarski('#skF_8')) | k3_xboole_0('#skF_9', k1_tarski('#skF_8'))!=k1_tarski('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_9442, c_64])).
% 9.08/3.19  tff(c_13720, plain, (~r2_hidden('#skF_8', k1_tarski('#skF_8')) | k1_tarski('#skF_8')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_11822, c_9790])).
% 9.08/3.19  tff(c_13721, plain, (k1_tarski('#skF_8')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_13720])).
% 9.08/3.19  tff(c_66, plain, (![A_37, B_38]: (k4_xboole_0(A_37, k1_tarski(B_38))=A_37 | r2_hidden(B_38, A_37))), inference(cnfTransformation, [status(thm)], [f_83])).
% 9.08/3.19  tff(c_9797, plain, (k3_xboole_0('#skF_9', k1_tarski('#skF_8'))=k1_tarski('#skF_8') | r2_hidden('#skF_8', k1_tarski('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_66, c_9442])).
% 9.08/3.19  tff(c_13922, plain, (k1_tarski('#skF_8')=k1_xboole_0 | r2_hidden('#skF_8', k1_tarski('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_11822, c_9797])).
% 9.08/3.19  tff(c_13923, plain, (r2_hidden('#skF_8', k1_tarski('#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_13721, c_13922])).
% 9.08/3.19  tff(c_13926, plain, (~r2_hidden('#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_13923, c_9433])).
% 9.08/3.19  tff(c_13930, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9254, c_13926])).
% 9.08/3.19  tff(c_13932, plain, (k1_tarski('#skF_8')=k1_xboole_0), inference(splitRight, [status(thm)], [c_13720])).
% 9.08/3.19  tff(c_13975, plain, (![A_37]: (~r2_hidden('#skF_8', A_37) | k4_xboole_0(A_37, k1_xboole_0)!=A_37)), inference(superposition, [status(thm), theory('equality')], [c_13932, c_64])).
% 9.08/3.19  tff(c_14752, plain, (![A_37]: (~r2_hidden('#skF_8', A_37))), inference(demodulation, [status(thm), theory('equality')], [c_14145, c_13975])).
% 9.08/3.19  tff(c_14754, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14752, c_9254])).
% 9.08/3.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.08/3.19  
% 9.08/3.19  Inference rules
% 9.08/3.19  ----------------------
% 9.08/3.19  #Ref     : 0
% 9.08/3.19  #Sup     : 3489
% 9.08/3.19  #Fact    : 0
% 9.08/3.19  #Define  : 0
% 9.08/3.19  #Split   : 7
% 9.08/3.19  #Chain   : 0
% 9.08/3.19  #Close   : 0
% 9.08/3.19  
% 9.08/3.19  Ordering : KBO
% 9.08/3.19  
% 9.08/3.19  Simplification rules
% 9.08/3.19  ----------------------
% 9.08/3.19  #Subsume      : 545
% 9.08/3.19  #Demod        : 3152
% 9.08/3.19  #Tautology    : 1757
% 9.08/3.19  #SimpNegUnit  : 47
% 9.08/3.19  #BackRed      : 40
% 9.08/3.19  
% 9.08/3.19  #Partial instantiations: 0
% 9.08/3.19  #Strategies tried      : 1
% 9.08/3.19  
% 9.08/3.19  Timing (in seconds)
% 9.08/3.19  ----------------------
% 9.08/3.19  Preprocessing        : 0.46
% 9.08/3.19  Parsing              : 0.25
% 9.08/3.19  CNF conversion       : 0.03
% 9.08/3.19  Main loop            : 1.86
% 9.08/3.19  Inferencing          : 0.55
% 9.08/3.19  Reduction            : 0.79
% 9.08/3.19  Demodulation         : 0.64
% 9.08/3.19  BG Simplification    : 0.07
% 9.08/3.19  Subsumption          : 0.34
% 9.08/3.19  Abstraction          : 0.09
% 9.08/3.19  MUC search           : 0.00
% 9.08/3.19  Cooper               : 0.00
% 9.08/3.19  Total                : 2.36
% 9.08/3.19  Index Insertion      : 0.00
% 9.08/3.19  Index Deletion       : 0.00
% 9.08/3.19  Index Matching       : 0.00
% 9.08/3.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
