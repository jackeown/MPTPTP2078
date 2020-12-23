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
% DateTime   : Thu Dec  3 09:50:22 EST 2020

% Result     : Theorem 4.43s
% Output     : CNFRefutation 4.63s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 351 expanded)
%              Number of leaves         :   40 ( 131 expanded)
%              Depth                    :   14
%              Number of atoms          :  144 ( 526 expanded)
%              Number of equality atoms :  108 ( 489 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_113,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_68,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_66,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_60,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_54,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_56,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_70,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_64,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_72,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_62,axiom,(
    ! [A,B,C] : r1_tarski(k3_xboole_0(A,B),k2_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_xboole_1)).

tff(c_62,plain,
    ( k1_tarski('#skF_3') != '#skF_5'
    | k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_96,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_60,plain,
    ( k1_xboole_0 != '#skF_5'
    | k1_tarski('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_77,plain,(
    k1_tarski('#skF_3') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_66,plain,(
    k2_xboole_0('#skF_4','#skF_5') = k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_32,plain,(
    ! [A_27,B_28] : r1_tarski(A_27,k2_xboole_0(A_27,B_28)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_92,plain,(
    r1_tarski('#skF_4',k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_32])).

tff(c_596,plain,(
    ! [B_140,A_141] :
      ( k1_tarski(B_140) = A_141
      | k1_xboole_0 = A_141
      | ~ r1_tarski(A_141,k1_tarski(B_140)) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_622,plain,
    ( k1_tarski('#skF_3') = '#skF_4'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_92,c_596])).

tff(c_633,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_77,c_622])).

tff(c_634,plain,(
    k1_tarski('#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_635,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_30,plain,(
    ! [A_26] : k5_xboole_0(A_26,k1_xboole_0) = A_26 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_636,plain,(
    ! [A_26] : k5_xboole_0(A_26,'#skF_4') = A_26 ),
    inference(demodulation,[status(thm),theory(equality)],[c_635,c_30])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_24,plain,(
    ! [A_19,B_20] : k2_xboole_0(A_19,k3_xboole_0(A_19,B_20)) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_667,plain,(
    ! [A_147,B_148] : k3_xboole_0(A_147,k2_xboole_0(A_147,B_148)) = A_147 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_679,plain,(
    ! [A_19] : k3_xboole_0(A_19,A_19) = A_19 ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_667])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( r1_xboole_0(A_6,B_7)
      | k3_xboole_0(A_6,B_7) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_763,plain,(
    ! [A_6,B_7] :
      ( r1_xboole_0(A_6,B_7)
      | k3_xboole_0(A_6,B_7) != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_635,c_10])).

tff(c_969,plain,(
    ! [A_184,B_185,C_186] :
      ( ~ r1_xboole_0(A_184,B_185)
      | ~ r2_hidden(C_186,k3_xboole_0(A_184,B_185)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_984,plain,(
    ! [A_187,C_188] :
      ( ~ r1_xboole_0(A_187,A_187)
      | ~ r2_hidden(C_188,A_187) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_679,c_969])).

tff(c_987,plain,(
    ! [C_188,B_7] :
      ( ~ r2_hidden(C_188,B_7)
      | k3_xboole_0(B_7,B_7) != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_763,c_984])).

tff(c_991,plain,(
    ! [C_189,B_190] :
      ( ~ r2_hidden(C_189,B_190)
      | B_190 != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_679,c_987])).

tff(c_1002,plain,(
    ! [A_194,B_195] :
      ( A_194 != '#skF_4'
      | r1_tarski(A_194,B_195) ) ),
    inference(resolution,[status(thm)],[c_6,c_991])).

tff(c_18,plain,(
    ! [A_13,B_14] :
      ( k4_xboole_0(A_13,B_14) = k1_xboole_0
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_765,plain,(
    ! [A_13,B_14] :
      ( k4_xboole_0(A_13,B_14) = '#skF_4'
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_635,c_18])).

tff(c_1007,plain,(
    ! [B_195] : k4_xboole_0('#skF_4',B_195) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1002,c_765])).

tff(c_20,plain,(
    ! [A_15,B_16] : k5_xboole_0(A_15,k3_xboole_0(A_15,B_16)) = k4_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1377,plain,(
    ! [A_224,B_225,C_226] : k5_xboole_0(k5_xboole_0(A_224,B_225),C_226) = k5_xboole_0(A_224,k5_xboole_0(B_225,C_226)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1429,plain,(
    ! [A_227,C_228] : k5_xboole_0(A_227,k5_xboole_0('#skF_4',C_228)) = k5_xboole_0(A_227,C_228) ),
    inference(superposition,[status(thm),theory(equality)],[c_636,c_1377])).

tff(c_1470,plain,(
    ! [A_227,B_16] : k5_xboole_0(A_227,k4_xboole_0('#skF_4',B_16)) = k5_xboole_0(A_227,k3_xboole_0('#skF_4',B_16)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_1429])).

tff(c_1575,plain,(
    ! [A_230,B_231] : k5_xboole_0(A_230,k3_xboole_0('#skF_4',B_231)) = A_230 ),
    inference(demodulation,[status(thm),theory(equality)],[c_636,c_1007,c_1470])).

tff(c_28,plain,(
    ! [A_24,B_25] : k4_xboole_0(A_24,k2_xboole_0(A_24,B_25)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_685,plain,(
    ! [A_24,B_25] : k4_xboole_0(A_24,k2_xboole_0(A_24,B_25)) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_635,c_28])).

tff(c_22,plain,(
    ! [A_17,B_18] : k3_xboole_0(A_17,k2_xboole_0(A_17,B_18)) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_923,plain,(
    ! [A_179,B_180] : k5_xboole_0(A_179,k3_xboole_0(A_179,B_180)) = k4_xboole_0(A_179,B_180) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_938,plain,(
    ! [A_17,B_18] : k4_xboole_0(A_17,k2_xboole_0(A_17,B_18)) = k5_xboole_0(A_17,A_17) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_923])).

tff(c_943,plain,(
    ! [A_17] : k5_xboole_0(A_17,A_17) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_685,c_938])).

tff(c_1601,plain,(
    ! [B_231] : k3_xboole_0('#skF_4',B_231) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1575,c_943])).

tff(c_1971,plain,(
    ! [A_241,C_242] : k5_xboole_0(A_241,k5_xboole_0(A_241,C_242)) = k5_xboole_0('#skF_4',C_242) ),
    inference(superposition,[status(thm),theory(equality)],[c_943,c_1377])).

tff(c_2055,plain,(
    ! [A_17] : k5_xboole_0(A_17,'#skF_4') = k5_xboole_0('#skF_4',A_17) ),
    inference(superposition,[status(thm),theory(equality)],[c_943,c_1971])).

tff(c_2084,plain,(
    ! [A_17] : k5_xboole_0('#skF_4',A_17) = A_17 ),
    inference(demodulation,[status(thm),theory(equality)],[c_636,c_2055])).

tff(c_2237,plain,(
    ! [A_246,B_247] : k5_xboole_0(k5_xboole_0(A_246,B_247),k3_xboole_0(A_246,B_247)) = k2_xboole_0(A_246,B_247) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2267,plain,(
    ! [A_17] : k5_xboole_0(A_17,k3_xboole_0('#skF_4',A_17)) = k2_xboole_0('#skF_4',A_17) ),
    inference(superposition,[status(thm),theory(equality)],[c_2084,c_2237])).

tff(c_2298,plain,(
    ! [A_17] : k2_xboole_0('#skF_4',A_17) = A_17 ),
    inference(demodulation,[status(thm),theory(equality)],[c_636,c_1601,c_2267])).

tff(c_2303,plain,(
    k1_tarski('#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2298,c_66])).

tff(c_2305,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_634,c_2303])).

tff(c_2307,plain,(
    k1_tarski('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_64,plain,
    ( k1_tarski('#skF_3') != '#skF_5'
    | k1_tarski('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_2358,plain,(
    '#skF_5' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2307,c_2307,c_64])).

tff(c_3130,plain,(
    ! [A_337,B_338,C_339] : k5_xboole_0(k5_xboole_0(A_337,B_338),C_339) = k5_xboole_0(A_337,k5_xboole_0(B_338,C_339)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2583,plain,(
    ! [A_285,B_286] : k5_xboole_0(A_285,k3_xboole_0(A_285,B_286)) = k4_xboole_0(A_285,B_286) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2595,plain,(
    ! [A_17,B_18] : k4_xboole_0(A_17,k2_xboole_0(A_17,B_18)) = k5_xboole_0(A_17,A_17) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_2583])).

tff(c_2599,plain,(
    ! [A_17] : k5_xboole_0(A_17,A_17) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_2595])).

tff(c_3147,plain,(
    ! [A_337,B_338] : k5_xboole_0(A_337,k5_xboole_0(B_338,k5_xboole_0(A_337,B_338))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_3130,c_2599])).

tff(c_2377,plain,(
    ! [A_256,B_257] : k2_xboole_0(A_256,k3_xboole_0(A_256,B_257)) = A_256 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2398,plain,(
    ! [A_17] : k2_xboole_0(A_17,A_17) = A_17 ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_2377])).

tff(c_2386,plain,(
    ! [A_256] : k3_xboole_0(A_256,A_256) = A_256 ),
    inference(superposition,[status(thm),theory(equality)],[c_2377,c_22])).

tff(c_3093,plain,(
    ! [A_335,B_336] : k5_xboole_0(k5_xboole_0(A_335,B_336),k3_xboole_0(A_335,B_336)) = k2_xboole_0(A_335,B_336) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_3111,plain,(
    ! [A_17] : k5_xboole_0(k1_xboole_0,k3_xboole_0(A_17,A_17)) = k2_xboole_0(A_17,A_17) ),
    inference(superposition,[status(thm),theory(equality)],[c_2599,c_3093])).

tff(c_3127,plain,(
    ! [A_17] : k5_xboole_0(k1_xboole_0,A_17) = A_17 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2398,c_2386,c_3111])).

tff(c_3170,plain,(
    ! [A_17,C_339] : k5_xboole_0(A_17,k5_xboole_0(A_17,C_339)) = k5_xboole_0(k1_xboole_0,C_339) ),
    inference(superposition,[status(thm),theory(equality)],[c_2599,c_3130])).

tff(c_3951,plain,(
    ! [A_363,C_364] : k5_xboole_0(A_363,k5_xboole_0(A_363,C_364)) = C_364 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3127,c_3170])).

tff(c_4002,plain,(
    ! [B_338,A_337] : k5_xboole_0(B_338,k5_xboole_0(A_337,B_338)) = k5_xboole_0(A_337,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_3147,c_3951])).

tff(c_4055,plain,(
    ! [B_365,A_366] : k5_xboole_0(B_365,k5_xboole_0(A_366,B_365)) = A_366 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_4002])).

tff(c_4046,plain,(
    ! [B_338,A_337] : k5_xboole_0(B_338,k5_xboole_0(A_337,B_338)) = A_337 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_4002])).

tff(c_4058,plain,(
    ! [A_366,B_365] : k5_xboole_0(k5_xboole_0(A_366,B_365),A_366) = B_365 ),
    inference(superposition,[status(thm),theory(equality)],[c_4055,c_4046])).

tff(c_2326,plain,(
    k2_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2307,c_66])).

tff(c_2306,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_2501,plain,(
    ! [A_273,B_274,C_275] : r1_tarski(k3_xboole_0(A_273,B_274),k2_xboole_0(A_273,C_275)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2513,plain,(
    ! [A_19,B_274] : r1_tarski(k3_xboole_0(A_19,B_274),A_19) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_2501])).

tff(c_2739,plain,(
    ! [B_307,A_308] :
      ( k1_tarski(B_307) = A_308
      | k1_xboole_0 = A_308
      | ~ r1_tarski(A_308,k1_tarski(B_307)) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_2758,plain,(
    ! [A_308] :
      ( k1_tarski('#skF_3') = A_308
      | k1_xboole_0 = A_308
      | ~ r1_tarski(A_308,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2307,c_2739])).

tff(c_2765,plain,(
    ! [A_309] :
      ( A_309 = '#skF_4'
      | k1_xboole_0 = A_309
      | ~ r1_tarski(A_309,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2307,c_2758])).

tff(c_2783,plain,(
    ! [B_274] :
      ( k3_xboole_0('#skF_4',B_274) = '#skF_4'
      | k3_xboole_0('#skF_4',B_274) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2513,c_2765])).

tff(c_3108,plain,(
    ! [B_274] :
      ( k5_xboole_0(k5_xboole_0('#skF_4',B_274),k1_xboole_0) = k2_xboole_0('#skF_4',B_274)
      | k3_xboole_0('#skF_4',B_274) = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2783,c_3093])).

tff(c_3126,plain,(
    ! [B_274] :
      ( k5_xboole_0('#skF_4',B_274) = k2_xboole_0('#skF_4',B_274)
      | k3_xboole_0('#skF_4',B_274) = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_3108])).

tff(c_4530,plain,(
    ! [B_378] :
      ( k5_xboole_0('#skF_4',k2_xboole_0('#skF_4',B_378)) = B_378
      | k3_xboole_0('#skF_4',B_378) = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3126,c_3951])).

tff(c_4578,plain,
    ( k5_xboole_0('#skF_4','#skF_4') = '#skF_5'
    | k3_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_2326,c_4530])).

tff(c_4591,plain,
    ( k1_xboole_0 = '#skF_5'
    | k3_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2599,c_4578])).

tff(c_4592,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_2306,c_4591])).

tff(c_36,plain,(
    ! [A_32,B_33] : k5_xboole_0(k5_xboole_0(A_32,B_33),k3_xboole_0(A_32,B_33)) = k2_xboole_0(A_32,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_4602,plain,(
    k5_xboole_0(k5_xboole_0('#skF_4','#skF_5'),'#skF_4') = k2_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_4592,c_36])).

tff(c_4638,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4058,c_2326,c_4602])).

tff(c_4640,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2358,c_4638])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:35:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.43/1.84  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.43/1.85  
% 4.43/1.85  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.43/1.85  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 4.43/1.85  
% 4.43/1.85  %Foreground sorts:
% 4.43/1.85  
% 4.43/1.85  
% 4.43/1.85  %Background operators:
% 4.43/1.85  
% 4.43/1.85  
% 4.43/1.85  %Foreground operators:
% 4.43/1.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.43/1.85  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.43/1.85  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.43/1.85  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.43/1.85  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.43/1.85  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.43/1.85  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.43/1.85  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.43/1.85  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.43/1.85  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.43/1.85  tff('#skF_5', type, '#skF_5': $i).
% 4.43/1.85  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.43/1.85  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.43/1.85  tff('#skF_3', type, '#skF_3': $i).
% 4.43/1.85  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.43/1.85  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.43/1.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.43/1.85  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.43/1.85  tff('#skF_4', type, '#skF_4': $i).
% 4.43/1.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.43/1.85  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.43/1.85  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.43/1.85  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.43/1.85  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.43/1.85  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.43/1.85  
% 4.63/1.87  tff(f_113, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 4.63/1.87  tff(f_68, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 4.63/1.87  tff(f_92, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 4.63/1.87  tff(f_66, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 4.63/1.87  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.63/1.87  tff(f_60, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 4.63/1.87  tff(f_58, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 4.63/1.87  tff(f_36, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 4.63/1.87  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 4.63/1.87  tff(f_54, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 4.63/1.87  tff(f_56, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.63/1.87  tff(f_70, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 4.63/1.87  tff(f_64, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 4.63/1.87  tff(f_72, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 4.63/1.87  tff(f_62, axiom, (![A, B, C]: r1_tarski(k3_xboole_0(A, B), k2_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_xboole_1)).
% 4.63/1.87  tff(c_62, plain, (k1_tarski('#skF_3')!='#skF_5' | k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.63/1.87  tff(c_96, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_62])).
% 4.63/1.87  tff(c_60, plain, (k1_xboole_0!='#skF_5' | k1_tarski('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.63/1.87  tff(c_77, plain, (k1_tarski('#skF_3')!='#skF_4'), inference(splitLeft, [status(thm)], [c_60])).
% 4.63/1.87  tff(c_66, plain, (k2_xboole_0('#skF_4', '#skF_5')=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.63/1.87  tff(c_32, plain, (![A_27, B_28]: (r1_tarski(A_27, k2_xboole_0(A_27, B_28)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.63/1.87  tff(c_92, plain, (r1_tarski('#skF_4', k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_66, c_32])).
% 4.63/1.87  tff(c_596, plain, (![B_140, A_141]: (k1_tarski(B_140)=A_141 | k1_xboole_0=A_141 | ~r1_tarski(A_141, k1_tarski(B_140)))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.63/1.87  tff(c_622, plain, (k1_tarski('#skF_3')='#skF_4' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_92, c_596])).
% 4.63/1.87  tff(c_633, plain, $false, inference(negUnitSimplification, [status(thm)], [c_96, c_77, c_622])).
% 4.63/1.87  tff(c_634, plain, (k1_tarski('#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_62])).
% 4.63/1.87  tff(c_635, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_62])).
% 4.63/1.87  tff(c_30, plain, (![A_26]: (k5_xboole_0(A_26, k1_xboole_0)=A_26)), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.63/1.87  tff(c_636, plain, (![A_26]: (k5_xboole_0(A_26, '#skF_4')=A_26)), inference(demodulation, [status(thm), theory('equality')], [c_635, c_30])).
% 4.63/1.87  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.63/1.87  tff(c_24, plain, (![A_19, B_20]: (k2_xboole_0(A_19, k3_xboole_0(A_19, B_20))=A_19)), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.63/1.87  tff(c_667, plain, (![A_147, B_148]: (k3_xboole_0(A_147, k2_xboole_0(A_147, B_148))=A_147)), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.63/1.87  tff(c_679, plain, (![A_19]: (k3_xboole_0(A_19, A_19)=A_19)), inference(superposition, [status(thm), theory('equality')], [c_24, c_667])).
% 4.63/1.87  tff(c_10, plain, (![A_6, B_7]: (r1_xboole_0(A_6, B_7) | k3_xboole_0(A_6, B_7)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.63/1.87  tff(c_763, plain, (![A_6, B_7]: (r1_xboole_0(A_6, B_7) | k3_xboole_0(A_6, B_7)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_635, c_10])).
% 4.63/1.87  tff(c_969, plain, (![A_184, B_185, C_186]: (~r1_xboole_0(A_184, B_185) | ~r2_hidden(C_186, k3_xboole_0(A_184, B_185)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.63/1.87  tff(c_984, plain, (![A_187, C_188]: (~r1_xboole_0(A_187, A_187) | ~r2_hidden(C_188, A_187))), inference(superposition, [status(thm), theory('equality')], [c_679, c_969])).
% 4.63/1.87  tff(c_987, plain, (![C_188, B_7]: (~r2_hidden(C_188, B_7) | k3_xboole_0(B_7, B_7)!='#skF_4')), inference(resolution, [status(thm)], [c_763, c_984])).
% 4.63/1.87  tff(c_991, plain, (![C_189, B_190]: (~r2_hidden(C_189, B_190) | B_190!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_679, c_987])).
% 4.63/1.87  tff(c_1002, plain, (![A_194, B_195]: (A_194!='#skF_4' | r1_tarski(A_194, B_195))), inference(resolution, [status(thm)], [c_6, c_991])).
% 4.63/1.87  tff(c_18, plain, (![A_13, B_14]: (k4_xboole_0(A_13, B_14)=k1_xboole_0 | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.63/1.87  tff(c_765, plain, (![A_13, B_14]: (k4_xboole_0(A_13, B_14)='#skF_4' | ~r1_tarski(A_13, B_14))), inference(demodulation, [status(thm), theory('equality')], [c_635, c_18])).
% 4.63/1.87  tff(c_1007, plain, (![B_195]: (k4_xboole_0('#skF_4', B_195)='#skF_4')), inference(resolution, [status(thm)], [c_1002, c_765])).
% 4.63/1.87  tff(c_20, plain, (![A_15, B_16]: (k5_xboole_0(A_15, k3_xboole_0(A_15, B_16))=k4_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.63/1.87  tff(c_1377, plain, (![A_224, B_225, C_226]: (k5_xboole_0(k5_xboole_0(A_224, B_225), C_226)=k5_xboole_0(A_224, k5_xboole_0(B_225, C_226)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.63/1.87  tff(c_1429, plain, (![A_227, C_228]: (k5_xboole_0(A_227, k5_xboole_0('#skF_4', C_228))=k5_xboole_0(A_227, C_228))), inference(superposition, [status(thm), theory('equality')], [c_636, c_1377])).
% 4.63/1.87  tff(c_1470, plain, (![A_227, B_16]: (k5_xboole_0(A_227, k4_xboole_0('#skF_4', B_16))=k5_xboole_0(A_227, k3_xboole_0('#skF_4', B_16)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_1429])).
% 4.63/1.87  tff(c_1575, plain, (![A_230, B_231]: (k5_xboole_0(A_230, k3_xboole_0('#skF_4', B_231))=A_230)), inference(demodulation, [status(thm), theory('equality')], [c_636, c_1007, c_1470])).
% 4.63/1.87  tff(c_28, plain, (![A_24, B_25]: (k4_xboole_0(A_24, k2_xboole_0(A_24, B_25))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.63/1.87  tff(c_685, plain, (![A_24, B_25]: (k4_xboole_0(A_24, k2_xboole_0(A_24, B_25))='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_635, c_28])).
% 4.63/1.87  tff(c_22, plain, (![A_17, B_18]: (k3_xboole_0(A_17, k2_xboole_0(A_17, B_18))=A_17)), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.63/1.87  tff(c_923, plain, (![A_179, B_180]: (k5_xboole_0(A_179, k3_xboole_0(A_179, B_180))=k4_xboole_0(A_179, B_180))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.63/1.87  tff(c_938, plain, (![A_17, B_18]: (k4_xboole_0(A_17, k2_xboole_0(A_17, B_18))=k5_xboole_0(A_17, A_17))), inference(superposition, [status(thm), theory('equality')], [c_22, c_923])).
% 4.63/1.87  tff(c_943, plain, (![A_17]: (k5_xboole_0(A_17, A_17)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_685, c_938])).
% 4.63/1.87  tff(c_1601, plain, (![B_231]: (k3_xboole_0('#skF_4', B_231)='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1575, c_943])).
% 4.63/1.87  tff(c_1971, plain, (![A_241, C_242]: (k5_xboole_0(A_241, k5_xboole_0(A_241, C_242))=k5_xboole_0('#skF_4', C_242))), inference(superposition, [status(thm), theory('equality')], [c_943, c_1377])).
% 4.63/1.87  tff(c_2055, plain, (![A_17]: (k5_xboole_0(A_17, '#skF_4')=k5_xboole_0('#skF_4', A_17))), inference(superposition, [status(thm), theory('equality')], [c_943, c_1971])).
% 4.63/1.87  tff(c_2084, plain, (![A_17]: (k5_xboole_0('#skF_4', A_17)=A_17)), inference(demodulation, [status(thm), theory('equality')], [c_636, c_2055])).
% 4.63/1.87  tff(c_2237, plain, (![A_246, B_247]: (k5_xboole_0(k5_xboole_0(A_246, B_247), k3_xboole_0(A_246, B_247))=k2_xboole_0(A_246, B_247))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.63/1.87  tff(c_2267, plain, (![A_17]: (k5_xboole_0(A_17, k3_xboole_0('#skF_4', A_17))=k2_xboole_0('#skF_4', A_17))), inference(superposition, [status(thm), theory('equality')], [c_2084, c_2237])).
% 4.63/1.87  tff(c_2298, plain, (![A_17]: (k2_xboole_0('#skF_4', A_17)=A_17)), inference(demodulation, [status(thm), theory('equality')], [c_636, c_1601, c_2267])).
% 4.63/1.87  tff(c_2303, plain, (k1_tarski('#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2298, c_66])).
% 4.63/1.87  tff(c_2305, plain, $false, inference(negUnitSimplification, [status(thm)], [c_634, c_2303])).
% 4.63/1.87  tff(c_2307, plain, (k1_tarski('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_60])).
% 4.63/1.87  tff(c_64, plain, (k1_tarski('#skF_3')!='#skF_5' | k1_tarski('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.63/1.87  tff(c_2358, plain, ('#skF_5'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2307, c_2307, c_64])).
% 4.63/1.87  tff(c_3130, plain, (![A_337, B_338, C_339]: (k5_xboole_0(k5_xboole_0(A_337, B_338), C_339)=k5_xboole_0(A_337, k5_xboole_0(B_338, C_339)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.63/1.87  tff(c_2583, plain, (![A_285, B_286]: (k5_xboole_0(A_285, k3_xboole_0(A_285, B_286))=k4_xboole_0(A_285, B_286))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.63/1.87  tff(c_2595, plain, (![A_17, B_18]: (k4_xboole_0(A_17, k2_xboole_0(A_17, B_18))=k5_xboole_0(A_17, A_17))), inference(superposition, [status(thm), theory('equality')], [c_22, c_2583])).
% 4.63/1.87  tff(c_2599, plain, (![A_17]: (k5_xboole_0(A_17, A_17)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_2595])).
% 4.63/1.87  tff(c_3147, plain, (![A_337, B_338]: (k5_xboole_0(A_337, k5_xboole_0(B_338, k5_xboole_0(A_337, B_338)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3130, c_2599])).
% 4.63/1.87  tff(c_2377, plain, (![A_256, B_257]: (k2_xboole_0(A_256, k3_xboole_0(A_256, B_257))=A_256)), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.63/1.87  tff(c_2398, plain, (![A_17]: (k2_xboole_0(A_17, A_17)=A_17)), inference(superposition, [status(thm), theory('equality')], [c_22, c_2377])).
% 4.63/1.87  tff(c_2386, plain, (![A_256]: (k3_xboole_0(A_256, A_256)=A_256)), inference(superposition, [status(thm), theory('equality')], [c_2377, c_22])).
% 4.63/1.87  tff(c_3093, plain, (![A_335, B_336]: (k5_xboole_0(k5_xboole_0(A_335, B_336), k3_xboole_0(A_335, B_336))=k2_xboole_0(A_335, B_336))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.63/1.87  tff(c_3111, plain, (![A_17]: (k5_xboole_0(k1_xboole_0, k3_xboole_0(A_17, A_17))=k2_xboole_0(A_17, A_17))), inference(superposition, [status(thm), theory('equality')], [c_2599, c_3093])).
% 4.63/1.87  tff(c_3127, plain, (![A_17]: (k5_xboole_0(k1_xboole_0, A_17)=A_17)), inference(demodulation, [status(thm), theory('equality')], [c_2398, c_2386, c_3111])).
% 4.63/1.87  tff(c_3170, plain, (![A_17, C_339]: (k5_xboole_0(A_17, k5_xboole_0(A_17, C_339))=k5_xboole_0(k1_xboole_0, C_339))), inference(superposition, [status(thm), theory('equality')], [c_2599, c_3130])).
% 4.63/1.87  tff(c_3951, plain, (![A_363, C_364]: (k5_xboole_0(A_363, k5_xboole_0(A_363, C_364))=C_364)), inference(demodulation, [status(thm), theory('equality')], [c_3127, c_3170])).
% 4.63/1.87  tff(c_4002, plain, (![B_338, A_337]: (k5_xboole_0(B_338, k5_xboole_0(A_337, B_338))=k5_xboole_0(A_337, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_3147, c_3951])).
% 4.63/1.87  tff(c_4055, plain, (![B_365, A_366]: (k5_xboole_0(B_365, k5_xboole_0(A_366, B_365))=A_366)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_4002])).
% 4.63/1.87  tff(c_4046, plain, (![B_338, A_337]: (k5_xboole_0(B_338, k5_xboole_0(A_337, B_338))=A_337)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_4002])).
% 4.63/1.87  tff(c_4058, plain, (![A_366, B_365]: (k5_xboole_0(k5_xboole_0(A_366, B_365), A_366)=B_365)), inference(superposition, [status(thm), theory('equality')], [c_4055, c_4046])).
% 4.63/1.87  tff(c_2326, plain, (k2_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2307, c_66])).
% 4.63/1.87  tff(c_2306, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_60])).
% 4.63/1.87  tff(c_2501, plain, (![A_273, B_274, C_275]: (r1_tarski(k3_xboole_0(A_273, B_274), k2_xboole_0(A_273, C_275)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.63/1.87  tff(c_2513, plain, (![A_19, B_274]: (r1_tarski(k3_xboole_0(A_19, B_274), A_19))), inference(superposition, [status(thm), theory('equality')], [c_24, c_2501])).
% 4.63/1.87  tff(c_2739, plain, (![B_307, A_308]: (k1_tarski(B_307)=A_308 | k1_xboole_0=A_308 | ~r1_tarski(A_308, k1_tarski(B_307)))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.63/1.87  tff(c_2758, plain, (![A_308]: (k1_tarski('#skF_3')=A_308 | k1_xboole_0=A_308 | ~r1_tarski(A_308, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2307, c_2739])).
% 4.63/1.87  tff(c_2765, plain, (![A_309]: (A_309='#skF_4' | k1_xboole_0=A_309 | ~r1_tarski(A_309, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2307, c_2758])).
% 4.63/1.87  tff(c_2783, plain, (![B_274]: (k3_xboole_0('#skF_4', B_274)='#skF_4' | k3_xboole_0('#skF_4', B_274)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2513, c_2765])).
% 4.63/1.87  tff(c_3108, plain, (![B_274]: (k5_xboole_0(k5_xboole_0('#skF_4', B_274), k1_xboole_0)=k2_xboole_0('#skF_4', B_274) | k3_xboole_0('#skF_4', B_274)='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2783, c_3093])).
% 4.63/1.87  tff(c_3126, plain, (![B_274]: (k5_xboole_0('#skF_4', B_274)=k2_xboole_0('#skF_4', B_274) | k3_xboole_0('#skF_4', B_274)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_3108])).
% 4.63/1.87  tff(c_4530, plain, (![B_378]: (k5_xboole_0('#skF_4', k2_xboole_0('#skF_4', B_378))=B_378 | k3_xboole_0('#skF_4', B_378)='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3126, c_3951])).
% 4.63/1.87  tff(c_4578, plain, (k5_xboole_0('#skF_4', '#skF_4')='#skF_5' | k3_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_2326, c_4530])).
% 4.63/1.87  tff(c_4591, plain, (k1_xboole_0='#skF_5' | k3_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2599, c_4578])).
% 4.63/1.87  tff(c_4592, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_2306, c_4591])).
% 4.63/1.87  tff(c_36, plain, (![A_32, B_33]: (k5_xboole_0(k5_xboole_0(A_32, B_33), k3_xboole_0(A_32, B_33))=k2_xboole_0(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.63/1.87  tff(c_4602, plain, (k5_xboole_0(k5_xboole_0('#skF_4', '#skF_5'), '#skF_4')=k2_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_4592, c_36])).
% 4.63/1.87  tff(c_4638, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4058, c_2326, c_4602])).
% 4.63/1.87  tff(c_4640, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2358, c_4638])).
% 4.63/1.87  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.63/1.87  
% 4.63/1.87  Inference rules
% 4.63/1.87  ----------------------
% 4.63/1.87  #Ref     : 0
% 4.63/1.87  #Sup     : 1088
% 4.63/1.87  #Fact    : 2
% 4.63/1.87  #Define  : 0
% 4.63/1.87  #Split   : 9
% 4.63/1.87  #Chain   : 0
% 4.63/1.87  #Close   : 0
% 4.63/1.87  
% 4.63/1.87  Ordering : KBO
% 4.63/1.87  
% 4.63/1.87  Simplification rules
% 4.63/1.87  ----------------------
% 4.63/1.87  #Subsume      : 99
% 4.63/1.87  #Demod        : 628
% 4.63/1.87  #Tautology    : 725
% 4.63/1.87  #SimpNegUnit  : 34
% 4.63/1.87  #BackRed      : 10
% 4.63/1.87  
% 4.63/1.87  #Partial instantiations: 0
% 4.63/1.87  #Strategies tried      : 1
% 4.63/1.87  
% 4.63/1.87  Timing (in seconds)
% 4.63/1.87  ----------------------
% 4.63/1.88  Preprocessing        : 0.35
% 4.63/1.88  Parsing              : 0.18
% 4.63/1.88  CNF conversion       : 0.02
% 4.63/1.88  Main loop            : 0.75
% 4.63/1.88  Inferencing          : 0.28
% 4.63/1.88  Reduction            : 0.27
% 4.63/1.88  Demodulation         : 0.20
% 4.63/1.88  BG Simplification    : 0.03
% 4.63/1.88  Subsumption          : 0.11
% 4.63/1.88  Abstraction          : 0.03
% 4.63/1.88  MUC search           : 0.00
% 4.63/1.88  Cooper               : 0.00
% 4.63/1.88  Total                : 1.14
% 4.63/1.88  Index Insertion      : 0.00
% 4.63/1.88  Index Deletion       : 0.00
% 4.63/1.88  Index Matching       : 0.00
% 4.63/1.88  BG Taut test         : 0.00
%------------------------------------------------------------------------------
