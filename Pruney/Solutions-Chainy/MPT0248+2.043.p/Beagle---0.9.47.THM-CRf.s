%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:09 EST 2020

% Result     : Theorem 5.95s
% Output     : CNFRefutation 6.20s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 308 expanded)
%              Number of leaves         :   45 ( 117 expanded)
%              Depth                    :   13
%              Number of atoms          :  149 ( 488 expanded)
%              Number of equality atoms :   75 ( 362 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_129,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_103,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_81,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_108,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_79,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_85,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_83,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_71,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k4_xboole_0(k2_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l98_xboole_1)).

tff(f_77,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_67,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(c_68,plain,
    ( k1_tarski('#skF_3') != '#skF_5'
    | k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_122,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_60,plain,(
    ! [A_66,B_67] :
      ( r1_tarski(k1_tarski(A_66),B_67)
      | ~ r2_hidden(A_66,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_66,plain,
    ( k1_xboole_0 != '#skF_5'
    | k1_tarski('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_123,plain,(
    k1_tarski('#skF_3') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_72,plain,(
    k2_xboole_0('#skF_4','#skF_5') = k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_125,plain,(
    ! [A_80,B_81] : r1_tarski(A_80,k2_xboole_0(A_80,B_81)) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_128,plain,(
    r1_tarski('#skF_4',k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_125])).

tff(c_848,plain,(
    ! [B_135,A_136] :
      ( B_135 = A_136
      | ~ r1_tarski(B_135,A_136)
      | ~ r1_tarski(A_136,B_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_858,plain,
    ( k1_tarski('#skF_3') = '#skF_4'
    | ~ r1_tarski(k1_tarski('#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_128,c_848])).

tff(c_869,plain,(
    ~ r1_tarski(k1_tarski('#skF_3'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_123,c_858])).

tff(c_878,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_869])).

tff(c_62,plain,(
    ! [A_68,B_69] :
      ( r1_xboole_0(k1_tarski(A_68),B_69)
      | r2_hidden(A_68,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_421,plain,(
    ! [A_107,B_108] :
      ( k3_xboole_0(A_107,B_108) = A_107
      | ~ r1_tarski(A_107,B_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_448,plain,(
    k3_xboole_0('#skF_4',k1_tarski('#skF_3')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_128,c_421])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_5] :
      ( v1_xboole_0(A_5)
      | r2_hidden('#skF_1'(A_5),A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_803,plain,(
    ! [A_129,B_130,C_131] :
      ( ~ r1_xboole_0(A_129,B_130)
      | ~ r2_hidden(C_131,k3_xboole_0(A_129,B_130)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_910,plain,(
    ! [A_138,B_139] :
      ( ~ r1_xboole_0(A_138,B_139)
      | v1_xboole_0(k3_xboole_0(A_138,B_139)) ) ),
    inference(resolution,[status(thm)],[c_8,c_803])).

tff(c_946,plain,(
    ! [B_141,A_142] :
      ( ~ r1_xboole_0(B_141,A_142)
      | v1_xboole_0(k3_xboole_0(A_142,B_141)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_910])).

tff(c_955,plain,
    ( ~ r1_xboole_0(k1_tarski('#skF_3'),'#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_448,c_946])).

tff(c_974,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_955])).

tff(c_1049,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_974])).

tff(c_1053,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_878,c_1049])).

tff(c_1054,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_955])).

tff(c_10,plain,(
    ! [A_9] :
      ( k1_xboole_0 = A_9
      | ~ v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1058,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1054,c_10])).

tff(c_1062,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_122,c_1058])).

tff(c_1063,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_24,plain,(
    ! [A_19,B_20] : k5_xboole_0(A_19,k3_xboole_0(A_19,B_20)) = k4_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1085,plain,(
    ! [B_154,A_155] : k5_xboole_0(B_154,A_155) = k5_xboole_0(A_155,B_154) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_36,plain,(
    ! [A_31] : k5_xboole_0(A_31,k1_xboole_0) = A_31 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1101,plain,(
    ! [A_155] : k5_xboole_0(k1_xboole_0,A_155) = A_155 ),
    inference(superposition,[status(thm),theory(equality)],[c_1085,c_36])).

tff(c_42,plain,(
    ! [A_37] : k5_xboole_0(A_37,A_37) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2093,plain,(
    ! [A_226,B_227,C_228] : k5_xboole_0(k5_xboole_0(A_226,B_227),C_228) = k5_xboole_0(A_226,k5_xboole_0(B_227,C_228)) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_2150,plain,(
    ! [A_37,C_228] : k5_xboole_0(A_37,k5_xboole_0(A_37,C_228)) = k5_xboole_0(k1_xboole_0,C_228) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_2093])).

tff(c_2171,plain,(
    ! [A_229,C_230] : k5_xboole_0(A_229,k5_xboole_0(A_229,C_230)) = C_230 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1101,c_2150])).

tff(c_6776,plain,(
    ! [A_387,B_388] : k5_xboole_0(A_387,k4_xboole_0(A_387,B_388)) = k3_xboole_0(A_387,B_388) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_2171])).

tff(c_30,plain,(
    ! [A_26,B_27] : r1_tarski(k3_xboole_0(A_26,B_27),A_26) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1402,plain,(
    ! [A_178,B_179] :
      ( k3_xboole_0(A_178,B_179) = A_178
      | ~ r1_tarski(A_178,B_179) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_4384,plain,(
    ! [A_330,B_331] : k3_xboole_0(k3_xboole_0(A_330,B_331),A_330) = k3_xboole_0(A_330,B_331) ),
    inference(resolution,[status(thm)],[c_30,c_1402])).

tff(c_1777,plain,(
    ! [A_204,B_205] : k5_xboole_0(A_204,k3_xboole_0(A_204,B_205)) = k4_xboole_0(A_204,B_205) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1802,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1777])).

tff(c_4393,plain,(
    ! [A_330,B_331] : k5_xboole_0(A_330,k3_xboole_0(A_330,B_331)) = k4_xboole_0(A_330,k3_xboole_0(A_330,B_331)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4384,c_1802])).

tff(c_4529,plain,(
    ! [A_330,B_331] : k4_xboole_0(A_330,k3_xboole_0(A_330,B_331)) = k4_xboole_0(A_330,B_331) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_4393])).

tff(c_1064,plain,(
    k1_tarski('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_1065,plain,(
    k2_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1064,c_72])).

tff(c_3113,plain,(
    ! [A_266,B_267] : k4_xboole_0(k2_xboole_0(A_266,B_267),k3_xboole_0(A_266,B_267)) = k5_xboole_0(A_266,B_267) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_3152,plain,(
    k4_xboole_0('#skF_4',k3_xboole_0('#skF_4','#skF_5')) = k5_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1065,c_3113])).

tff(c_6359,plain,(
    k5_xboole_0('#skF_4','#skF_5') = k4_xboole_0('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4529,c_3152])).

tff(c_2168,plain,(
    ! [A_37,C_228] : k5_xboole_0(A_37,k5_xboole_0(A_37,C_228)) = C_228 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1101,c_2150])).

tff(c_6432,plain,(
    k5_xboole_0('#skF_4',k4_xboole_0('#skF_4','#skF_5')) = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_6359,c_2168])).

tff(c_6782,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_6776,c_6432])).

tff(c_1281,plain,(
    ! [A_161,B_162] :
      ( r1_xboole_0(k1_tarski(A_161),B_162)
      | r2_hidden(A_161,B_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1284,plain,(
    ! [B_162] :
      ( r1_xboole_0('#skF_4',B_162)
      | r2_hidden('#skF_3',B_162) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1064,c_1281])).

tff(c_1310,plain,(
    ! [A_167,B_168] :
      ( r1_tarski(k1_tarski(A_167),B_168)
      | ~ r2_hidden(A_167,B_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1314,plain,(
    ! [B_169] :
      ( r1_tarski('#skF_4',B_169)
      | ~ r2_hidden('#skF_3',B_169) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1064,c_1310])).

tff(c_1318,plain,(
    ! [B_162] :
      ( r1_tarski('#skF_4',B_162)
      | r1_xboole_0('#skF_4',B_162) ) ),
    inference(resolution,[status(thm)],[c_1284,c_1314])).

tff(c_1845,plain,(
    ! [A_208,B_209,C_210] :
      ( ~ r1_xboole_0(A_208,B_209)
      | ~ r2_hidden(C_210,k3_xboole_0(A_208,B_209)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2835,plain,(
    ! [A_253,B_254] :
      ( ~ r1_xboole_0(A_253,B_254)
      | v1_xboole_0(k3_xboole_0(A_253,B_254)) ) ),
    inference(resolution,[status(thm)],[c_8,c_1845])).

tff(c_3415,plain,(
    ! [A_276,B_277] :
      ( k3_xboole_0(A_276,B_277) = k1_xboole_0
      | ~ r1_xboole_0(A_276,B_277) ) ),
    inference(resolution,[status(thm)],[c_2835,c_10])).

tff(c_3457,plain,(
    ! [B_162] :
      ( k3_xboole_0('#skF_4',B_162) = k1_xboole_0
      | r1_tarski('#skF_4',B_162) ) ),
    inference(resolution,[status(thm)],[c_1318,c_3415])).

tff(c_70,plain,
    ( k1_tarski('#skF_3') != '#skF_5'
    | k1_tarski('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_1133,plain,(
    '#skF_5' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1064,c_1064,c_70])).

tff(c_1725,plain,(
    ! [B_201,A_202] :
      ( B_201 = A_202
      | ~ r1_tarski(B_201,A_202)
      | ~ r1_tarski(A_202,B_201) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1741,plain,(
    ! [A_26,B_27] :
      ( k3_xboole_0(A_26,B_27) = A_26
      | ~ r1_tarski(A_26,k3_xboole_0(A_26,B_27)) ) ),
    inference(resolution,[status(thm)],[c_30,c_1725])).

tff(c_6865,plain,
    ( k3_xboole_0('#skF_4','#skF_5') = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_6782,c_1741])).

tff(c_6970,plain,
    ( '#skF_5' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6782,c_6865])).

tff(c_6971,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_1133,c_6970])).

tff(c_6993,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3457,c_6971])).

tff(c_6996,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6782,c_6993])).

tff(c_6998,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1063,c_6996])).

tff(c_6999,plain,(
    k1_tarski('#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_7000,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_34,plain,(
    ! [A_30] : k3_xboole_0(A_30,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_7003,plain,(
    ! [A_30] : k3_xboole_0(A_30,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7000,c_7000,c_34])).

tff(c_7045,plain,(
    ! [A_393,B_394] : r1_tarski(k3_xboole_0(A_393,B_394),A_393) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_7048,plain,(
    ! [A_30] : r1_tarski('#skF_4',A_30) ),
    inference(superposition,[status(thm),theory(equality)],[c_7003,c_7045])).

tff(c_7307,plain,(
    ! [A_415,B_416] :
      ( k2_xboole_0(A_415,B_416) = B_416
      | ~ r1_tarski(A_415,B_416) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_7333,plain,(
    ! [A_30] : k2_xboole_0('#skF_4',A_30) = A_30 ),
    inference(resolution,[status(thm)],[c_7048,c_7307])).

tff(c_7428,plain,(
    k1_tarski('#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7333,c_72])).

tff(c_7430,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6999,c_7428])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:02:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.95/2.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.95/2.28  
% 5.95/2.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.95/2.28  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 5.95/2.28  
% 5.95/2.28  %Foreground sorts:
% 5.95/2.28  
% 5.95/2.28  
% 5.95/2.28  %Background operators:
% 5.95/2.28  
% 5.95/2.28  
% 5.95/2.28  %Foreground operators:
% 5.95/2.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.95/2.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.95/2.28  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.95/2.28  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.95/2.28  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.95/2.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.95/2.28  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.95/2.28  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.95/2.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.95/2.28  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.95/2.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.95/2.28  tff('#skF_5', type, '#skF_5': $i).
% 5.95/2.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.95/2.28  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.95/2.28  tff('#skF_3', type, '#skF_3': $i).
% 5.95/2.28  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.95/2.28  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.95/2.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.95/2.28  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.95/2.28  tff('#skF_4', type, '#skF_4': $i).
% 5.95/2.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.95/2.28  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.95/2.28  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.95/2.28  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.95/2.28  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.95/2.28  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.95/2.28  
% 6.20/2.30  tff(f_129, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 6.20/2.30  tff(f_103, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 6.20/2.30  tff(f_81, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 6.20/2.30  tff(f_59, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.20/2.30  tff(f_108, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 6.20/2.30  tff(f_75, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 6.20/2.30  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 6.20/2.30  tff(f_35, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 6.20/2.30  tff(f_53, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 6.20/2.30  tff(f_39, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 6.20/2.30  tff(f_63, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 6.20/2.30  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 6.20/2.30  tff(f_79, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 6.20/2.30  tff(f_85, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 6.20/2.30  tff(f_83, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 6.20/2.30  tff(f_71, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 6.20/2.30  tff(f_61, axiom, (![A, B]: (k5_xboole_0(A, B) = k4_xboole_0(k2_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l98_xboole_1)).
% 6.20/2.30  tff(f_77, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 6.20/2.30  tff(f_67, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 6.20/2.30  tff(c_68, plain, (k1_tarski('#skF_3')!='#skF_5' | k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_129])).
% 6.20/2.30  tff(c_122, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_68])).
% 6.20/2.30  tff(c_60, plain, (![A_66, B_67]: (r1_tarski(k1_tarski(A_66), B_67) | ~r2_hidden(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.20/2.30  tff(c_66, plain, (k1_xboole_0!='#skF_5' | k1_tarski('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_129])).
% 6.20/2.30  tff(c_123, plain, (k1_tarski('#skF_3')!='#skF_4'), inference(splitLeft, [status(thm)], [c_66])).
% 6.20/2.30  tff(c_72, plain, (k2_xboole_0('#skF_4', '#skF_5')=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_129])).
% 6.20/2.30  tff(c_125, plain, (![A_80, B_81]: (r1_tarski(A_80, k2_xboole_0(A_80, B_81)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.20/2.30  tff(c_128, plain, (r1_tarski('#skF_4', k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_72, c_125])).
% 6.20/2.30  tff(c_848, plain, (![B_135, A_136]: (B_135=A_136 | ~r1_tarski(B_135, A_136) | ~r1_tarski(A_136, B_135))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.20/2.30  tff(c_858, plain, (k1_tarski('#skF_3')='#skF_4' | ~r1_tarski(k1_tarski('#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_128, c_848])).
% 6.20/2.30  tff(c_869, plain, (~r1_tarski(k1_tarski('#skF_3'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_123, c_858])).
% 6.20/2.30  tff(c_878, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_60, c_869])).
% 6.20/2.30  tff(c_62, plain, (![A_68, B_69]: (r1_xboole_0(k1_tarski(A_68), B_69) | r2_hidden(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_108])).
% 6.20/2.30  tff(c_421, plain, (![A_107, B_108]: (k3_xboole_0(A_107, B_108)=A_107 | ~r1_tarski(A_107, B_108))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.20/2.30  tff(c_448, plain, (k3_xboole_0('#skF_4', k1_tarski('#skF_3'))='#skF_4'), inference(resolution, [status(thm)], [c_128, c_421])).
% 6.20/2.30  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.20/2.30  tff(c_8, plain, (![A_5]: (v1_xboole_0(A_5) | r2_hidden('#skF_1'(A_5), A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.20/2.30  tff(c_803, plain, (![A_129, B_130, C_131]: (~r1_xboole_0(A_129, B_130) | ~r2_hidden(C_131, k3_xboole_0(A_129, B_130)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.20/2.30  tff(c_910, plain, (![A_138, B_139]: (~r1_xboole_0(A_138, B_139) | v1_xboole_0(k3_xboole_0(A_138, B_139)))), inference(resolution, [status(thm)], [c_8, c_803])).
% 6.20/2.30  tff(c_946, plain, (![B_141, A_142]: (~r1_xboole_0(B_141, A_142) | v1_xboole_0(k3_xboole_0(A_142, B_141)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_910])).
% 6.20/2.30  tff(c_955, plain, (~r1_xboole_0(k1_tarski('#skF_3'), '#skF_4') | v1_xboole_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_448, c_946])).
% 6.20/2.30  tff(c_974, plain, (~r1_xboole_0(k1_tarski('#skF_3'), '#skF_4')), inference(splitLeft, [status(thm)], [c_955])).
% 6.20/2.30  tff(c_1049, plain, (r2_hidden('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_62, c_974])).
% 6.20/2.30  tff(c_1053, plain, $false, inference(negUnitSimplification, [status(thm)], [c_878, c_1049])).
% 6.20/2.30  tff(c_1054, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_955])).
% 6.20/2.30  tff(c_10, plain, (![A_9]: (k1_xboole_0=A_9 | ~v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.20/2.30  tff(c_1058, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_1054, c_10])).
% 6.20/2.30  tff(c_1062, plain, $false, inference(negUnitSimplification, [status(thm)], [c_122, c_1058])).
% 6.20/2.30  tff(c_1063, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_66])).
% 6.20/2.30  tff(c_24, plain, (![A_19, B_20]: (k5_xboole_0(A_19, k3_xboole_0(A_19, B_20))=k4_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.20/2.30  tff(c_1085, plain, (![B_154, A_155]: (k5_xboole_0(B_154, A_155)=k5_xboole_0(A_155, B_154))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.20/2.30  tff(c_36, plain, (![A_31]: (k5_xboole_0(A_31, k1_xboole_0)=A_31)), inference(cnfTransformation, [status(thm)], [f_79])).
% 6.20/2.30  tff(c_1101, plain, (![A_155]: (k5_xboole_0(k1_xboole_0, A_155)=A_155)), inference(superposition, [status(thm), theory('equality')], [c_1085, c_36])).
% 6.20/2.30  tff(c_42, plain, (![A_37]: (k5_xboole_0(A_37, A_37)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.20/2.30  tff(c_2093, plain, (![A_226, B_227, C_228]: (k5_xboole_0(k5_xboole_0(A_226, B_227), C_228)=k5_xboole_0(A_226, k5_xboole_0(B_227, C_228)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 6.20/2.30  tff(c_2150, plain, (![A_37, C_228]: (k5_xboole_0(A_37, k5_xboole_0(A_37, C_228))=k5_xboole_0(k1_xboole_0, C_228))), inference(superposition, [status(thm), theory('equality')], [c_42, c_2093])).
% 6.20/2.30  tff(c_2171, plain, (![A_229, C_230]: (k5_xboole_0(A_229, k5_xboole_0(A_229, C_230))=C_230)), inference(demodulation, [status(thm), theory('equality')], [c_1101, c_2150])).
% 6.20/2.30  tff(c_6776, plain, (![A_387, B_388]: (k5_xboole_0(A_387, k4_xboole_0(A_387, B_388))=k3_xboole_0(A_387, B_388))), inference(superposition, [status(thm), theory('equality')], [c_24, c_2171])).
% 6.20/2.30  tff(c_30, plain, (![A_26, B_27]: (r1_tarski(k3_xboole_0(A_26, B_27), A_26))), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.20/2.30  tff(c_1402, plain, (![A_178, B_179]: (k3_xboole_0(A_178, B_179)=A_178 | ~r1_tarski(A_178, B_179))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.20/2.30  tff(c_4384, plain, (![A_330, B_331]: (k3_xboole_0(k3_xboole_0(A_330, B_331), A_330)=k3_xboole_0(A_330, B_331))), inference(resolution, [status(thm)], [c_30, c_1402])).
% 6.20/2.30  tff(c_1777, plain, (![A_204, B_205]: (k5_xboole_0(A_204, k3_xboole_0(A_204, B_205))=k4_xboole_0(A_204, B_205))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.20/2.30  tff(c_1802, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1777])).
% 6.20/2.30  tff(c_4393, plain, (![A_330, B_331]: (k5_xboole_0(A_330, k3_xboole_0(A_330, B_331))=k4_xboole_0(A_330, k3_xboole_0(A_330, B_331)))), inference(superposition, [status(thm), theory('equality')], [c_4384, c_1802])).
% 6.20/2.30  tff(c_4529, plain, (![A_330, B_331]: (k4_xboole_0(A_330, k3_xboole_0(A_330, B_331))=k4_xboole_0(A_330, B_331))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_4393])).
% 6.20/2.30  tff(c_1064, plain, (k1_tarski('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_66])).
% 6.20/2.30  tff(c_1065, plain, (k2_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1064, c_72])).
% 6.20/2.30  tff(c_3113, plain, (![A_266, B_267]: (k4_xboole_0(k2_xboole_0(A_266, B_267), k3_xboole_0(A_266, B_267))=k5_xboole_0(A_266, B_267))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.20/2.30  tff(c_3152, plain, (k4_xboole_0('#skF_4', k3_xboole_0('#skF_4', '#skF_5'))=k5_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1065, c_3113])).
% 6.20/2.30  tff(c_6359, plain, (k5_xboole_0('#skF_4', '#skF_5')=k4_xboole_0('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4529, c_3152])).
% 6.20/2.30  tff(c_2168, plain, (![A_37, C_228]: (k5_xboole_0(A_37, k5_xboole_0(A_37, C_228))=C_228)), inference(demodulation, [status(thm), theory('equality')], [c_1101, c_2150])).
% 6.20/2.30  tff(c_6432, plain, (k5_xboole_0('#skF_4', k4_xboole_0('#skF_4', '#skF_5'))='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_6359, c_2168])).
% 6.20/2.30  tff(c_6782, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_6776, c_6432])).
% 6.20/2.30  tff(c_1281, plain, (![A_161, B_162]: (r1_xboole_0(k1_tarski(A_161), B_162) | r2_hidden(A_161, B_162))), inference(cnfTransformation, [status(thm)], [f_108])).
% 6.20/2.30  tff(c_1284, plain, (![B_162]: (r1_xboole_0('#skF_4', B_162) | r2_hidden('#skF_3', B_162))), inference(superposition, [status(thm), theory('equality')], [c_1064, c_1281])).
% 6.20/2.30  tff(c_1310, plain, (![A_167, B_168]: (r1_tarski(k1_tarski(A_167), B_168) | ~r2_hidden(A_167, B_168))), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.20/2.30  tff(c_1314, plain, (![B_169]: (r1_tarski('#skF_4', B_169) | ~r2_hidden('#skF_3', B_169))), inference(superposition, [status(thm), theory('equality')], [c_1064, c_1310])).
% 6.20/2.30  tff(c_1318, plain, (![B_162]: (r1_tarski('#skF_4', B_162) | r1_xboole_0('#skF_4', B_162))), inference(resolution, [status(thm)], [c_1284, c_1314])).
% 6.20/2.30  tff(c_1845, plain, (![A_208, B_209, C_210]: (~r1_xboole_0(A_208, B_209) | ~r2_hidden(C_210, k3_xboole_0(A_208, B_209)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.20/2.30  tff(c_2835, plain, (![A_253, B_254]: (~r1_xboole_0(A_253, B_254) | v1_xboole_0(k3_xboole_0(A_253, B_254)))), inference(resolution, [status(thm)], [c_8, c_1845])).
% 6.20/2.30  tff(c_3415, plain, (![A_276, B_277]: (k3_xboole_0(A_276, B_277)=k1_xboole_0 | ~r1_xboole_0(A_276, B_277))), inference(resolution, [status(thm)], [c_2835, c_10])).
% 6.20/2.30  tff(c_3457, plain, (![B_162]: (k3_xboole_0('#skF_4', B_162)=k1_xboole_0 | r1_tarski('#skF_4', B_162))), inference(resolution, [status(thm)], [c_1318, c_3415])).
% 6.20/2.30  tff(c_70, plain, (k1_tarski('#skF_3')!='#skF_5' | k1_tarski('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_129])).
% 6.20/2.30  tff(c_1133, plain, ('#skF_5'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1064, c_1064, c_70])).
% 6.20/2.30  tff(c_1725, plain, (![B_201, A_202]: (B_201=A_202 | ~r1_tarski(B_201, A_202) | ~r1_tarski(A_202, B_201))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.20/2.30  tff(c_1741, plain, (![A_26, B_27]: (k3_xboole_0(A_26, B_27)=A_26 | ~r1_tarski(A_26, k3_xboole_0(A_26, B_27)))), inference(resolution, [status(thm)], [c_30, c_1725])).
% 6.20/2.30  tff(c_6865, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_4' | ~r1_tarski('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_6782, c_1741])).
% 6.20/2.30  tff(c_6970, plain, ('#skF_5'='#skF_4' | ~r1_tarski('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_6782, c_6865])).
% 6.20/2.30  tff(c_6971, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_1133, c_6970])).
% 6.20/2.30  tff(c_6993, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_3457, c_6971])).
% 6.20/2.30  tff(c_6996, plain, (k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_6782, c_6993])).
% 6.20/2.30  tff(c_6998, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1063, c_6996])).
% 6.20/2.30  tff(c_6999, plain, (k1_tarski('#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_68])).
% 6.20/2.30  tff(c_7000, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_68])).
% 6.20/2.30  tff(c_34, plain, (![A_30]: (k3_xboole_0(A_30, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.20/2.30  tff(c_7003, plain, (![A_30]: (k3_xboole_0(A_30, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7000, c_7000, c_34])).
% 6.20/2.30  tff(c_7045, plain, (![A_393, B_394]: (r1_tarski(k3_xboole_0(A_393, B_394), A_393))), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.20/2.30  tff(c_7048, plain, (![A_30]: (r1_tarski('#skF_4', A_30))), inference(superposition, [status(thm), theory('equality')], [c_7003, c_7045])).
% 6.20/2.30  tff(c_7307, plain, (![A_415, B_416]: (k2_xboole_0(A_415, B_416)=B_416 | ~r1_tarski(A_415, B_416))), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.20/2.30  tff(c_7333, plain, (![A_30]: (k2_xboole_0('#skF_4', A_30)=A_30)), inference(resolution, [status(thm)], [c_7048, c_7307])).
% 6.20/2.30  tff(c_7428, plain, (k1_tarski('#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_7333, c_72])).
% 6.20/2.30  tff(c_7430, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6999, c_7428])).
% 6.20/2.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.20/2.30  
% 6.20/2.30  Inference rules
% 6.20/2.30  ----------------------
% 6.20/2.30  #Ref     : 0
% 6.20/2.30  #Sup     : 1755
% 6.20/2.30  #Fact    : 0
% 6.20/2.30  #Define  : 0
% 6.20/2.30  #Split   : 7
% 6.20/2.30  #Chain   : 0
% 6.20/2.30  #Close   : 0
% 6.20/2.30  
% 6.20/2.30  Ordering : KBO
% 6.20/2.30  
% 6.20/2.30  Simplification rules
% 6.20/2.30  ----------------------
% 6.20/2.30  #Subsume      : 242
% 6.20/2.30  #Demod        : 966
% 6.20/2.30  #Tautology    : 972
% 6.20/2.30  #SimpNegUnit  : 57
% 6.20/2.30  #BackRed      : 14
% 6.20/2.30  
% 6.20/2.30  #Partial instantiations: 0
% 6.20/2.30  #Strategies tried      : 1
% 6.20/2.30  
% 6.20/2.30  Timing (in seconds)
% 6.20/2.30  ----------------------
% 6.20/2.30  Preprocessing        : 0.41
% 6.20/2.30  Parsing              : 0.21
% 6.20/2.30  CNF conversion       : 0.03
% 6.20/2.30  Main loop            : 1.02
% 6.20/2.30  Inferencing          : 0.34
% 6.20/2.30  Reduction            : 0.40
% 6.20/2.30  Demodulation         : 0.31
% 6.20/2.30  BG Simplification    : 0.04
% 6.20/2.30  Subsumption          : 0.16
% 6.20/2.30  Abstraction          : 0.04
% 6.20/2.30  MUC search           : 0.00
% 6.20/2.30  Cooper               : 0.00
% 6.20/2.30  Total                : 1.47
% 6.20/2.30  Index Insertion      : 0.00
% 6.20/2.30  Index Deletion       : 0.00
% 6.20/2.30  Index Matching       : 0.00
% 6.20/2.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
