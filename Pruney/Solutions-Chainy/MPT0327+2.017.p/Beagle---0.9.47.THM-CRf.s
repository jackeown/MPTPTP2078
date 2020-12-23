%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:32 EST 2020

% Result     : Theorem 5.47s
% Output     : CNFRefutation 5.61s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 165 expanded)
%              Number of leaves         :   38 (  70 expanded)
%              Depth                    :   16
%              Number of atoms          :  121 ( 251 expanded)
%              Number of equality atoms :   43 (  79 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_72,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_99,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k4_xboole_0(B,k1_tarski(A)),k1_tarski(A)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_zfmisc_1)).

tff(f_74,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_46,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_54,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(f_56,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k3_xboole_0(B,C))
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).

tff(f_78,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_76,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_46,plain,(
    ! [A_31,B_32] : k2_xboole_0(A_31,k4_xboole_0(B_32,A_31)) = k2_xboole_0(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_70,plain,(
    k2_xboole_0(k4_xboole_0('#skF_5',k1_tarski('#skF_4')),k1_tarski('#skF_4')) != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_74,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),k4_xboole_0('#skF_5',k1_tarski('#skF_4'))) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_70])).

tff(c_75,plain,(
    k2_xboole_0('#skF_5',k1_tarski('#skF_4')) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_46,c_74])).

tff(c_48,plain,(
    ! [A_33] : k5_xboole_0(A_33,k1_xboole_0) = A_33 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_26,plain,(
    ! [A_8,B_9,C_10] :
      ( r2_hidden('#skF_2'(A_8,B_9,C_10),A_8)
      | r2_hidden('#skF_3'(A_8,B_9,C_10),C_10)
      | k4_xboole_0(A_8,B_9) = C_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_3198,plain,(
    ! [A_245,B_246,C_247] :
      ( ~ r2_hidden('#skF_2'(A_245,B_246,C_247),B_246)
      | r2_hidden('#skF_3'(A_245,B_246,C_247),C_247)
      | k4_xboole_0(A_245,B_246) = C_247 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_3207,plain,(
    ! [A_248,C_249] :
      ( r2_hidden('#skF_3'(A_248,A_248,C_249),C_249)
      | k4_xboole_0(A_248,A_248) = C_249 ) ),
    inference(resolution,[status(thm)],[c_26,c_3198])).

tff(c_34,plain,(
    ! [B_17] : r1_tarski(B_17,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_253,plain,(
    ! [A_100,C_101,B_102] :
      ( r2_hidden(A_100,C_101)
      | ~ r1_tarski(k2_tarski(A_100,B_102),C_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_261,plain,(
    ! [A_100,B_102] : r2_hidden(A_100,k2_tarski(A_100,B_102)) ),
    inference(resolution,[status(thm)],[c_34,c_253])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_28,plain,(
    ! [A_14] : k3_xboole_0(A_14,A_14) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_280,plain,(
    ! [A_107,B_108] : k5_xboole_0(A_107,k3_xboole_0(A_107,B_108)) = k4_xboole_0(A_107,B_108) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_292,plain,(
    ! [A_109] : k5_xboole_0(A_109,A_109) = k4_xboole_0(A_109,A_109) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_280])).

tff(c_299,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_292,c_48])).

tff(c_12,plain,(
    ! [D_13,B_9,A_8] :
      ( ~ r2_hidden(D_13,B_9)
      | ~ r2_hidden(D_13,k4_xboole_0(A_8,B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_361,plain,(
    ! [D_114] :
      ( ~ r2_hidden(D_114,k1_xboole_0)
      | ~ r2_hidden(D_114,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_299,c_12])).

tff(c_444,plain,(
    ! [B_128] :
      ( ~ r2_hidden('#skF_1'(k1_xboole_0,B_128),k1_xboole_0)
      | r1_tarski(k1_xboole_0,B_128) ) ),
    inference(resolution,[status(thm)],[c_8,c_361])).

tff(c_451,plain,(
    ! [B_129] : r1_tarski(k1_xboole_0,B_129) ),
    inference(resolution,[status(thm)],[c_8,c_444])).

tff(c_44,plain,(
    ! [A_29,B_30] :
      ( k3_xboole_0(A_29,B_30) = A_29
      | ~ r1_tarski(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_468,plain,(
    ! [B_130] : k3_xboole_0(k1_xboole_0,B_130) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_451,c_44])).

tff(c_36,plain,(
    ! [A_18,B_19] : k5_xboole_0(A_18,k3_xboole_0(A_18,B_19)) = k4_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_479,plain,(
    ! [B_130] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,B_130) ),
    inference(superposition,[status(thm),theory(equality)],[c_468,c_36])).

tff(c_508,plain,(
    ! [B_131] : k4_xboole_0(k1_xboole_0,B_131) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_479])).

tff(c_802,plain,(
    ! [D_143,B_144] :
      ( ~ r2_hidden(D_143,B_144)
      | ~ r2_hidden(D_143,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_508,c_12])).

tff(c_819,plain,(
    ! [A_100] : ~ r2_hidden(A_100,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_261,c_802])).

tff(c_3251,plain,(
    ! [A_248] : k4_xboole_0(A_248,A_248) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3207,c_819])).

tff(c_1463,plain,(
    ! [A_178,B_179,C_180] :
      ( r1_tarski(A_178,k3_xboole_0(B_179,C_180))
      | ~ r1_tarski(A_178,C_180)
      | ~ r1_tarski(A_178,B_179) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_4170,plain,(
    ! [A_293,B_294,C_295] :
      ( k3_xboole_0(A_293,k3_xboole_0(B_294,C_295)) = A_293
      | ~ r1_tarski(A_293,C_295)
      | ~ r1_tarski(A_293,B_294) ) ),
    inference(resolution,[status(thm)],[c_1463,c_44])).

tff(c_537,plain,(
    ! [A_132,B_133,C_134] : k3_xboole_0(k3_xboole_0(A_132,B_133),C_134) = k3_xboole_0(A_132,k3_xboole_0(B_133,C_134)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_188,plain,(
    ! [A_84,B_85,C_86] :
      ( r1_tarski(A_84,B_85)
      | ~ r1_tarski(A_84,k3_xboole_0(B_85,C_86)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_196,plain,(
    ! [B_85,C_86] : r1_tarski(k3_xboole_0(B_85,C_86),B_85) ),
    inference(resolution,[status(thm)],[c_34,c_188])).

tff(c_559,plain,(
    ! [A_132,B_133,C_134] : r1_tarski(k3_xboole_0(A_132,k3_xboole_0(B_133,C_134)),k3_xboole_0(A_132,B_133)) ),
    inference(superposition,[status(thm),theory(equality)],[c_537,c_196])).

tff(c_4411,plain,(
    ! [A_296,B_297,C_298] :
      ( r1_tarski(A_296,k3_xboole_0(A_296,B_297))
      | ~ r1_tarski(A_296,C_298)
      | ~ r1_tarski(A_296,B_297) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4170,c_559])).

tff(c_4440,plain,(
    ! [B_299,B_300] :
      ( r1_tarski(B_299,k3_xboole_0(B_299,B_300))
      | ~ r1_tarski(B_299,B_300) ) ),
    inference(resolution,[status(thm)],[c_34,c_4411])).

tff(c_72,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_327,plain,(
    ! [C_110,B_111,A_112] :
      ( r2_hidden(C_110,B_111)
      | ~ r2_hidden(C_110,A_112)
      | ~ r1_tarski(A_112,B_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_342,plain,(
    ! [B_111] :
      ( r2_hidden('#skF_4',B_111)
      | ~ r1_tarski('#skF_5',B_111) ) ),
    inference(resolution,[status(thm)],[c_72,c_327])).

tff(c_52,plain,(
    ! [A_36] : k2_tarski(A_36,A_36) = k1_tarski(A_36) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_836,plain,(
    ! [A_146,B_147,C_148] :
      ( r1_tarski(k2_tarski(A_146,B_147),C_148)
      | ~ r2_hidden(B_147,C_148)
      | ~ r2_hidden(A_146,C_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1374,plain,(
    ! [A_171,C_172] :
      ( r1_tarski(k1_tarski(A_171),C_172)
      | ~ r2_hidden(A_171,C_172)
      | ~ r2_hidden(A_171,C_172) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_836])).

tff(c_40,plain,(
    ! [A_23,B_24,C_25] :
      ( r1_tarski(A_23,B_24)
      | ~ r1_tarski(A_23,k3_xboole_0(B_24,C_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1404,plain,(
    ! [A_173,B_174,C_175] :
      ( r1_tarski(k1_tarski(A_173),B_174)
      | ~ r2_hidden(A_173,k3_xboole_0(B_174,C_175)) ) ),
    inference(resolution,[status(thm)],[c_1374,c_40])).

tff(c_1431,plain,(
    ! [B_174,C_175] :
      ( r1_tarski(k1_tarski('#skF_4'),B_174)
      | ~ r1_tarski('#skF_5',k3_xboole_0(B_174,C_175)) ) ),
    inference(resolution,[status(thm)],[c_342,c_1404])).

tff(c_4518,plain,(
    ! [B_300] :
      ( r1_tarski(k1_tarski('#skF_4'),'#skF_5')
      | ~ r1_tarski('#skF_5',B_300) ) ),
    inference(resolution,[status(thm)],[c_4440,c_1431])).

tff(c_4544,plain,(
    ! [B_301] : ~ r1_tarski('#skF_5',B_301) ),
    inference(splitLeft,[status(thm)],[c_4518])).

tff(c_4559,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_34,c_4544])).

tff(c_4560,plain,(
    r1_tarski(k1_tarski('#skF_4'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_4518])).

tff(c_4576,plain,(
    k3_xboole_0(k1_tarski('#skF_4'),'#skF_5') = k1_tarski('#skF_4') ),
    inference(resolution,[status(thm)],[c_4560,c_44])).

tff(c_868,plain,(
    ! [A_149,C_150] : k3_xboole_0(A_149,k3_xboole_0(A_149,C_150)) = k3_xboole_0(A_149,C_150) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_537])).

tff(c_894,plain,(
    ! [A_149,C_150] : k5_xboole_0(A_149,k3_xboole_0(A_149,C_150)) = k4_xboole_0(A_149,k3_xboole_0(A_149,C_150)) ),
    inference(superposition,[status(thm),theory(equality)],[c_868,c_36])).

tff(c_933,plain,(
    ! [A_149,C_150] : k4_xboole_0(A_149,k3_xboole_0(A_149,C_150)) = k4_xboole_0(A_149,C_150) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_894])).

tff(c_4639,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_4')) = k4_xboole_0(k1_tarski('#skF_4'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_4576,c_933])).

tff(c_4691,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),'#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3251,c_4639])).

tff(c_50,plain,(
    ! [A_34,B_35] : k5_xboole_0(A_34,k4_xboole_0(B_35,A_34)) = k2_xboole_0(A_34,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_4739,plain,(
    k2_xboole_0('#skF_5',k1_tarski('#skF_4')) = k5_xboole_0('#skF_5',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4691,c_50])).

tff(c_4759,plain,(
    k2_xboole_0('#skF_5',k1_tarski('#skF_4')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_4739])).

tff(c_4761,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_4759])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:15:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.47/2.06  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.47/2.07  
% 5.47/2.07  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.47/2.07  %$ r2_hidden > r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 5.47/2.07  
% 5.47/2.07  %Foreground sorts:
% 5.47/2.07  
% 5.47/2.07  
% 5.47/2.07  %Background operators:
% 5.47/2.07  
% 5.47/2.07  
% 5.47/2.07  %Foreground operators:
% 5.47/2.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.47/2.07  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.47/2.07  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.47/2.07  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.47/2.07  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.47/2.07  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.47/2.07  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.47/2.07  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.47/2.07  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.47/2.07  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.47/2.07  tff('#skF_5', type, '#skF_5': $i).
% 5.47/2.07  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.47/2.07  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.47/2.07  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.47/2.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.47/2.07  tff('#skF_4', type, '#skF_4': $i).
% 5.47/2.07  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 5.47/2.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.47/2.07  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.47/2.07  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.47/2.07  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.47/2.07  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.47/2.07  
% 5.61/2.09  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 5.61/2.09  tff(f_72, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 5.61/2.09  tff(f_99, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k4_xboole_0(B, k1_tarski(A)), k1_tarski(A)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t140_zfmisc_1)).
% 5.61/2.09  tff(f_74, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 5.61/2.09  tff(f_44, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 5.61/2.09  tff(f_52, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.61/2.09  tff(f_94, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 5.61/2.09  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 5.61/2.09  tff(f_46, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 5.61/2.09  tff(f_54, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.61/2.09  tff(f_70, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 5.61/2.09  tff(f_66, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 5.61/2.09  tff(f_56, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 5.61/2.09  tff(f_60, axiom, (![A, B, C]: (r1_tarski(A, k3_xboole_0(B, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_xboole_1)).
% 5.61/2.09  tff(f_78, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 5.61/2.09  tff(f_76, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 5.61/2.09  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.61/2.09  tff(c_46, plain, (![A_31, B_32]: (k2_xboole_0(A_31, k4_xboole_0(B_32, A_31))=k2_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.61/2.09  tff(c_70, plain, (k2_xboole_0(k4_xboole_0('#skF_5', k1_tarski('#skF_4')), k1_tarski('#skF_4'))!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.61/2.09  tff(c_74, plain, (k2_xboole_0(k1_tarski('#skF_4'), k4_xboole_0('#skF_5', k1_tarski('#skF_4')))!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_70])).
% 5.61/2.09  tff(c_75, plain, (k2_xboole_0('#skF_5', k1_tarski('#skF_4'))!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_46, c_74])).
% 5.61/2.09  tff(c_48, plain, (![A_33]: (k5_xboole_0(A_33, k1_xboole_0)=A_33)), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.61/2.09  tff(c_26, plain, (![A_8, B_9, C_10]: (r2_hidden('#skF_2'(A_8, B_9, C_10), A_8) | r2_hidden('#skF_3'(A_8, B_9, C_10), C_10) | k4_xboole_0(A_8, B_9)=C_10)), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.61/2.09  tff(c_3198, plain, (![A_245, B_246, C_247]: (~r2_hidden('#skF_2'(A_245, B_246, C_247), B_246) | r2_hidden('#skF_3'(A_245, B_246, C_247), C_247) | k4_xboole_0(A_245, B_246)=C_247)), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.61/2.09  tff(c_3207, plain, (![A_248, C_249]: (r2_hidden('#skF_3'(A_248, A_248, C_249), C_249) | k4_xboole_0(A_248, A_248)=C_249)), inference(resolution, [status(thm)], [c_26, c_3198])).
% 5.61/2.09  tff(c_34, plain, (![B_17]: (r1_tarski(B_17, B_17))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.61/2.09  tff(c_253, plain, (![A_100, C_101, B_102]: (r2_hidden(A_100, C_101) | ~r1_tarski(k2_tarski(A_100, B_102), C_101))), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.61/2.09  tff(c_261, plain, (![A_100, B_102]: (r2_hidden(A_100, k2_tarski(A_100, B_102)))), inference(resolution, [status(thm)], [c_34, c_253])).
% 5.61/2.09  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.61/2.09  tff(c_28, plain, (![A_14]: (k3_xboole_0(A_14, A_14)=A_14)), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.61/2.09  tff(c_280, plain, (![A_107, B_108]: (k5_xboole_0(A_107, k3_xboole_0(A_107, B_108))=k4_xboole_0(A_107, B_108))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.61/2.09  tff(c_292, plain, (![A_109]: (k5_xboole_0(A_109, A_109)=k4_xboole_0(A_109, A_109))), inference(superposition, [status(thm), theory('equality')], [c_28, c_280])).
% 5.61/2.09  tff(c_299, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_292, c_48])).
% 5.61/2.09  tff(c_12, plain, (![D_13, B_9, A_8]: (~r2_hidden(D_13, B_9) | ~r2_hidden(D_13, k4_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.61/2.09  tff(c_361, plain, (![D_114]: (~r2_hidden(D_114, k1_xboole_0) | ~r2_hidden(D_114, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_299, c_12])).
% 5.61/2.09  tff(c_444, plain, (![B_128]: (~r2_hidden('#skF_1'(k1_xboole_0, B_128), k1_xboole_0) | r1_tarski(k1_xboole_0, B_128))), inference(resolution, [status(thm)], [c_8, c_361])).
% 5.61/2.09  tff(c_451, plain, (![B_129]: (r1_tarski(k1_xboole_0, B_129))), inference(resolution, [status(thm)], [c_8, c_444])).
% 5.61/2.09  tff(c_44, plain, (![A_29, B_30]: (k3_xboole_0(A_29, B_30)=A_29 | ~r1_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.61/2.09  tff(c_468, plain, (![B_130]: (k3_xboole_0(k1_xboole_0, B_130)=k1_xboole_0)), inference(resolution, [status(thm)], [c_451, c_44])).
% 5.61/2.09  tff(c_36, plain, (![A_18, B_19]: (k5_xboole_0(A_18, k3_xboole_0(A_18, B_19))=k4_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.61/2.09  tff(c_479, plain, (![B_130]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, B_130))), inference(superposition, [status(thm), theory('equality')], [c_468, c_36])).
% 5.61/2.09  tff(c_508, plain, (![B_131]: (k4_xboole_0(k1_xboole_0, B_131)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_479])).
% 5.61/2.09  tff(c_802, plain, (![D_143, B_144]: (~r2_hidden(D_143, B_144) | ~r2_hidden(D_143, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_508, c_12])).
% 5.61/2.09  tff(c_819, plain, (![A_100]: (~r2_hidden(A_100, k1_xboole_0))), inference(resolution, [status(thm)], [c_261, c_802])).
% 5.61/2.09  tff(c_3251, plain, (![A_248]: (k4_xboole_0(A_248, A_248)=k1_xboole_0)), inference(resolution, [status(thm)], [c_3207, c_819])).
% 5.61/2.09  tff(c_1463, plain, (![A_178, B_179, C_180]: (r1_tarski(A_178, k3_xboole_0(B_179, C_180)) | ~r1_tarski(A_178, C_180) | ~r1_tarski(A_178, B_179))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.61/2.09  tff(c_4170, plain, (![A_293, B_294, C_295]: (k3_xboole_0(A_293, k3_xboole_0(B_294, C_295))=A_293 | ~r1_tarski(A_293, C_295) | ~r1_tarski(A_293, B_294))), inference(resolution, [status(thm)], [c_1463, c_44])).
% 5.61/2.09  tff(c_537, plain, (![A_132, B_133, C_134]: (k3_xboole_0(k3_xboole_0(A_132, B_133), C_134)=k3_xboole_0(A_132, k3_xboole_0(B_133, C_134)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.61/2.09  tff(c_188, plain, (![A_84, B_85, C_86]: (r1_tarski(A_84, B_85) | ~r1_tarski(A_84, k3_xboole_0(B_85, C_86)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.61/2.09  tff(c_196, plain, (![B_85, C_86]: (r1_tarski(k3_xboole_0(B_85, C_86), B_85))), inference(resolution, [status(thm)], [c_34, c_188])).
% 5.61/2.09  tff(c_559, plain, (![A_132, B_133, C_134]: (r1_tarski(k3_xboole_0(A_132, k3_xboole_0(B_133, C_134)), k3_xboole_0(A_132, B_133)))), inference(superposition, [status(thm), theory('equality')], [c_537, c_196])).
% 5.61/2.09  tff(c_4411, plain, (![A_296, B_297, C_298]: (r1_tarski(A_296, k3_xboole_0(A_296, B_297)) | ~r1_tarski(A_296, C_298) | ~r1_tarski(A_296, B_297))), inference(superposition, [status(thm), theory('equality')], [c_4170, c_559])).
% 5.61/2.09  tff(c_4440, plain, (![B_299, B_300]: (r1_tarski(B_299, k3_xboole_0(B_299, B_300)) | ~r1_tarski(B_299, B_300))), inference(resolution, [status(thm)], [c_34, c_4411])).
% 5.61/2.09  tff(c_72, plain, (r2_hidden('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.61/2.09  tff(c_327, plain, (![C_110, B_111, A_112]: (r2_hidden(C_110, B_111) | ~r2_hidden(C_110, A_112) | ~r1_tarski(A_112, B_111))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.61/2.09  tff(c_342, plain, (![B_111]: (r2_hidden('#skF_4', B_111) | ~r1_tarski('#skF_5', B_111))), inference(resolution, [status(thm)], [c_72, c_327])).
% 5.61/2.09  tff(c_52, plain, (![A_36]: (k2_tarski(A_36, A_36)=k1_tarski(A_36))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.61/2.09  tff(c_836, plain, (![A_146, B_147, C_148]: (r1_tarski(k2_tarski(A_146, B_147), C_148) | ~r2_hidden(B_147, C_148) | ~r2_hidden(A_146, C_148))), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.61/2.09  tff(c_1374, plain, (![A_171, C_172]: (r1_tarski(k1_tarski(A_171), C_172) | ~r2_hidden(A_171, C_172) | ~r2_hidden(A_171, C_172))), inference(superposition, [status(thm), theory('equality')], [c_52, c_836])).
% 5.61/2.09  tff(c_40, plain, (![A_23, B_24, C_25]: (r1_tarski(A_23, B_24) | ~r1_tarski(A_23, k3_xboole_0(B_24, C_25)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.61/2.09  tff(c_1404, plain, (![A_173, B_174, C_175]: (r1_tarski(k1_tarski(A_173), B_174) | ~r2_hidden(A_173, k3_xboole_0(B_174, C_175)))), inference(resolution, [status(thm)], [c_1374, c_40])).
% 5.61/2.09  tff(c_1431, plain, (![B_174, C_175]: (r1_tarski(k1_tarski('#skF_4'), B_174) | ~r1_tarski('#skF_5', k3_xboole_0(B_174, C_175)))), inference(resolution, [status(thm)], [c_342, c_1404])).
% 5.61/2.09  tff(c_4518, plain, (![B_300]: (r1_tarski(k1_tarski('#skF_4'), '#skF_5') | ~r1_tarski('#skF_5', B_300))), inference(resolution, [status(thm)], [c_4440, c_1431])).
% 5.61/2.09  tff(c_4544, plain, (![B_301]: (~r1_tarski('#skF_5', B_301))), inference(splitLeft, [status(thm)], [c_4518])).
% 5.61/2.09  tff(c_4559, plain, $false, inference(resolution, [status(thm)], [c_34, c_4544])).
% 5.61/2.09  tff(c_4560, plain, (r1_tarski(k1_tarski('#skF_4'), '#skF_5')), inference(splitRight, [status(thm)], [c_4518])).
% 5.61/2.09  tff(c_4576, plain, (k3_xboole_0(k1_tarski('#skF_4'), '#skF_5')=k1_tarski('#skF_4')), inference(resolution, [status(thm)], [c_4560, c_44])).
% 5.61/2.09  tff(c_868, plain, (![A_149, C_150]: (k3_xboole_0(A_149, k3_xboole_0(A_149, C_150))=k3_xboole_0(A_149, C_150))), inference(superposition, [status(thm), theory('equality')], [c_28, c_537])).
% 5.61/2.09  tff(c_894, plain, (![A_149, C_150]: (k5_xboole_0(A_149, k3_xboole_0(A_149, C_150))=k4_xboole_0(A_149, k3_xboole_0(A_149, C_150)))), inference(superposition, [status(thm), theory('equality')], [c_868, c_36])).
% 5.61/2.09  tff(c_933, plain, (![A_149, C_150]: (k4_xboole_0(A_149, k3_xboole_0(A_149, C_150))=k4_xboole_0(A_149, C_150))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_894])).
% 5.61/2.09  tff(c_4639, plain, (k4_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_4'))=k4_xboole_0(k1_tarski('#skF_4'), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_4576, c_933])).
% 5.61/2.09  tff(c_4691, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3251, c_4639])).
% 5.61/2.09  tff(c_50, plain, (![A_34, B_35]: (k5_xboole_0(A_34, k4_xboole_0(B_35, A_34))=k2_xboole_0(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.61/2.09  tff(c_4739, plain, (k2_xboole_0('#skF_5', k1_tarski('#skF_4'))=k5_xboole_0('#skF_5', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4691, c_50])).
% 5.61/2.09  tff(c_4759, plain, (k2_xboole_0('#skF_5', k1_tarski('#skF_4'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_4739])).
% 5.61/2.09  tff(c_4761, plain, $false, inference(negUnitSimplification, [status(thm)], [c_75, c_4759])).
% 5.61/2.09  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.61/2.09  
% 5.61/2.09  Inference rules
% 5.61/2.09  ----------------------
% 5.61/2.09  #Ref     : 0
% 5.61/2.09  #Sup     : 1107
% 5.61/2.09  #Fact    : 0
% 5.61/2.09  #Define  : 0
% 5.61/2.09  #Split   : 2
% 5.61/2.09  #Chain   : 0
% 5.61/2.09  #Close   : 0
% 5.61/2.09  
% 5.61/2.09  Ordering : KBO
% 5.61/2.09  
% 5.61/2.09  Simplification rules
% 5.61/2.09  ----------------------
% 5.61/2.09  #Subsume      : 347
% 5.61/2.09  #Demod        : 765
% 5.61/2.09  #Tautology    : 440
% 5.61/2.09  #SimpNegUnit  : 8
% 5.61/2.09  #BackRed      : 12
% 5.61/2.09  
% 5.61/2.09  #Partial instantiations: 0
% 5.61/2.09  #Strategies tried      : 1
% 5.61/2.09  
% 5.61/2.09  Timing (in seconds)
% 5.61/2.09  ----------------------
% 5.61/2.09  Preprocessing        : 0.37
% 5.61/2.09  Parsing              : 0.18
% 5.61/2.09  CNF conversion       : 0.03
% 5.61/2.09  Main loop            : 0.98
% 5.61/2.09  Inferencing          : 0.31
% 5.61/2.09  Reduction            : 0.37
% 5.61/2.09  Demodulation         : 0.29
% 5.61/2.09  BG Simplification    : 0.04
% 5.61/2.09  Subsumption          : 0.19
% 5.61/2.09  Abstraction          : 0.05
% 5.61/2.09  MUC search           : 0.00
% 5.61/2.09  Cooper               : 0.00
% 5.61/2.09  Total                : 1.39
% 5.61/2.10  Index Insertion      : 0.00
% 5.61/2.10  Index Deletion       : 0.00
% 5.61/2.10  Index Matching       : 0.00
% 5.61/2.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
