%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:03 EST 2020

% Result     : Theorem 10.18s
% Output     : CNFRefutation 10.18s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 341 expanded)
%              Number of leaves         :   38 ( 129 expanded)
%              Depth                    :   13
%              Number of atoms          :  141 ( 356 expanded)
%              Number of equality atoms :  103 ( 304 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(f_86,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
      <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_zfmisc_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_45,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_77,axiom,(
    ! [A] : k3_tarski(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_zfmisc_1)).

tff(f_51,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_70,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_37,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_47,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_43,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => k4_xboole_0(k2_xboole_0(A,B),B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_xboole_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k3_xboole_0(B,k1_tarski(A)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_zfmisc_1)).

tff(c_50,plain,
    ( r2_hidden('#skF_1','#skF_2')
    | ~ r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_132,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_36,plain,(
    ! [A_49,B_50] :
      ( r1_xboole_0(k1_tarski(A_49),B_50)
      | r2_hidden(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_16,plain,(
    ! [A_16] : k5_xboole_0(A_16,A_16) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_44,plain,(
    ! [A_55] : k3_tarski(k1_tarski(A_55)) = A_55 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_22,plain,(
    ! [A_21] : k2_tarski(A_21,A_21) = k1_tarski(A_21) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_241,plain,(
    ! [A_72,B_73] : k3_tarski(k2_tarski(A_72,B_73)) = k2_xboole_0(A_72,B_73) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_256,plain,(
    ! [A_21] : k3_tarski(k1_tarski(A_21)) = k2_xboole_0(A_21,A_21) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_241])).

tff(c_259,plain,(
    ! [A_21] : k2_xboole_0(A_21,A_21) = A_21 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_256])).

tff(c_133,plain,(
    ! [B_64,A_65] : k5_xboole_0(B_64,A_65) = k5_xboole_0(A_65,B_64) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_10] : k5_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_149,plain,(
    ! [A_65] : k5_xboole_0(k1_xboole_0,A_65) = A_65 ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_10])).

tff(c_647,plain,(
    ! [A_106,B_107] : k5_xboole_0(k5_xboole_0(A_106,B_107),k2_xboole_0(A_106,B_107)) = k3_xboole_0(A_106,B_107) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_707,plain,(
    ! [A_16] : k5_xboole_0(k1_xboole_0,k2_xboole_0(A_16,A_16)) = k3_xboole_0(A_16,A_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_647])).

tff(c_714,plain,(
    ! [A_108] : k3_xboole_0(A_108,A_108) = A_108 ),
    inference(demodulation,[status(thm),theory(equality)],[c_259,c_149,c_707])).

tff(c_6,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_724,plain,(
    ! [A_108] : k5_xboole_0(A_108,A_108) = k4_xboole_0(A_108,A_108) ),
    inference(superposition,[status(thm),theory(equality)],[c_714,c_6])).

tff(c_736,plain,(
    ! [A_108] : k4_xboole_0(A_108,A_108) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_724])).

tff(c_40,plain,(
    ! [B_54] : k4_xboole_0(k1_tarski(B_54),k1_tarski(B_54)) != k1_tarski(B_54) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_834,plain,(
    ! [B_54] : k1_tarski(B_54) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_736,c_40])).

tff(c_20,plain,(
    ! [B_20,A_19] : k2_tarski(B_20,A_19) = k2_tarski(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_282,plain,(
    ! [A_79,B_80] : k3_tarski(k2_tarski(A_79,B_80)) = k2_xboole_0(B_80,A_79) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_241])).

tff(c_38,plain,(
    ! [A_51,B_52] : k3_tarski(k2_tarski(A_51,B_52)) = k2_xboole_0(A_51,B_52) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_288,plain,(
    ! [B_80,A_79] : k2_xboole_0(B_80,A_79) = k2_xboole_0(A_79,B_80) ),
    inference(superposition,[status(thm),theory(equality)],[c_282,c_38])).

tff(c_54,plain,
    ( r2_hidden('#skF_1','#skF_2')
    | k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_227,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_18,plain,(
    ! [A_17,B_18] : k5_xboole_0(k5_xboole_0(A_17,B_18),k2_xboole_0(A_17,B_18)) = k3_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_741,plain,(
    ! [A_109,B_110,C_111] : k5_xboole_0(k5_xboole_0(A_109,B_110),C_111) = k5_xboole_0(A_109,k5_xboole_0(B_110,C_111)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1684,plain,(
    ! [A_153,B_154] : k5_xboole_0(A_153,k5_xboole_0(B_154,k2_xboole_0(A_153,B_154))) = k3_xboole_0(A_153,B_154) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_741])).

tff(c_818,plain,(
    ! [A_16,C_111] : k5_xboole_0(A_16,k5_xboole_0(A_16,C_111)) = k5_xboole_0(k1_xboole_0,C_111) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_741])).

tff(c_831,plain,(
    ! [A_16,C_111] : k5_xboole_0(A_16,k5_xboole_0(A_16,C_111)) = C_111 ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_818])).

tff(c_1699,plain,(
    ! [B_154,A_153] : k5_xboole_0(B_154,k2_xboole_0(A_153,B_154)) = k5_xboole_0(A_153,k3_xboole_0(A_153,B_154)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1684,c_831])).

tff(c_2674,plain,(
    ! [B_173,A_174] : k5_xboole_0(B_173,k2_xboole_0(A_174,B_173)) = k4_xboole_0(A_174,B_173) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1699])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_887,plain,(
    ! [A_119,C_120] : k5_xboole_0(A_119,k5_xboole_0(A_119,C_120)) = C_120 ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_818])).

tff(c_936,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k5_xboole_0(B_2,A_1)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_887])).

tff(c_5100,plain,(
    ! [A_202,B_203] : k5_xboole_0(k2_xboole_0(A_202,B_203),k4_xboole_0(A_202,B_203)) = B_203 ),
    inference(superposition,[status(thm),theory(equality)],[c_2674,c_936])).

tff(c_5190,plain,(
    k5_xboole_0(k2_xboole_0(k1_tarski('#skF_3'),'#skF_4'),k1_xboole_0) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_227,c_5100])).

tff(c_5208,plain,(
    k2_xboole_0('#skF_4',k1_tarski('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_288,c_5190])).

tff(c_371,plain,(
    ! [A_86,B_87] :
      ( k4_xboole_0(k2_xboole_0(A_86,B_87),B_87) = A_86
      | ~ r1_xboole_0(A_86,B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_383,plain,(
    ! [A_79,B_80] :
      ( k4_xboole_0(k2_xboole_0(A_79,B_80),A_79) = B_80
      | ~ r1_xboole_0(B_80,A_79) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_288,c_371])).

tff(c_5248,plain,
    ( k4_xboole_0('#skF_4','#skF_4') = k1_tarski('#skF_3')
    | ~ r1_xboole_0(k1_tarski('#skF_3'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_5208,c_383])).

tff(c_5263,plain,
    ( k1_tarski('#skF_3') = k1_xboole_0
    | ~ r1_xboole_0(k1_tarski('#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_736,c_5248])).

tff(c_5264,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_3'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_834,c_5263])).

tff(c_5268,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_5264])).

tff(c_5272,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_132,c_5268])).

tff(c_5273,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_5793,plain,(
    ! [A_247,B_248,C_249] : k5_xboole_0(k5_xboole_0(A_247,B_248),C_249) = k5_xboole_0(A_247,k5_xboole_0(B_248,C_249)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_7171,plain,(
    ! [A_302,B_303] : k5_xboole_0(A_302,k5_xboole_0(B_303,k2_xboole_0(A_302,B_303))) = k3_xboole_0(A_302,B_303) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_5793])).

tff(c_5870,plain,(
    ! [A_16,C_249] : k5_xboole_0(A_16,k5_xboole_0(A_16,C_249)) = k5_xboole_0(k1_xboole_0,C_249) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_5793])).

tff(c_5883,plain,(
    ! [A_16,C_249] : k5_xboole_0(A_16,k5_xboole_0(A_16,C_249)) = C_249 ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_5870])).

tff(c_7189,plain,(
    ! [B_303,A_302] : k5_xboole_0(B_303,k2_xboole_0(A_302,B_303)) = k5_xboole_0(A_302,k3_xboole_0(A_302,B_303)) ),
    inference(superposition,[status(thm),theory(equality)],[c_7171,c_5883])).

tff(c_7365,plain,(
    ! [B_305,A_306] : k5_xboole_0(B_305,k2_xboole_0(A_306,B_305)) = k4_xboole_0(A_306,B_305) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_7189])).

tff(c_7391,plain,(
    ! [B_305,A_306] : k5_xboole_0(B_305,k4_xboole_0(A_306,B_305)) = k2_xboole_0(A_306,B_305) ),
    inference(superposition,[status(thm),theory(equality)],[c_7365,c_5883])).

tff(c_5414,plain,(
    ! [B_223,A_224] :
      ( k3_xboole_0(B_223,k1_tarski(A_224)) = k1_tarski(A_224)
      | ~ r2_hidden(A_224,B_223) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_15121,plain,(
    ! [B_393,A_394] :
      ( k5_xboole_0(B_393,k1_tarski(A_394)) = k4_xboole_0(B_393,k1_tarski(A_394))
      | ~ r2_hidden(A_394,B_393) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5414,c_6])).

tff(c_5884,plain,(
    ! [A_250,C_251] : k5_xboole_0(A_250,k5_xboole_0(A_250,C_251)) = C_251 ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_5870])).

tff(c_5933,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k5_xboole_0(B_2,A_1)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_5884])).

tff(c_15228,plain,(
    ! [A_394,B_393] :
      ( k5_xboole_0(k1_tarski(A_394),k4_xboole_0(B_393,k1_tarski(A_394))) = B_393
      | ~ r2_hidden(A_394,B_393) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15121,c_5933])).

tff(c_15382,plain,(
    ! [B_395,A_396] :
      ( k2_xboole_0(B_395,k1_tarski(A_396)) = B_395
      | ~ r2_hidden(A_396,B_395) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7391,c_15228])).

tff(c_5280,plain,(
    ! [A_207,B_208] : k3_tarski(k2_tarski(A_207,B_208)) = k2_xboole_0(A_207,B_208) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_5322,plain,(
    ! [B_214,A_215] : k3_tarski(k2_tarski(B_214,A_215)) = k2_xboole_0(A_215,B_214) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_5280])).

tff(c_5328,plain,(
    ! [B_214,A_215] : k2_xboole_0(B_214,A_215) = k2_xboole_0(A_215,B_214) ),
    inference(superposition,[status(thm),theory(equality)],[c_5322,c_38])).

tff(c_7431,plain,(
    ! [B_214,A_215] : k5_xboole_0(B_214,k2_xboole_0(B_214,A_215)) = k4_xboole_0(A_215,B_214) ),
    inference(superposition,[status(thm),theory(equality)],[c_5328,c_7365])).

tff(c_15436,plain,(
    ! [B_395,A_396] :
      ( k5_xboole_0(B_395,B_395) = k4_xboole_0(k1_tarski(A_396),B_395)
      | ~ r2_hidden(A_396,B_395) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15382,c_7431])).

tff(c_16044,plain,(
    ! [A_402,B_403] :
      ( k4_xboole_0(k1_tarski(A_402),B_403) = k1_xboole_0
      | ~ r2_hidden(A_402,B_403) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_15436])).

tff(c_5274,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_52,plain,
    ( k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_xboole_0
    | k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_5321,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_5274,c_52])).

tff(c_16107,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_16044,c_5321])).

tff(c_16159,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5273,c_16107])).

tff(c_16160,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_16675,plain,(
    ! [A_442,B_443] : k5_xboole_0(k5_xboole_0(A_442,B_443),k2_xboole_0(A_442,B_443)) = k3_xboole_0(A_442,B_443) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_14,plain,(
    ! [A_13,B_14,C_15] : k5_xboole_0(k5_xboole_0(A_13,B_14),C_15) = k5_xboole_0(A_13,k5_xboole_0(B_14,C_15)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_20384,plain,(
    ! [A_534,B_535] : k5_xboole_0(A_534,k5_xboole_0(B_535,k2_xboole_0(A_534,B_535))) = k3_xboole_0(A_534,B_535) ),
    inference(superposition,[status(thm),theory(equality)],[c_16675,c_14])).

tff(c_16163,plain,(
    ! [B_404,A_405] : k5_xboole_0(B_404,A_405) = k5_xboole_0(A_405,B_404) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_16179,plain,(
    ! [A_405] : k5_xboole_0(k1_xboole_0,A_405) = A_405 ),
    inference(superposition,[status(thm),theory(equality)],[c_16163,c_10])).

tff(c_16452,plain,(
    ! [A_435,B_436,C_437] : k5_xboole_0(k5_xboole_0(A_435,B_436),C_437) = k5_xboole_0(A_435,k5_xboole_0(B_436,C_437)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_16516,plain,(
    ! [A_16,C_437] : k5_xboole_0(A_16,k5_xboole_0(A_16,C_437)) = k5_xboole_0(k1_xboole_0,C_437) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_16452])).

tff(c_16529,plain,(
    ! [A_16,C_437] : k5_xboole_0(A_16,k5_xboole_0(A_16,C_437)) = C_437 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16179,c_16516])).

tff(c_20427,plain,(
    ! [B_535,A_534] : k5_xboole_0(B_535,k2_xboole_0(A_534,B_535)) = k5_xboole_0(A_534,k3_xboole_0(A_534,B_535)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20384,c_16529])).

tff(c_20532,plain,(
    ! [B_536,A_537] : k5_xboole_0(B_536,k2_xboole_0(A_537,B_536)) = k4_xboole_0(A_537,B_536) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_20427])).

tff(c_20584,plain,(
    ! [B_536,A_537] : k5_xboole_0(B_536,k4_xboole_0(A_537,B_536)) = k2_xboole_0(A_537,B_536) ),
    inference(superposition,[status(thm),theory(equality)],[c_20532,c_16529])).

tff(c_16422,plain,(
    ! [B_431,A_432] :
      ( k3_xboole_0(B_431,k1_tarski(A_432)) = k1_tarski(A_432)
      | ~ r2_hidden(A_432,B_431) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_25797,plain,(
    ! [B_595,A_596] :
      ( k5_xboole_0(B_595,k1_tarski(A_596)) = k4_xboole_0(B_595,k1_tarski(A_596))
      | ~ r2_hidden(A_596,B_595) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16422,c_6])).

tff(c_16530,plain,(
    ! [A_438,C_439] : k5_xboole_0(A_438,k5_xboole_0(A_438,C_439)) = C_439 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16179,c_16516])).

tff(c_16573,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k5_xboole_0(B_2,A_1)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_16530])).

tff(c_25891,plain,(
    ! [A_596,B_595] :
      ( k5_xboole_0(k1_tarski(A_596),k4_xboole_0(B_595,k1_tarski(A_596))) = B_595
      | ~ r2_hidden(A_596,B_595) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_25797,c_16573])).

tff(c_26032,plain,(
    ! [B_597,A_598] :
      ( k2_xboole_0(B_597,k1_tarski(A_598)) = B_597
      | ~ r2_hidden(A_598,B_597) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20584,c_25891])).

tff(c_16277,plain,(
    ! [A_414,B_415] : k3_tarski(k2_tarski(A_414,B_415)) = k2_xboole_0(A_414,B_415) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_16309,plain,(
    ! [A_419,B_420] : k3_tarski(k2_tarski(A_419,B_420)) = k2_xboole_0(B_420,A_419) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_16277])).

tff(c_16315,plain,(
    ! [B_420,A_419] : k2_xboole_0(B_420,A_419) = k2_xboole_0(A_419,B_420) ),
    inference(superposition,[status(thm),theory(equality)],[c_16309,c_38])).

tff(c_20628,plain,(
    ! [B_420,A_419] : k5_xboole_0(B_420,k2_xboole_0(B_420,A_419)) = k4_xboole_0(A_419,B_420) ),
    inference(superposition,[status(thm),theory(equality)],[c_16315,c_20532])).

tff(c_26066,plain,(
    ! [B_597,A_598] :
      ( k5_xboole_0(B_597,B_597) = k4_xboole_0(k1_tarski(A_598),B_597)
      | ~ r2_hidden(A_598,B_597) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26032,c_20628])).

tff(c_27104,plain,(
    ! [A_609,B_610] :
      ( k4_xboole_0(k1_tarski(A_609),B_610) = k1_xboole_0
      | ~ r2_hidden(A_609,B_610) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_26066])).

tff(c_16161,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_48,plain,
    ( k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_xboole_0
    | ~ r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_16276,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16161,c_48])).

tff(c_27165,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_27104,c_16276])).

tff(c_27221,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16160,c_27165])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:06:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.18/4.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.18/4.18  
% 10.18/4.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.18/4.18  %$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 10.18/4.18  
% 10.18/4.18  %Foreground sorts:
% 10.18/4.18  
% 10.18/4.18  
% 10.18/4.18  %Background operators:
% 10.18/4.18  
% 10.18/4.18  
% 10.18/4.18  %Foreground operators:
% 10.18/4.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.18/4.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.18/4.18  tff(k1_tarski, type, k1_tarski: $i > $i).
% 10.18/4.18  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.18/4.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.18/4.18  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 10.18/4.18  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 10.18/4.18  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 10.18/4.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.18/4.18  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 10.18/4.18  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 10.18/4.18  tff('#skF_2', type, '#skF_2': $i).
% 10.18/4.18  tff('#skF_3', type, '#skF_3': $i).
% 10.18/4.18  tff('#skF_1', type, '#skF_1': $i).
% 10.18/4.18  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 10.18/4.18  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 10.18/4.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.18/4.18  tff(k3_tarski, type, k3_tarski: $i > $i).
% 10.18/4.18  tff('#skF_4', type, '#skF_4': $i).
% 10.18/4.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.18/4.18  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.18/4.18  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 10.18/4.18  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 10.18/4.18  
% 10.18/4.20  tff(f_86, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_zfmisc_1)).
% 10.18/4.20  tff(f_68, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 10.18/4.20  tff(f_45, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 10.18/4.20  tff(f_77, axiom, (![A]: (k3_tarski(k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 10.18/4.20  tff(f_51, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 10.18/4.20  tff(f_70, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 10.18/4.20  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 10.18/4.20  tff(f_37, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 10.18/4.20  tff(f_47, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 10.18/4.20  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 10.18/4.20  tff(f_75, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 10.18/4.20  tff(f_49, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 10.18/4.20  tff(f_43, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 10.18/4.20  tff(f_41, axiom, (![A, B]: (r1_xboole_0(A, B) => (k4_xboole_0(k2_xboole_0(A, B), B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_xboole_1)).
% 10.18/4.20  tff(f_81, axiom, (![A, B]: (r2_hidden(A, B) => (k3_xboole_0(B, k1_tarski(A)) = k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_zfmisc_1)).
% 10.18/4.20  tff(c_50, plain, (r2_hidden('#skF_1', '#skF_2') | ~r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_86])).
% 10.18/4.20  tff(c_132, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_50])).
% 10.18/4.20  tff(c_36, plain, (![A_49, B_50]: (r1_xboole_0(k1_tarski(A_49), B_50) | r2_hidden(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_68])).
% 10.18/4.20  tff(c_16, plain, (![A_16]: (k5_xboole_0(A_16, A_16)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 10.18/4.20  tff(c_44, plain, (![A_55]: (k3_tarski(k1_tarski(A_55))=A_55)), inference(cnfTransformation, [status(thm)], [f_77])).
% 10.18/4.20  tff(c_22, plain, (![A_21]: (k2_tarski(A_21, A_21)=k1_tarski(A_21))), inference(cnfTransformation, [status(thm)], [f_51])).
% 10.18/4.20  tff(c_241, plain, (![A_72, B_73]: (k3_tarski(k2_tarski(A_72, B_73))=k2_xboole_0(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_70])).
% 10.18/4.20  tff(c_256, plain, (![A_21]: (k3_tarski(k1_tarski(A_21))=k2_xboole_0(A_21, A_21))), inference(superposition, [status(thm), theory('equality')], [c_22, c_241])).
% 10.18/4.20  tff(c_259, plain, (![A_21]: (k2_xboole_0(A_21, A_21)=A_21)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_256])).
% 10.18/4.20  tff(c_133, plain, (![B_64, A_65]: (k5_xboole_0(B_64, A_65)=k5_xboole_0(A_65, B_64))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.18/4.20  tff(c_10, plain, (![A_10]: (k5_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.18/4.20  tff(c_149, plain, (![A_65]: (k5_xboole_0(k1_xboole_0, A_65)=A_65)), inference(superposition, [status(thm), theory('equality')], [c_133, c_10])).
% 10.18/4.20  tff(c_647, plain, (![A_106, B_107]: (k5_xboole_0(k5_xboole_0(A_106, B_107), k2_xboole_0(A_106, B_107))=k3_xboole_0(A_106, B_107))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.18/4.20  tff(c_707, plain, (![A_16]: (k5_xboole_0(k1_xboole_0, k2_xboole_0(A_16, A_16))=k3_xboole_0(A_16, A_16))), inference(superposition, [status(thm), theory('equality')], [c_16, c_647])).
% 10.18/4.20  tff(c_714, plain, (![A_108]: (k3_xboole_0(A_108, A_108)=A_108)), inference(demodulation, [status(thm), theory('equality')], [c_259, c_149, c_707])).
% 10.18/4.20  tff(c_6, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 10.18/4.20  tff(c_724, plain, (![A_108]: (k5_xboole_0(A_108, A_108)=k4_xboole_0(A_108, A_108))), inference(superposition, [status(thm), theory('equality')], [c_714, c_6])).
% 10.18/4.20  tff(c_736, plain, (![A_108]: (k4_xboole_0(A_108, A_108)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_724])).
% 10.18/4.20  tff(c_40, plain, (![B_54]: (k4_xboole_0(k1_tarski(B_54), k1_tarski(B_54))!=k1_tarski(B_54))), inference(cnfTransformation, [status(thm)], [f_75])).
% 10.18/4.20  tff(c_834, plain, (![B_54]: (k1_tarski(B_54)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_736, c_40])).
% 10.18/4.20  tff(c_20, plain, (![B_20, A_19]: (k2_tarski(B_20, A_19)=k2_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_49])).
% 10.18/4.20  tff(c_282, plain, (![A_79, B_80]: (k3_tarski(k2_tarski(A_79, B_80))=k2_xboole_0(B_80, A_79))), inference(superposition, [status(thm), theory('equality')], [c_20, c_241])).
% 10.18/4.20  tff(c_38, plain, (![A_51, B_52]: (k3_tarski(k2_tarski(A_51, B_52))=k2_xboole_0(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_70])).
% 10.18/4.20  tff(c_288, plain, (![B_80, A_79]: (k2_xboole_0(B_80, A_79)=k2_xboole_0(A_79, B_80))), inference(superposition, [status(thm), theory('equality')], [c_282, c_38])).
% 10.18/4.20  tff(c_54, plain, (r2_hidden('#skF_1', '#skF_2') | k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_86])).
% 10.18/4.20  tff(c_227, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_54])).
% 10.18/4.20  tff(c_18, plain, (![A_17, B_18]: (k5_xboole_0(k5_xboole_0(A_17, B_18), k2_xboole_0(A_17, B_18))=k3_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.18/4.20  tff(c_741, plain, (![A_109, B_110, C_111]: (k5_xboole_0(k5_xboole_0(A_109, B_110), C_111)=k5_xboole_0(A_109, k5_xboole_0(B_110, C_111)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.18/4.20  tff(c_1684, plain, (![A_153, B_154]: (k5_xboole_0(A_153, k5_xboole_0(B_154, k2_xboole_0(A_153, B_154)))=k3_xboole_0(A_153, B_154))), inference(superposition, [status(thm), theory('equality')], [c_18, c_741])).
% 10.18/4.20  tff(c_818, plain, (![A_16, C_111]: (k5_xboole_0(A_16, k5_xboole_0(A_16, C_111))=k5_xboole_0(k1_xboole_0, C_111))), inference(superposition, [status(thm), theory('equality')], [c_16, c_741])).
% 10.18/4.20  tff(c_831, plain, (![A_16, C_111]: (k5_xboole_0(A_16, k5_xboole_0(A_16, C_111))=C_111)), inference(demodulation, [status(thm), theory('equality')], [c_149, c_818])).
% 10.18/4.20  tff(c_1699, plain, (![B_154, A_153]: (k5_xboole_0(B_154, k2_xboole_0(A_153, B_154))=k5_xboole_0(A_153, k3_xboole_0(A_153, B_154)))), inference(superposition, [status(thm), theory('equality')], [c_1684, c_831])).
% 10.18/4.20  tff(c_2674, plain, (![B_173, A_174]: (k5_xboole_0(B_173, k2_xboole_0(A_174, B_173))=k4_xboole_0(A_174, B_173))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1699])).
% 10.18/4.20  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.18/4.20  tff(c_887, plain, (![A_119, C_120]: (k5_xboole_0(A_119, k5_xboole_0(A_119, C_120))=C_120)), inference(demodulation, [status(thm), theory('equality')], [c_149, c_818])).
% 10.18/4.20  tff(c_936, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k5_xboole_0(B_2, A_1))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_887])).
% 10.18/4.20  tff(c_5100, plain, (![A_202, B_203]: (k5_xboole_0(k2_xboole_0(A_202, B_203), k4_xboole_0(A_202, B_203))=B_203)), inference(superposition, [status(thm), theory('equality')], [c_2674, c_936])).
% 10.18/4.20  tff(c_5190, plain, (k5_xboole_0(k2_xboole_0(k1_tarski('#skF_3'), '#skF_4'), k1_xboole_0)='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_227, c_5100])).
% 10.18/4.20  tff(c_5208, plain, (k2_xboole_0('#skF_4', k1_tarski('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_10, c_288, c_5190])).
% 10.18/4.20  tff(c_371, plain, (![A_86, B_87]: (k4_xboole_0(k2_xboole_0(A_86, B_87), B_87)=A_86 | ~r1_xboole_0(A_86, B_87))), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.18/4.20  tff(c_383, plain, (![A_79, B_80]: (k4_xboole_0(k2_xboole_0(A_79, B_80), A_79)=B_80 | ~r1_xboole_0(B_80, A_79))), inference(superposition, [status(thm), theory('equality')], [c_288, c_371])).
% 10.18/4.20  tff(c_5248, plain, (k4_xboole_0('#skF_4', '#skF_4')=k1_tarski('#skF_3') | ~r1_xboole_0(k1_tarski('#skF_3'), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_5208, c_383])).
% 10.18/4.20  tff(c_5263, plain, (k1_tarski('#skF_3')=k1_xboole_0 | ~r1_xboole_0(k1_tarski('#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_736, c_5248])).
% 10.18/4.20  tff(c_5264, plain, (~r1_xboole_0(k1_tarski('#skF_3'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_834, c_5263])).
% 10.18/4.20  tff(c_5268, plain, (r2_hidden('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_36, c_5264])).
% 10.18/4.20  tff(c_5272, plain, $false, inference(negUnitSimplification, [status(thm)], [c_132, c_5268])).
% 10.18/4.20  tff(c_5273, plain, (r2_hidden('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_54])).
% 10.18/4.20  tff(c_5793, plain, (![A_247, B_248, C_249]: (k5_xboole_0(k5_xboole_0(A_247, B_248), C_249)=k5_xboole_0(A_247, k5_xboole_0(B_248, C_249)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.18/4.20  tff(c_7171, plain, (![A_302, B_303]: (k5_xboole_0(A_302, k5_xboole_0(B_303, k2_xboole_0(A_302, B_303)))=k3_xboole_0(A_302, B_303))), inference(superposition, [status(thm), theory('equality')], [c_18, c_5793])).
% 10.18/4.20  tff(c_5870, plain, (![A_16, C_249]: (k5_xboole_0(A_16, k5_xboole_0(A_16, C_249))=k5_xboole_0(k1_xboole_0, C_249))), inference(superposition, [status(thm), theory('equality')], [c_16, c_5793])).
% 10.18/4.20  tff(c_5883, plain, (![A_16, C_249]: (k5_xboole_0(A_16, k5_xboole_0(A_16, C_249))=C_249)), inference(demodulation, [status(thm), theory('equality')], [c_149, c_5870])).
% 10.18/4.21  tff(c_7189, plain, (![B_303, A_302]: (k5_xboole_0(B_303, k2_xboole_0(A_302, B_303))=k5_xboole_0(A_302, k3_xboole_0(A_302, B_303)))), inference(superposition, [status(thm), theory('equality')], [c_7171, c_5883])).
% 10.18/4.21  tff(c_7365, plain, (![B_305, A_306]: (k5_xboole_0(B_305, k2_xboole_0(A_306, B_305))=k4_xboole_0(A_306, B_305))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_7189])).
% 10.18/4.21  tff(c_7391, plain, (![B_305, A_306]: (k5_xboole_0(B_305, k4_xboole_0(A_306, B_305))=k2_xboole_0(A_306, B_305))), inference(superposition, [status(thm), theory('equality')], [c_7365, c_5883])).
% 10.18/4.21  tff(c_5414, plain, (![B_223, A_224]: (k3_xboole_0(B_223, k1_tarski(A_224))=k1_tarski(A_224) | ~r2_hidden(A_224, B_223))), inference(cnfTransformation, [status(thm)], [f_81])).
% 10.18/4.21  tff(c_15121, plain, (![B_393, A_394]: (k5_xboole_0(B_393, k1_tarski(A_394))=k4_xboole_0(B_393, k1_tarski(A_394)) | ~r2_hidden(A_394, B_393))), inference(superposition, [status(thm), theory('equality')], [c_5414, c_6])).
% 10.18/4.21  tff(c_5884, plain, (![A_250, C_251]: (k5_xboole_0(A_250, k5_xboole_0(A_250, C_251))=C_251)), inference(demodulation, [status(thm), theory('equality')], [c_149, c_5870])).
% 10.18/4.21  tff(c_5933, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k5_xboole_0(B_2, A_1))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_5884])).
% 10.18/4.21  tff(c_15228, plain, (![A_394, B_393]: (k5_xboole_0(k1_tarski(A_394), k4_xboole_0(B_393, k1_tarski(A_394)))=B_393 | ~r2_hidden(A_394, B_393))), inference(superposition, [status(thm), theory('equality')], [c_15121, c_5933])).
% 10.18/4.21  tff(c_15382, plain, (![B_395, A_396]: (k2_xboole_0(B_395, k1_tarski(A_396))=B_395 | ~r2_hidden(A_396, B_395))), inference(demodulation, [status(thm), theory('equality')], [c_7391, c_15228])).
% 10.18/4.21  tff(c_5280, plain, (![A_207, B_208]: (k3_tarski(k2_tarski(A_207, B_208))=k2_xboole_0(A_207, B_208))), inference(cnfTransformation, [status(thm)], [f_70])).
% 10.18/4.21  tff(c_5322, plain, (![B_214, A_215]: (k3_tarski(k2_tarski(B_214, A_215))=k2_xboole_0(A_215, B_214))), inference(superposition, [status(thm), theory('equality')], [c_20, c_5280])).
% 10.18/4.21  tff(c_5328, plain, (![B_214, A_215]: (k2_xboole_0(B_214, A_215)=k2_xboole_0(A_215, B_214))), inference(superposition, [status(thm), theory('equality')], [c_5322, c_38])).
% 10.18/4.21  tff(c_7431, plain, (![B_214, A_215]: (k5_xboole_0(B_214, k2_xboole_0(B_214, A_215))=k4_xboole_0(A_215, B_214))), inference(superposition, [status(thm), theory('equality')], [c_5328, c_7365])).
% 10.18/4.21  tff(c_15436, plain, (![B_395, A_396]: (k5_xboole_0(B_395, B_395)=k4_xboole_0(k1_tarski(A_396), B_395) | ~r2_hidden(A_396, B_395))), inference(superposition, [status(thm), theory('equality')], [c_15382, c_7431])).
% 10.18/4.21  tff(c_16044, plain, (![A_402, B_403]: (k4_xboole_0(k1_tarski(A_402), B_403)=k1_xboole_0 | ~r2_hidden(A_402, B_403))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_15436])).
% 10.18/4.21  tff(c_5274, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_54])).
% 10.18/4.21  tff(c_52, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_xboole_0 | k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_86])).
% 10.18/4.21  tff(c_5321, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_5274, c_52])).
% 10.18/4.21  tff(c_16107, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_16044, c_5321])).
% 10.18/4.21  tff(c_16159, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5273, c_16107])).
% 10.18/4.21  tff(c_16160, plain, (r2_hidden('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_50])).
% 10.18/4.21  tff(c_16675, plain, (![A_442, B_443]: (k5_xboole_0(k5_xboole_0(A_442, B_443), k2_xboole_0(A_442, B_443))=k3_xboole_0(A_442, B_443))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.18/4.21  tff(c_14, plain, (![A_13, B_14, C_15]: (k5_xboole_0(k5_xboole_0(A_13, B_14), C_15)=k5_xboole_0(A_13, k5_xboole_0(B_14, C_15)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.18/4.21  tff(c_20384, plain, (![A_534, B_535]: (k5_xboole_0(A_534, k5_xboole_0(B_535, k2_xboole_0(A_534, B_535)))=k3_xboole_0(A_534, B_535))), inference(superposition, [status(thm), theory('equality')], [c_16675, c_14])).
% 10.18/4.21  tff(c_16163, plain, (![B_404, A_405]: (k5_xboole_0(B_404, A_405)=k5_xboole_0(A_405, B_404))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.18/4.21  tff(c_16179, plain, (![A_405]: (k5_xboole_0(k1_xboole_0, A_405)=A_405)), inference(superposition, [status(thm), theory('equality')], [c_16163, c_10])).
% 10.18/4.21  tff(c_16452, plain, (![A_435, B_436, C_437]: (k5_xboole_0(k5_xboole_0(A_435, B_436), C_437)=k5_xboole_0(A_435, k5_xboole_0(B_436, C_437)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.18/4.21  tff(c_16516, plain, (![A_16, C_437]: (k5_xboole_0(A_16, k5_xboole_0(A_16, C_437))=k5_xboole_0(k1_xboole_0, C_437))), inference(superposition, [status(thm), theory('equality')], [c_16, c_16452])).
% 10.18/4.21  tff(c_16529, plain, (![A_16, C_437]: (k5_xboole_0(A_16, k5_xboole_0(A_16, C_437))=C_437)), inference(demodulation, [status(thm), theory('equality')], [c_16179, c_16516])).
% 10.18/4.21  tff(c_20427, plain, (![B_535, A_534]: (k5_xboole_0(B_535, k2_xboole_0(A_534, B_535))=k5_xboole_0(A_534, k3_xboole_0(A_534, B_535)))), inference(superposition, [status(thm), theory('equality')], [c_20384, c_16529])).
% 10.18/4.21  tff(c_20532, plain, (![B_536, A_537]: (k5_xboole_0(B_536, k2_xboole_0(A_537, B_536))=k4_xboole_0(A_537, B_536))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_20427])).
% 10.18/4.21  tff(c_20584, plain, (![B_536, A_537]: (k5_xboole_0(B_536, k4_xboole_0(A_537, B_536))=k2_xboole_0(A_537, B_536))), inference(superposition, [status(thm), theory('equality')], [c_20532, c_16529])).
% 10.18/4.21  tff(c_16422, plain, (![B_431, A_432]: (k3_xboole_0(B_431, k1_tarski(A_432))=k1_tarski(A_432) | ~r2_hidden(A_432, B_431))), inference(cnfTransformation, [status(thm)], [f_81])).
% 10.18/4.21  tff(c_25797, plain, (![B_595, A_596]: (k5_xboole_0(B_595, k1_tarski(A_596))=k4_xboole_0(B_595, k1_tarski(A_596)) | ~r2_hidden(A_596, B_595))), inference(superposition, [status(thm), theory('equality')], [c_16422, c_6])).
% 10.18/4.21  tff(c_16530, plain, (![A_438, C_439]: (k5_xboole_0(A_438, k5_xboole_0(A_438, C_439))=C_439)), inference(demodulation, [status(thm), theory('equality')], [c_16179, c_16516])).
% 10.18/4.21  tff(c_16573, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k5_xboole_0(B_2, A_1))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_16530])).
% 10.18/4.21  tff(c_25891, plain, (![A_596, B_595]: (k5_xboole_0(k1_tarski(A_596), k4_xboole_0(B_595, k1_tarski(A_596)))=B_595 | ~r2_hidden(A_596, B_595))), inference(superposition, [status(thm), theory('equality')], [c_25797, c_16573])).
% 10.18/4.21  tff(c_26032, plain, (![B_597, A_598]: (k2_xboole_0(B_597, k1_tarski(A_598))=B_597 | ~r2_hidden(A_598, B_597))), inference(demodulation, [status(thm), theory('equality')], [c_20584, c_25891])).
% 10.18/4.21  tff(c_16277, plain, (![A_414, B_415]: (k3_tarski(k2_tarski(A_414, B_415))=k2_xboole_0(A_414, B_415))), inference(cnfTransformation, [status(thm)], [f_70])).
% 10.18/4.21  tff(c_16309, plain, (![A_419, B_420]: (k3_tarski(k2_tarski(A_419, B_420))=k2_xboole_0(B_420, A_419))), inference(superposition, [status(thm), theory('equality')], [c_20, c_16277])).
% 10.18/4.21  tff(c_16315, plain, (![B_420, A_419]: (k2_xboole_0(B_420, A_419)=k2_xboole_0(A_419, B_420))), inference(superposition, [status(thm), theory('equality')], [c_16309, c_38])).
% 10.18/4.21  tff(c_20628, plain, (![B_420, A_419]: (k5_xboole_0(B_420, k2_xboole_0(B_420, A_419))=k4_xboole_0(A_419, B_420))), inference(superposition, [status(thm), theory('equality')], [c_16315, c_20532])).
% 10.18/4.21  tff(c_26066, plain, (![B_597, A_598]: (k5_xboole_0(B_597, B_597)=k4_xboole_0(k1_tarski(A_598), B_597) | ~r2_hidden(A_598, B_597))), inference(superposition, [status(thm), theory('equality')], [c_26032, c_20628])).
% 10.18/4.21  tff(c_27104, plain, (![A_609, B_610]: (k4_xboole_0(k1_tarski(A_609), B_610)=k1_xboole_0 | ~r2_hidden(A_609, B_610))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_26066])).
% 10.18/4.21  tff(c_16161, plain, (r2_hidden('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_50])).
% 10.18/4.21  tff(c_48, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_xboole_0 | ~r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_86])).
% 10.18/4.21  tff(c_16276, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_16161, c_48])).
% 10.18/4.21  tff(c_27165, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_27104, c_16276])).
% 10.18/4.21  tff(c_27221, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16160, c_27165])).
% 10.18/4.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.18/4.21  
% 10.18/4.21  Inference rules
% 10.18/4.21  ----------------------
% 10.18/4.21  #Ref     : 0
% 10.18/4.21  #Sup     : 6690
% 10.18/4.21  #Fact    : 0
% 10.18/4.21  #Define  : 0
% 10.18/4.21  #Split   : 2
% 10.18/4.21  #Chain   : 0
% 10.18/4.21  #Close   : 0
% 10.18/4.21  
% 10.18/4.21  Ordering : KBO
% 10.18/4.21  
% 10.18/4.21  Simplification rules
% 10.18/4.21  ----------------------
% 10.18/4.21  #Subsume      : 500
% 10.18/4.21  #Demod        : 6601
% 10.18/4.21  #Tautology    : 3400
% 10.18/4.21  #SimpNegUnit  : 32
% 10.18/4.21  #BackRed      : 9
% 10.18/4.21  
% 10.18/4.21  #Partial instantiations: 0
% 10.18/4.21  #Strategies tried      : 1
% 10.18/4.21  
% 10.18/4.21  Timing (in seconds)
% 10.18/4.21  ----------------------
% 10.18/4.21  Preprocessing        : 0.34
% 10.18/4.21  Parsing              : 0.18
% 10.18/4.21  CNF conversion       : 0.02
% 10.18/4.21  Main loop            : 3.03
% 10.18/4.21  Inferencing          : 0.69
% 10.18/4.21  Reduction            : 1.66
% 10.18/4.21  Demodulation         : 1.46
% 10.18/4.21  BG Simplification    : 0.10
% 10.18/4.21  Subsumption          : 0.43
% 10.18/4.21  Abstraction          : 0.14
% 10.18/4.21  MUC search           : 0.00
% 10.18/4.21  Cooper               : 0.00
% 10.18/4.21  Total                : 3.41
% 10.18/4.21  Index Insertion      : 0.00
% 10.18/4.21  Index Deletion       : 0.00
% 10.18/4.21  Index Matching       : 0.00
% 10.18/4.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
