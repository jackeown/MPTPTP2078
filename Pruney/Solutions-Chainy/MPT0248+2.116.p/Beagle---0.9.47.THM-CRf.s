%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:20 EST 2020

% Result     : Theorem 7.95s
% Output     : CNFRefutation 8.47s
% Verified   : 
% Statistics : Number of formulae       :  241 (2079 expanded)
%              Number of leaves         :   46 ( 669 expanded)
%              Depth                    :   18
%              Number of atoms          :  351 (5015 expanded)
%              Number of equality atoms :  215 (3365 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_6 > #skF_4 > #skF_7 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_1 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

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

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

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

tff(f_60,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_88,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_79,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_50,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_81,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_77,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_90,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_110,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_62,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_75,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_67,axiom,(
    ! [A,B] :
      ~ ( r2_xboole_0(A,B)
        & k4_xboole_0(B,A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(c_90,plain,
    ( k1_tarski('#skF_7') != '#skF_9'
    | k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_135,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_90])).

tff(c_36,plain,(
    ! [A_18] :
      ( r2_hidden('#skF_4'(A_18),A_18)
      | k1_xboole_0 = A_18 ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_94,plain,(
    k2_xboole_0('#skF_8','#skF_9') = k1_tarski('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_292,plain,(
    ! [D_108,A_109,B_110] :
      ( ~ r2_hidden(D_108,A_109)
      | r2_hidden(D_108,k2_xboole_0(A_109,B_110)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_329,plain,(
    ! [D_115] :
      ( ~ r2_hidden(D_115,'#skF_8')
      | r2_hidden(D_115,k1_tarski('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_292])).

tff(c_54,plain,(
    ! [C_40,A_36] :
      ( C_40 = A_36
      | ~ r2_hidden(C_40,k1_tarski(A_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_334,plain,(
    ! [D_116] :
      ( D_116 = '#skF_7'
      | ~ r2_hidden(D_116,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_329,c_54])).

tff(c_338,plain,
    ( '#skF_4'('#skF_8') = '#skF_7'
    | k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_36,c_334])).

tff(c_341,plain,(
    '#skF_4'('#skF_8') = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_135,c_338])).

tff(c_345,plain,
    ( r2_hidden('#skF_7','#skF_8')
    | k1_xboole_0 = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_341,c_36])).

tff(c_348,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_135,c_345])).

tff(c_350,plain,(
    ! [D_117,B_118,A_119] :
      ( ~ r2_hidden(D_117,B_118)
      | r2_hidden(D_117,k2_xboole_0(A_119,B_118)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_368,plain,(
    ! [D_120] :
      ( ~ r2_hidden(D_120,'#skF_9')
      | r2_hidden(D_120,k1_tarski('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_350])).

tff(c_373,plain,(
    ! [D_121] :
      ( D_121 = '#skF_7'
      | ~ r2_hidden(D_121,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_368,c_54])).

tff(c_378,plain,
    ( '#skF_4'('#skF_9') = '#skF_7'
    | k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_36,c_373])).

tff(c_379,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_378])).

tff(c_50,plain,(
    ! [A_33] : k5_xboole_0(A_33,A_33) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_384,plain,(
    ! [A_33] : k5_xboole_0(A_33,A_33) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_379,c_50])).

tff(c_34,plain,(
    ! [A_16] : k3_xboole_0(A_16,A_16) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_32,plain,(
    ! [A_14] : k2_xboole_0(A_14,A_14) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1359,plain,(
    ! [A_171,B_172] : k5_xboole_0(k5_xboole_0(A_171,B_172),k2_xboole_0(A_171,B_172)) = k3_xboole_0(A_171,B_172) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1441,plain,(
    ! [A_14] : k5_xboole_0(k5_xboole_0(A_14,A_14),A_14) = k3_xboole_0(A_14,A_14) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_1359])).

tff(c_1447,plain,(
    ! [A_14] : k5_xboole_0('#skF_9',A_14) = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_384,c_34,c_1441])).

tff(c_823,plain,(
    ! [A_158,B_159,C_160] : k5_xboole_0(k5_xboole_0(A_158,B_159),C_160) = k5_xboole_0(A_158,k5_xboole_0(B_159,C_160)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_958,plain,(
    ! [A_165,C_166] : k5_xboole_0(A_165,k5_xboole_0(A_165,C_166)) = k5_xboole_0('#skF_9',C_166) ),
    inference(superposition,[status(thm),theory(equality)],[c_384,c_823])).

tff(c_1018,plain,(
    ! [A_33] : k5_xboole_0(A_33,'#skF_9') = k5_xboole_0('#skF_9',A_33) ),
    inference(superposition,[status(thm),theory(equality)],[c_384,c_958])).

tff(c_1450,plain,(
    ! [A_33] : k5_xboole_0(A_33,'#skF_9') = A_33 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1447,c_1018])).

tff(c_837,plain,(
    ! [A_158,B_159] : k5_xboole_0(A_158,k5_xboole_0(B_159,k5_xboole_0(A_158,B_159))) = '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_823,c_384])).

tff(c_853,plain,(
    ! [A_33,C_160] : k5_xboole_0(A_33,k5_xboole_0(A_33,C_160)) = k5_xboole_0('#skF_9',C_160) ),
    inference(superposition,[status(thm),theory(equality)],[c_384,c_823])).

tff(c_1611,plain,(
    ! [A_176,C_177] : k5_xboole_0(A_176,k5_xboole_0(A_176,C_177)) = C_177 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1447,c_853])).

tff(c_1667,plain,(
    ! [B_159,A_158] : k5_xboole_0(B_159,k5_xboole_0(A_158,B_159)) = k5_xboole_0(A_158,'#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_837,c_1611])).

tff(c_1698,plain,(
    ! [B_159,A_158] : k5_xboole_0(B_159,k5_xboole_0(A_158,B_159)) = A_158 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1450,c_1667])).

tff(c_1704,plain,(
    ! [B_178,A_179] : k5_xboole_0(B_178,k5_xboole_0(A_179,B_178)) = A_179 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1450,c_1667])).

tff(c_1452,plain,(
    ! [A_33,C_160] : k5_xboole_0(A_33,k5_xboole_0(A_33,C_160)) = C_160 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1447,c_853])).

tff(c_1713,plain,(
    ! [B_178,A_179] : k5_xboole_0(B_178,A_179) = k5_xboole_0(A_179,B_178) ),
    inference(superposition,[status(thm),theory(equality)],[c_1704,c_1452])).

tff(c_66,plain,(
    ! [A_41] : k2_tarski(A_41,A_41) = k1_tarski(A_41) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_2349,plain,(
    ! [A_196,B_197,C_198] :
      ( r1_tarski(k2_tarski(A_196,B_197),C_198)
      | ~ r2_hidden(B_197,C_198)
      | ~ r2_hidden(A_196,C_198) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_4891,plain,(
    ! [A_305,C_306] :
      ( r1_tarski(k1_tarski(A_305),C_306)
      | ~ r2_hidden(A_305,C_306)
      | ~ r2_hidden(A_305,C_306) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_2349])).

tff(c_42,plain,(
    ! [A_24,B_25] :
      ( k2_xboole_0(A_24,B_25) = B_25
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_4930,plain,(
    ! [A_307,C_308] :
      ( k2_xboole_0(k1_tarski(A_307),C_308) = C_308
      | ~ r2_hidden(A_307,C_308) ) ),
    inference(resolution,[status(thm)],[c_4891,c_42])).

tff(c_52,plain,(
    ! [A_34,B_35] : k5_xboole_0(k5_xboole_0(A_34,B_35),k2_xboole_0(A_34,B_35)) = k3_xboole_0(A_34,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_4975,plain,(
    ! [A_307,C_308] :
      ( k5_xboole_0(k5_xboole_0(k1_tarski(A_307),C_308),C_308) = k3_xboole_0(k1_tarski(A_307),C_308)
      | ~ r2_hidden(A_307,C_308) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4930,c_52])).

tff(c_5307,plain,(
    ! [A_320,C_321] :
      ( k3_xboole_0(k1_tarski(A_320),C_321) = k1_tarski(A_320)
      | ~ r2_hidden(A_320,C_321) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1698,c_1713,c_4975])).

tff(c_38,plain,(
    ! [A_20,B_21] : k5_xboole_0(A_20,k3_xboole_0(A_20,B_21)) = k4_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_5338,plain,(
    ! [A_320,C_321] :
      ( k5_xboole_0(k1_tarski(A_320),k1_tarski(A_320)) = k4_xboole_0(k1_tarski(A_320),C_321)
      | ~ r2_hidden(A_320,C_321) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5307,c_38])).

tff(c_5366,plain,(
    ! [A_322,C_323] :
      ( k4_xboole_0(k1_tarski(A_322),C_323) = '#skF_9'
      | ~ r2_hidden(A_322,C_323) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_384,c_5338])).

tff(c_88,plain,
    ( k1_xboole_0 != '#skF_9'
    | k1_tarski('#skF_7') != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_136,plain,(
    k1_tarski('#skF_7') != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_88])).

tff(c_137,plain,(
    ! [A_80,B_81] : r1_tarski(A_80,k2_xboole_0(A_80,B_81)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_140,plain,(
    r1_tarski('#skF_8',k1_tarski('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_137])).

tff(c_532,plain,(
    ! [A_142,B_143] :
      ( r2_xboole_0(A_142,B_143)
      | B_143 = A_142
      | ~ r1_tarski(A_142,B_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_40,plain,(
    ! [B_23,A_22] :
      ( k4_xboole_0(B_23,A_22) != k1_xboole_0
      | ~ r2_xboole_0(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_381,plain,(
    ! [B_23,A_22] :
      ( k4_xboole_0(B_23,A_22) != '#skF_9'
      | ~ r2_xboole_0(A_22,B_23) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_379,c_40])).

tff(c_4440,plain,(
    ! [B_286,A_287] :
      ( k4_xboole_0(B_286,A_287) != '#skF_9'
      | B_286 = A_287
      | ~ r1_tarski(A_287,B_286) ) ),
    inference(resolution,[status(thm)],[c_532,c_381])).

tff(c_4458,plain,
    ( k4_xboole_0(k1_tarski('#skF_7'),'#skF_8') != '#skF_9'
    | k1_tarski('#skF_7') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_140,c_4440])).

tff(c_4475,plain,(
    k4_xboole_0(k1_tarski('#skF_7'),'#skF_8') != '#skF_9' ),
    inference(negUnitSimplification,[status(thm)],[c_136,c_4458])).

tff(c_5372,plain,(
    ~ r2_hidden('#skF_7','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_5366,c_4475])).

tff(c_5408,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_348,c_5372])).

tff(c_5410,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(splitRight,[status(thm)],[c_378])).

tff(c_5409,plain,(
    '#skF_4'('#skF_9') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_378])).

tff(c_5427,plain,
    ( r2_hidden('#skF_7','#skF_9')
    | k1_xboole_0 = '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_5409,c_36])).

tff(c_5430,plain,(
    r2_hidden('#skF_7','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_5410,c_5427])).

tff(c_5516,plain,(
    ! [A_339,B_340] :
      ( r2_hidden('#skF_1'(A_339,B_340),A_339)
      | r1_tarski(A_339,B_340) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_333,plain,(
    ! [D_115] :
      ( D_115 = '#skF_7'
      | ~ r2_hidden(D_115,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_329,c_54])).

tff(c_5543,plain,(
    ! [B_342] :
      ( '#skF_1'('#skF_8',B_342) = '#skF_7'
      | r1_tarski('#skF_8',B_342) ) ),
    inference(resolution,[status(thm)],[c_5516,c_333])).

tff(c_5629,plain,(
    ! [B_345] :
      ( k2_xboole_0('#skF_8',B_345) = B_345
      | '#skF_1'('#skF_8',B_345) = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_5543,c_42])).

tff(c_5654,plain,
    ( k1_tarski('#skF_7') = '#skF_9'
    | '#skF_1'('#skF_8','#skF_9') = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_5629,c_94])).

tff(c_5685,plain,(
    '#skF_1'('#skF_8','#skF_9') = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_5654])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_5735,plain,
    ( ~ r2_hidden('#skF_7','#skF_9')
    | r1_tarski('#skF_8','#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_5685,c_4])).

tff(c_5740,plain,(
    r1_tarski('#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5430,c_5735])).

tff(c_5745,plain,(
    k2_xboole_0('#skF_8','#skF_9') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_5740,c_42])).

tff(c_5746,plain,(
    k1_tarski('#skF_7') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5745,c_94])).

tff(c_5782,plain,(
    '#skF_9' != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5746,c_136])).

tff(c_8168,plain,(
    ! [A_426,B_427] :
      ( '#skF_5'(A_426,B_427) = A_426
      | r2_hidden('#skF_6'(A_426,B_427),B_427)
      | k1_tarski(A_426) = B_427 ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_8325,plain,(
    ! [A_430] :
      ( '#skF_6'(A_430,'#skF_8') = '#skF_7'
      | '#skF_5'(A_430,'#skF_8') = A_430
      | k1_tarski(A_430) = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_8168,c_333])).

tff(c_8343,plain,
    ( '#skF_9' = '#skF_8'
    | '#skF_6'('#skF_7','#skF_8') = '#skF_7'
    | '#skF_5'('#skF_7','#skF_8') = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_8325,c_5746])).

tff(c_8371,plain,
    ( '#skF_6'('#skF_7','#skF_8') = '#skF_7'
    | '#skF_5'('#skF_7','#skF_8') = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_5782,c_8343])).

tff(c_8476,plain,(
    '#skF_5'('#skF_7','#skF_8') = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_8371])).

tff(c_58,plain,(
    ! [A_36,B_37] :
      ( ~ r2_hidden('#skF_5'(A_36,B_37),B_37)
      | '#skF_6'(A_36,B_37) != A_36
      | k1_tarski(A_36) = B_37 ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_8480,plain,
    ( ~ r2_hidden('#skF_7','#skF_8')
    | '#skF_6'('#skF_7','#skF_8') != '#skF_7'
    | k1_tarski('#skF_7') = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_8476,c_58])).

tff(c_8484,plain,
    ( '#skF_6'('#skF_7','#skF_8') != '#skF_7'
    | '#skF_9' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5746,c_348,c_8480])).

tff(c_8485,plain,(
    '#skF_6'('#skF_7','#skF_8') != '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_5782,c_8484])).

tff(c_8674,plain,(
    ! [A_441,B_442] :
      ( ~ r2_hidden('#skF_5'(A_441,B_442),B_442)
      | r2_hidden('#skF_6'(A_441,B_442),B_442)
      | k1_tarski(A_441) = B_442 ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_8899,plain,(
    ! [A_451] :
      ( '#skF_6'(A_451,'#skF_8') = '#skF_7'
      | ~ r2_hidden('#skF_5'(A_451,'#skF_8'),'#skF_8')
      | k1_tarski(A_451) = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_8674,c_333])).

tff(c_8902,plain,
    ( '#skF_6'('#skF_7','#skF_8') = '#skF_7'
    | ~ r2_hidden('#skF_7','#skF_8')
    | k1_tarski('#skF_7') = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_8476,c_8899])).

tff(c_8904,plain,
    ( '#skF_6'('#skF_7','#skF_8') = '#skF_7'
    | '#skF_9' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5746,c_348,c_8902])).

tff(c_8906,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5782,c_8485,c_8904])).

tff(c_8908,plain,(
    '#skF_5'('#skF_7','#skF_8') != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_8371])).

tff(c_8907,plain,(
    '#skF_6'('#skF_7','#skF_8') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_8371])).

tff(c_60,plain,(
    ! [A_36,B_37] :
      ( '#skF_5'(A_36,B_37) = A_36
      | '#skF_6'(A_36,B_37) != A_36
      | k1_tarski(A_36) = B_37 ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_8914,plain,
    ( '#skF_5'('#skF_7','#skF_8') = '#skF_7'
    | k1_tarski('#skF_7') = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_8907,c_60])).

tff(c_8920,plain,
    ( '#skF_5'('#skF_7','#skF_8') = '#skF_7'
    | '#skF_9' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5746,c_8914])).

tff(c_8921,plain,(
    '#skF_5'('#skF_7','#skF_8') = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_5782,c_8920])).

tff(c_8923,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8908,c_8921])).

tff(c_8924,plain,(
    k1_tarski('#skF_7') = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_5654])).

tff(c_8933,plain,(
    '#skF_9' != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8924,c_136])).

tff(c_11509,plain,(
    ! [A_535,B_536] :
      ( '#skF_5'(A_535,B_536) = A_535
      | r2_hidden('#skF_6'(A_535,B_536),B_536)
      | k1_tarski(A_535) = B_536 ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_11611,plain,(
    ! [A_538] :
      ( '#skF_6'(A_538,'#skF_8') = '#skF_7'
      | '#skF_5'(A_538,'#skF_8') = A_538
      | k1_tarski(A_538) = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_11509,c_333])).

tff(c_11653,plain,
    ( '#skF_6'('#skF_7','#skF_8') = '#skF_7'
    | '#skF_5'('#skF_7','#skF_8') = '#skF_7'
    | '#skF_9' = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_8924,c_11611])).

tff(c_11660,plain,
    ( '#skF_6'('#skF_7','#skF_8') = '#skF_7'
    | '#skF_5'('#skF_7','#skF_8') = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_8933,c_11653])).

tff(c_11904,plain,(
    '#skF_5'('#skF_7','#skF_8') = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_11660])).

tff(c_11908,plain,
    ( ~ r2_hidden('#skF_7','#skF_8')
    | '#skF_6'('#skF_7','#skF_8') != '#skF_7'
    | k1_tarski('#skF_7') = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_11904,c_58])).

tff(c_11912,plain,
    ( '#skF_6'('#skF_7','#skF_8') != '#skF_7'
    | '#skF_9' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8924,c_348,c_11908])).

tff(c_11913,plain,(
    '#skF_6'('#skF_7','#skF_8') != '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_8933,c_11912])).

tff(c_12050,plain,(
    ! [A_551,B_552] :
      ( ~ r2_hidden('#skF_5'(A_551,B_552),B_552)
      | r2_hidden('#skF_6'(A_551,B_552),B_552)
      | k1_tarski(A_551) = B_552 ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_12272,plain,(
    ! [A_570] :
      ( '#skF_6'(A_570,'#skF_8') = '#skF_7'
      | ~ r2_hidden('#skF_5'(A_570,'#skF_8'),'#skF_8')
      | k1_tarski(A_570) = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_12050,c_333])).

tff(c_12275,plain,
    ( '#skF_6'('#skF_7','#skF_8') = '#skF_7'
    | ~ r2_hidden('#skF_7','#skF_8')
    | k1_tarski('#skF_7') = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_11904,c_12272])).

tff(c_12277,plain,
    ( '#skF_6'('#skF_7','#skF_8') = '#skF_7'
    | '#skF_9' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8924,c_348,c_12275])).

tff(c_12279,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8933,c_11913,c_12277])).

tff(c_12281,plain,(
    '#skF_5'('#skF_7','#skF_8') != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_11660])).

tff(c_12280,plain,(
    '#skF_6'('#skF_7','#skF_8') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_11660])).

tff(c_12287,plain,
    ( '#skF_5'('#skF_7','#skF_8') = '#skF_7'
    | k1_tarski('#skF_7') = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_12280,c_60])).

tff(c_12293,plain,
    ( '#skF_5'('#skF_7','#skF_8') = '#skF_7'
    | '#skF_9' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8924,c_12287])).

tff(c_12294,plain,(
    '#skF_5'('#skF_7','#skF_8') = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_8933,c_12293])).

tff(c_12296,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12281,c_12294])).

tff(c_12298,plain,(
    k1_tarski('#skF_7') = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_92,plain,
    ( k1_tarski('#skF_7') != '#skF_9'
    | k1_tarski('#skF_7') != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_12320,plain,(
    '#skF_9' != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12298,c_12298,c_92])).

tff(c_12299,plain,(
    k2_xboole_0('#skF_8','#skF_9') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12298,c_94])).

tff(c_12297,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_12548,plain,(
    ! [D_614,B_615,A_616] :
      ( ~ r2_hidden(D_614,B_615)
      | r2_hidden(D_614,k2_xboole_0(A_616,B_615)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_12560,plain,(
    ! [D_617] :
      ( ~ r2_hidden(D_617,'#skF_9')
      | r2_hidden(D_617,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12299,c_12548])).

tff(c_12568,plain,
    ( r2_hidden('#skF_4'('#skF_9'),'#skF_8')
    | k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_36,c_12560])).

tff(c_12573,plain,(
    r2_hidden('#skF_4'('#skF_9'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_12297,c_12568])).

tff(c_12322,plain,(
    ! [C_574,A_575] :
      ( C_574 = A_575
      | ~ r2_hidden(C_574,k1_tarski(A_575)) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_12325,plain,(
    ! [C_574] :
      ( C_574 = '#skF_7'
      | ~ r2_hidden(C_574,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12298,c_12322])).

tff(c_12577,plain,(
    '#skF_4'('#skF_9') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_12573,c_12325])).

tff(c_12583,plain,
    ( r2_hidden('#skF_7','#skF_9')
    | k1_xboole_0 = '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_12577,c_36])).

tff(c_12586,plain,(
    r2_hidden('#skF_7','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_12297,c_12583])).

tff(c_12690,plain,(
    ! [A_629,B_630] :
      ( r2_hidden('#skF_1'(A_629,B_630),A_629)
      | r1_tarski(A_629,B_630) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12712,plain,(
    ! [B_631] :
      ( '#skF_1'('#skF_8',B_631) = '#skF_7'
      | r1_tarski('#skF_8',B_631) ) ),
    inference(resolution,[status(thm)],[c_12690,c_12325])).

tff(c_12781,plain,(
    ! [B_635] :
      ( k2_xboole_0('#skF_8',B_635) = B_635
      | '#skF_1'('#skF_8',B_635) = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_12712,c_42])).

tff(c_12805,plain,
    ( '#skF_9' = '#skF_8'
    | '#skF_1'('#skF_8','#skF_9') = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_12781,c_12299])).

tff(c_12827,plain,(
    '#skF_1'('#skF_8','#skF_9') = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_12320,c_12805])).

tff(c_12839,plain,
    ( ~ r2_hidden('#skF_7','#skF_9')
    | r1_tarski('#skF_8','#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_12827,c_4])).

tff(c_12844,plain,(
    r1_tarski('#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12586,c_12839])).

tff(c_12857,plain,(
    k2_xboole_0('#skF_8','#skF_9') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_12844,c_42])).

tff(c_12859,plain,(
    '#skF_9' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12299,c_12857])).

tff(c_12861,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12320,c_12859])).

tff(c_12862,plain,(
    k1_tarski('#skF_7') != '#skF_9' ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_12863,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_12869,plain,
    ( '#skF_9' != '#skF_8'
    | k1_tarski('#skF_7') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12863,c_88])).

tff(c_12870,plain,(
    k1_tarski('#skF_7') != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_12869])).

tff(c_12886,plain,(
    ! [A_18] :
      ( r2_hidden('#skF_4'(A_18),A_18)
      | A_18 = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12863,c_36])).

tff(c_13097,plain,(
    ! [D_675,B_676,A_677] :
      ( ~ r2_hidden(D_675,B_676)
      | r2_hidden(D_675,k2_xboole_0(A_677,B_676)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_13115,plain,(
    ! [D_678] :
      ( ~ r2_hidden(D_678,'#skF_9')
      | r2_hidden(D_678,k1_tarski('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_13097])).

tff(c_13125,plain,(
    ! [D_679] :
      ( D_679 = '#skF_7'
      | ~ r2_hidden(D_679,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_13115,c_54])).

tff(c_13135,plain,
    ( '#skF_4'('#skF_9') = '#skF_7'
    | '#skF_9' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_12886,c_13125])).

tff(c_13136,plain,(
    '#skF_9' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_13135])).

tff(c_13140,plain,(
    k2_xboole_0('#skF_8','#skF_8') = k1_tarski('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13136,c_94])).

tff(c_13141,plain,(
    k1_tarski('#skF_7') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_13140])).

tff(c_13143,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12870,c_13141])).

tff(c_13145,plain,(
    '#skF_9' != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_13135])).

tff(c_13144,plain,(
    '#skF_4'('#skF_9') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_13135])).

tff(c_13149,plain,
    ( r2_hidden('#skF_7','#skF_9')
    | '#skF_9' = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_13144,c_12886])).

tff(c_13152,plain,(
    r2_hidden('#skF_7','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_13145,c_13149])).

tff(c_13075,plain,(
    ! [A_672,B_673] :
      ( r2_hidden('#skF_1'(A_672,B_673),A_672)
      | r1_tarski(A_672,B_673) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_13022,plain,(
    ! [D_663,A_664,B_665] :
      ( ~ r2_hidden(D_663,A_664)
      | r2_hidden(D_663,k2_xboole_0(A_664,B_665)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_13035,plain,(
    ! [D_666] :
      ( ~ r2_hidden(D_666,'#skF_8')
      | r2_hidden(D_666,k1_tarski('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_13022])).

tff(c_13039,plain,(
    ! [D_666] :
      ( D_666 = '#skF_7'
      | ~ r2_hidden(D_666,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_13035,c_54])).

tff(c_13092,plain,(
    ! [B_674] :
      ( '#skF_1'('#skF_8',B_674) = '#skF_7'
      | r1_tarski('#skF_8',B_674) ) ),
    inference(resolution,[status(thm)],[c_13075,c_13039])).

tff(c_13273,plain,(
    ! [B_705] :
      ( k2_xboole_0('#skF_8',B_705) = B_705
      | '#skF_1'('#skF_8',B_705) = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_13092,c_42])).

tff(c_13298,plain,
    ( k1_tarski('#skF_7') = '#skF_9'
    | '#skF_1'('#skF_8','#skF_9') = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_13273,c_94])).

tff(c_13324,plain,(
    '#skF_1'('#skF_8','#skF_9') = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_12862,c_13298])).

tff(c_13337,plain,
    ( ~ r2_hidden('#skF_7','#skF_9')
    | r1_tarski('#skF_8','#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_13324,c_4])).

tff(c_13341,plain,(
    r1_tarski('#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13152,c_13337])).

tff(c_13347,plain,(
    k2_xboole_0('#skF_8','#skF_9') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_13341,c_42])).

tff(c_13348,plain,(
    k1_tarski('#skF_7') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13347,c_94])).

tff(c_13350,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12862,c_13348])).

tff(c_13351,plain,(
    '#skF_9' != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_12869])).

tff(c_13352,plain,(
    k1_tarski('#skF_7') = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_12869])).

tff(c_13354,plain,(
    k2_xboole_0('#skF_8','#skF_9') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13352,c_94])).

tff(c_13643,plain,(
    ! [A_753,B_754] :
      ( r2_hidden('#skF_1'(A_753,B_754),A_753)
      | r1_tarski(A_753,B_754) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_13384,plain,(
    ! [C_710,A_711] :
      ( C_710 = A_711
      | ~ r2_hidden(C_710,k1_tarski(A_711)) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_13387,plain,(
    ! [C_710] :
      ( C_710 = '#skF_7'
      | ~ r2_hidden(C_710,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13352,c_13384])).

tff(c_13675,plain,(
    ! [B_758] :
      ( '#skF_1'('#skF_8',B_758) = '#skF_7'
      | r1_tarski('#skF_8',B_758) ) ),
    inference(resolution,[status(thm)],[c_13643,c_13387])).

tff(c_13706,plain,(
    ! [B_760] :
      ( k2_xboole_0('#skF_8',B_760) = B_760
      | '#skF_1'('#skF_8',B_760) = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_13675,c_42])).

tff(c_13727,plain,
    ( '#skF_9' = '#skF_8'
    | '#skF_1'('#skF_8','#skF_9') = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_13706,c_13354])).

tff(c_13749,plain,(
    '#skF_1'('#skF_8','#skF_9') = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_13351,c_13727])).

tff(c_13761,plain,
    ( ~ r2_hidden('#skF_7','#skF_9')
    | r1_tarski('#skF_8','#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_13749,c_4])).

tff(c_13767,plain,(
    ~ r2_hidden('#skF_7','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_13761])).

tff(c_13399,plain,(
    ! [A_18] :
      ( r2_hidden('#skF_4'(A_18),A_18)
      | A_18 = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12863,c_36])).

tff(c_13814,plain,(
    ! [D_765,B_766,A_767] :
      ( ~ r2_hidden(D_765,B_766)
      | r2_hidden(D_765,k2_xboole_0(A_767,B_766)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_13832,plain,(
    ! [D_768] :
      ( ~ r2_hidden(D_768,'#skF_9')
      | r2_hidden(D_768,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13354,c_13814])).

tff(c_13848,plain,
    ( r2_hidden('#skF_4'('#skF_9'),'#skF_8')
    | '#skF_9' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_13399,c_13832])).

tff(c_13856,plain,(
    r2_hidden('#skF_4'('#skF_9'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_13351,c_13848])).

tff(c_13860,plain,(
    '#skF_4'('#skF_9') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_13856,c_13387])).

tff(c_13866,plain,
    ( r2_hidden('#skF_7','#skF_9')
    | '#skF_9' = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_13860,c_13399])).

tff(c_13870,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13351,c_13767,c_13866])).

tff(c_13871,plain,(
    r1_tarski('#skF_8','#skF_9') ),
    inference(splitRight,[status(thm)],[c_13761])).

tff(c_13875,plain,(
    k2_xboole_0('#skF_8','#skF_9') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_13871,c_42])).

tff(c_13877,plain,(
    '#skF_9' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13354,c_13875])).

tff(c_13879,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13351,c_13877])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:42:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.95/2.82  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.29/2.85  
% 8.29/2.85  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.29/2.85  %$ r2_xboole_0 > r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_6 > #skF_4 > #skF_7 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_1 > #skF_5
% 8.29/2.85  
% 8.29/2.85  %Foreground sorts:
% 8.29/2.85  
% 8.29/2.85  
% 8.29/2.85  %Background operators:
% 8.29/2.85  
% 8.29/2.85  
% 8.29/2.85  %Foreground operators:
% 8.29/2.85  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 8.29/2.85  tff('#skF_4', type, '#skF_4': $i > $i).
% 8.29/2.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.29/2.85  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.29/2.85  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.29/2.85  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.29/2.85  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.29/2.85  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 8.29/2.85  tff('#skF_7', type, '#skF_7': $i).
% 8.29/2.85  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.29/2.85  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.29/2.85  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.29/2.85  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.29/2.85  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.29/2.85  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 8.29/2.85  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.29/2.85  tff('#skF_9', type, '#skF_9': $i).
% 8.29/2.85  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 8.29/2.85  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 8.29/2.85  tff('#skF_8', type, '#skF_8': $i).
% 8.29/2.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.29/2.85  tff(k3_tarski, type, k3_tarski: $i > $i).
% 8.29/2.85  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 8.29/2.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.29/2.85  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.29/2.85  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.29/2.85  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 8.29/2.85  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.29/2.85  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 8.29/2.85  
% 8.29/2.88  tff(f_129, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 8.29/2.88  tff(f_60, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 8.29/2.88  tff(f_41, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 8.29/2.88  tff(f_88, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 8.29/2.88  tff(f_79, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 8.29/2.88  tff(f_52, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 8.29/2.88  tff(f_50, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 8.29/2.88  tff(f_81, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 8.29/2.88  tff(f_77, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 8.29/2.88  tff(f_90, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 8.29/2.88  tff(f_110, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 8.29/2.88  tff(f_71, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 8.29/2.88  tff(f_62, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 8.29/2.88  tff(f_75, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 8.29/2.88  tff(f_48, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 8.29/2.88  tff(f_67, axiom, (![A, B]: ~(r2_xboole_0(A, B) & (k4_xboole_0(B, A) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t105_xboole_1)).
% 8.29/2.88  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 8.29/2.88  tff(c_90, plain, (k1_tarski('#skF_7')!='#skF_9' | k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_129])).
% 8.29/2.88  tff(c_135, plain, (k1_xboole_0!='#skF_8'), inference(splitLeft, [status(thm)], [c_90])).
% 8.29/2.88  tff(c_36, plain, (![A_18]: (r2_hidden('#skF_4'(A_18), A_18) | k1_xboole_0=A_18)), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.29/2.88  tff(c_94, plain, (k2_xboole_0('#skF_8', '#skF_9')=k1_tarski('#skF_7')), inference(cnfTransformation, [status(thm)], [f_129])).
% 8.29/2.88  tff(c_292, plain, (![D_108, A_109, B_110]: (~r2_hidden(D_108, A_109) | r2_hidden(D_108, k2_xboole_0(A_109, B_110)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.29/2.88  tff(c_329, plain, (![D_115]: (~r2_hidden(D_115, '#skF_8') | r2_hidden(D_115, k1_tarski('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_94, c_292])).
% 8.29/2.88  tff(c_54, plain, (![C_40, A_36]: (C_40=A_36 | ~r2_hidden(C_40, k1_tarski(A_36)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 8.29/2.88  tff(c_334, plain, (![D_116]: (D_116='#skF_7' | ~r2_hidden(D_116, '#skF_8'))), inference(resolution, [status(thm)], [c_329, c_54])).
% 8.29/2.88  tff(c_338, plain, ('#skF_4'('#skF_8')='#skF_7' | k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_36, c_334])).
% 8.29/2.88  tff(c_341, plain, ('#skF_4'('#skF_8')='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_135, c_338])).
% 8.29/2.88  tff(c_345, plain, (r2_hidden('#skF_7', '#skF_8') | k1_xboole_0='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_341, c_36])).
% 8.29/2.88  tff(c_348, plain, (r2_hidden('#skF_7', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_135, c_345])).
% 8.29/2.88  tff(c_350, plain, (![D_117, B_118, A_119]: (~r2_hidden(D_117, B_118) | r2_hidden(D_117, k2_xboole_0(A_119, B_118)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.29/2.88  tff(c_368, plain, (![D_120]: (~r2_hidden(D_120, '#skF_9') | r2_hidden(D_120, k1_tarski('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_94, c_350])).
% 8.29/2.88  tff(c_373, plain, (![D_121]: (D_121='#skF_7' | ~r2_hidden(D_121, '#skF_9'))), inference(resolution, [status(thm)], [c_368, c_54])).
% 8.29/2.88  tff(c_378, plain, ('#skF_4'('#skF_9')='#skF_7' | k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_36, c_373])).
% 8.29/2.88  tff(c_379, plain, (k1_xboole_0='#skF_9'), inference(splitLeft, [status(thm)], [c_378])).
% 8.29/2.88  tff(c_50, plain, (![A_33]: (k5_xboole_0(A_33, A_33)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_79])).
% 8.29/2.88  tff(c_384, plain, (![A_33]: (k5_xboole_0(A_33, A_33)='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_379, c_50])).
% 8.29/2.88  tff(c_34, plain, (![A_16]: (k3_xboole_0(A_16, A_16)=A_16)), inference(cnfTransformation, [status(thm)], [f_52])).
% 8.29/2.88  tff(c_32, plain, (![A_14]: (k2_xboole_0(A_14, A_14)=A_14)), inference(cnfTransformation, [status(thm)], [f_50])).
% 8.29/2.88  tff(c_1359, plain, (![A_171, B_172]: (k5_xboole_0(k5_xboole_0(A_171, B_172), k2_xboole_0(A_171, B_172))=k3_xboole_0(A_171, B_172))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.29/2.88  tff(c_1441, plain, (![A_14]: (k5_xboole_0(k5_xboole_0(A_14, A_14), A_14)=k3_xboole_0(A_14, A_14))), inference(superposition, [status(thm), theory('equality')], [c_32, c_1359])).
% 8.29/2.88  tff(c_1447, plain, (![A_14]: (k5_xboole_0('#skF_9', A_14)=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_384, c_34, c_1441])).
% 8.29/2.88  tff(c_823, plain, (![A_158, B_159, C_160]: (k5_xboole_0(k5_xboole_0(A_158, B_159), C_160)=k5_xboole_0(A_158, k5_xboole_0(B_159, C_160)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 8.29/2.88  tff(c_958, plain, (![A_165, C_166]: (k5_xboole_0(A_165, k5_xboole_0(A_165, C_166))=k5_xboole_0('#skF_9', C_166))), inference(superposition, [status(thm), theory('equality')], [c_384, c_823])).
% 8.29/2.88  tff(c_1018, plain, (![A_33]: (k5_xboole_0(A_33, '#skF_9')=k5_xboole_0('#skF_9', A_33))), inference(superposition, [status(thm), theory('equality')], [c_384, c_958])).
% 8.29/2.88  tff(c_1450, plain, (![A_33]: (k5_xboole_0(A_33, '#skF_9')=A_33)), inference(demodulation, [status(thm), theory('equality')], [c_1447, c_1018])).
% 8.29/2.88  tff(c_837, plain, (![A_158, B_159]: (k5_xboole_0(A_158, k5_xboole_0(B_159, k5_xboole_0(A_158, B_159)))='#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_823, c_384])).
% 8.29/2.88  tff(c_853, plain, (![A_33, C_160]: (k5_xboole_0(A_33, k5_xboole_0(A_33, C_160))=k5_xboole_0('#skF_9', C_160))), inference(superposition, [status(thm), theory('equality')], [c_384, c_823])).
% 8.29/2.88  tff(c_1611, plain, (![A_176, C_177]: (k5_xboole_0(A_176, k5_xboole_0(A_176, C_177))=C_177)), inference(demodulation, [status(thm), theory('equality')], [c_1447, c_853])).
% 8.29/2.88  tff(c_1667, plain, (![B_159, A_158]: (k5_xboole_0(B_159, k5_xboole_0(A_158, B_159))=k5_xboole_0(A_158, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_837, c_1611])).
% 8.29/2.88  tff(c_1698, plain, (![B_159, A_158]: (k5_xboole_0(B_159, k5_xboole_0(A_158, B_159))=A_158)), inference(demodulation, [status(thm), theory('equality')], [c_1450, c_1667])).
% 8.29/2.88  tff(c_1704, plain, (![B_178, A_179]: (k5_xboole_0(B_178, k5_xboole_0(A_179, B_178))=A_179)), inference(demodulation, [status(thm), theory('equality')], [c_1450, c_1667])).
% 8.29/2.88  tff(c_1452, plain, (![A_33, C_160]: (k5_xboole_0(A_33, k5_xboole_0(A_33, C_160))=C_160)), inference(demodulation, [status(thm), theory('equality')], [c_1447, c_853])).
% 8.29/2.88  tff(c_1713, plain, (![B_178, A_179]: (k5_xboole_0(B_178, A_179)=k5_xboole_0(A_179, B_178))), inference(superposition, [status(thm), theory('equality')], [c_1704, c_1452])).
% 8.29/2.88  tff(c_66, plain, (![A_41]: (k2_tarski(A_41, A_41)=k1_tarski(A_41))), inference(cnfTransformation, [status(thm)], [f_90])).
% 8.29/2.88  tff(c_2349, plain, (![A_196, B_197, C_198]: (r1_tarski(k2_tarski(A_196, B_197), C_198) | ~r2_hidden(B_197, C_198) | ~r2_hidden(A_196, C_198))), inference(cnfTransformation, [status(thm)], [f_110])).
% 8.29/2.88  tff(c_4891, plain, (![A_305, C_306]: (r1_tarski(k1_tarski(A_305), C_306) | ~r2_hidden(A_305, C_306) | ~r2_hidden(A_305, C_306))), inference(superposition, [status(thm), theory('equality')], [c_66, c_2349])).
% 8.29/2.88  tff(c_42, plain, (![A_24, B_25]: (k2_xboole_0(A_24, B_25)=B_25 | ~r1_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_71])).
% 8.29/2.88  tff(c_4930, plain, (![A_307, C_308]: (k2_xboole_0(k1_tarski(A_307), C_308)=C_308 | ~r2_hidden(A_307, C_308))), inference(resolution, [status(thm)], [c_4891, c_42])).
% 8.29/2.88  tff(c_52, plain, (![A_34, B_35]: (k5_xboole_0(k5_xboole_0(A_34, B_35), k2_xboole_0(A_34, B_35))=k3_xboole_0(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.29/2.88  tff(c_4975, plain, (![A_307, C_308]: (k5_xboole_0(k5_xboole_0(k1_tarski(A_307), C_308), C_308)=k3_xboole_0(k1_tarski(A_307), C_308) | ~r2_hidden(A_307, C_308))), inference(superposition, [status(thm), theory('equality')], [c_4930, c_52])).
% 8.29/2.88  tff(c_5307, plain, (![A_320, C_321]: (k3_xboole_0(k1_tarski(A_320), C_321)=k1_tarski(A_320) | ~r2_hidden(A_320, C_321))), inference(demodulation, [status(thm), theory('equality')], [c_1698, c_1713, c_4975])).
% 8.29/2.88  tff(c_38, plain, (![A_20, B_21]: (k5_xboole_0(A_20, k3_xboole_0(A_20, B_21))=k4_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_62])).
% 8.29/2.88  tff(c_5338, plain, (![A_320, C_321]: (k5_xboole_0(k1_tarski(A_320), k1_tarski(A_320))=k4_xboole_0(k1_tarski(A_320), C_321) | ~r2_hidden(A_320, C_321))), inference(superposition, [status(thm), theory('equality')], [c_5307, c_38])).
% 8.29/2.88  tff(c_5366, plain, (![A_322, C_323]: (k4_xboole_0(k1_tarski(A_322), C_323)='#skF_9' | ~r2_hidden(A_322, C_323))), inference(demodulation, [status(thm), theory('equality')], [c_384, c_5338])).
% 8.29/2.88  tff(c_88, plain, (k1_xboole_0!='#skF_9' | k1_tarski('#skF_7')!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_129])).
% 8.29/2.88  tff(c_136, plain, (k1_tarski('#skF_7')!='#skF_8'), inference(splitLeft, [status(thm)], [c_88])).
% 8.29/2.88  tff(c_137, plain, (![A_80, B_81]: (r1_tarski(A_80, k2_xboole_0(A_80, B_81)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 8.29/2.88  tff(c_140, plain, (r1_tarski('#skF_8', k1_tarski('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_94, c_137])).
% 8.29/2.88  tff(c_532, plain, (![A_142, B_143]: (r2_xboole_0(A_142, B_143) | B_143=A_142 | ~r1_tarski(A_142, B_143))), inference(cnfTransformation, [status(thm)], [f_48])).
% 8.29/2.88  tff(c_40, plain, (![B_23, A_22]: (k4_xboole_0(B_23, A_22)!=k1_xboole_0 | ~r2_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.29/2.88  tff(c_381, plain, (![B_23, A_22]: (k4_xboole_0(B_23, A_22)!='#skF_9' | ~r2_xboole_0(A_22, B_23))), inference(demodulation, [status(thm), theory('equality')], [c_379, c_40])).
% 8.29/2.88  tff(c_4440, plain, (![B_286, A_287]: (k4_xboole_0(B_286, A_287)!='#skF_9' | B_286=A_287 | ~r1_tarski(A_287, B_286))), inference(resolution, [status(thm)], [c_532, c_381])).
% 8.29/2.88  tff(c_4458, plain, (k4_xboole_0(k1_tarski('#skF_7'), '#skF_8')!='#skF_9' | k1_tarski('#skF_7')='#skF_8'), inference(resolution, [status(thm)], [c_140, c_4440])).
% 8.29/2.88  tff(c_4475, plain, (k4_xboole_0(k1_tarski('#skF_7'), '#skF_8')!='#skF_9'), inference(negUnitSimplification, [status(thm)], [c_136, c_4458])).
% 8.29/2.88  tff(c_5372, plain, (~r2_hidden('#skF_7', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_5366, c_4475])).
% 8.29/2.88  tff(c_5408, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_348, c_5372])).
% 8.29/2.88  tff(c_5410, plain, (k1_xboole_0!='#skF_9'), inference(splitRight, [status(thm)], [c_378])).
% 8.29/2.88  tff(c_5409, plain, ('#skF_4'('#skF_9')='#skF_7'), inference(splitRight, [status(thm)], [c_378])).
% 8.29/2.88  tff(c_5427, plain, (r2_hidden('#skF_7', '#skF_9') | k1_xboole_0='#skF_9'), inference(superposition, [status(thm), theory('equality')], [c_5409, c_36])).
% 8.29/2.88  tff(c_5430, plain, (r2_hidden('#skF_7', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_5410, c_5427])).
% 8.29/2.88  tff(c_5516, plain, (![A_339, B_340]: (r2_hidden('#skF_1'(A_339, B_340), A_339) | r1_tarski(A_339, B_340))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.29/2.88  tff(c_333, plain, (![D_115]: (D_115='#skF_7' | ~r2_hidden(D_115, '#skF_8'))), inference(resolution, [status(thm)], [c_329, c_54])).
% 8.29/2.88  tff(c_5543, plain, (![B_342]: ('#skF_1'('#skF_8', B_342)='#skF_7' | r1_tarski('#skF_8', B_342))), inference(resolution, [status(thm)], [c_5516, c_333])).
% 8.29/2.88  tff(c_5629, plain, (![B_345]: (k2_xboole_0('#skF_8', B_345)=B_345 | '#skF_1'('#skF_8', B_345)='#skF_7')), inference(resolution, [status(thm)], [c_5543, c_42])).
% 8.29/2.88  tff(c_5654, plain, (k1_tarski('#skF_7')='#skF_9' | '#skF_1'('#skF_8', '#skF_9')='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_5629, c_94])).
% 8.29/2.88  tff(c_5685, plain, ('#skF_1'('#skF_8', '#skF_9')='#skF_7'), inference(splitLeft, [status(thm)], [c_5654])).
% 8.29/2.88  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.29/2.88  tff(c_5735, plain, (~r2_hidden('#skF_7', '#skF_9') | r1_tarski('#skF_8', '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_5685, c_4])).
% 8.29/2.88  tff(c_5740, plain, (r1_tarski('#skF_8', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_5430, c_5735])).
% 8.29/2.88  tff(c_5745, plain, (k2_xboole_0('#skF_8', '#skF_9')='#skF_9'), inference(resolution, [status(thm)], [c_5740, c_42])).
% 8.29/2.88  tff(c_5746, plain, (k1_tarski('#skF_7')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_5745, c_94])).
% 8.29/2.88  tff(c_5782, plain, ('#skF_9'!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_5746, c_136])).
% 8.29/2.88  tff(c_8168, plain, (![A_426, B_427]: ('#skF_5'(A_426, B_427)=A_426 | r2_hidden('#skF_6'(A_426, B_427), B_427) | k1_tarski(A_426)=B_427)), inference(cnfTransformation, [status(thm)], [f_88])).
% 8.29/2.88  tff(c_8325, plain, (![A_430]: ('#skF_6'(A_430, '#skF_8')='#skF_7' | '#skF_5'(A_430, '#skF_8')=A_430 | k1_tarski(A_430)='#skF_8')), inference(resolution, [status(thm)], [c_8168, c_333])).
% 8.29/2.88  tff(c_8343, plain, ('#skF_9'='#skF_8' | '#skF_6'('#skF_7', '#skF_8')='#skF_7' | '#skF_5'('#skF_7', '#skF_8')='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_8325, c_5746])).
% 8.29/2.88  tff(c_8371, plain, ('#skF_6'('#skF_7', '#skF_8')='#skF_7' | '#skF_5'('#skF_7', '#skF_8')='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_5782, c_8343])).
% 8.29/2.88  tff(c_8476, plain, ('#skF_5'('#skF_7', '#skF_8')='#skF_7'), inference(splitLeft, [status(thm)], [c_8371])).
% 8.29/2.88  tff(c_58, plain, (![A_36, B_37]: (~r2_hidden('#skF_5'(A_36, B_37), B_37) | '#skF_6'(A_36, B_37)!=A_36 | k1_tarski(A_36)=B_37)), inference(cnfTransformation, [status(thm)], [f_88])).
% 8.29/2.88  tff(c_8480, plain, (~r2_hidden('#skF_7', '#skF_8') | '#skF_6'('#skF_7', '#skF_8')!='#skF_7' | k1_tarski('#skF_7')='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_8476, c_58])).
% 8.29/2.88  tff(c_8484, plain, ('#skF_6'('#skF_7', '#skF_8')!='#skF_7' | '#skF_9'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_5746, c_348, c_8480])).
% 8.29/2.88  tff(c_8485, plain, ('#skF_6'('#skF_7', '#skF_8')!='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_5782, c_8484])).
% 8.29/2.88  tff(c_8674, plain, (![A_441, B_442]: (~r2_hidden('#skF_5'(A_441, B_442), B_442) | r2_hidden('#skF_6'(A_441, B_442), B_442) | k1_tarski(A_441)=B_442)), inference(cnfTransformation, [status(thm)], [f_88])).
% 8.29/2.88  tff(c_8899, plain, (![A_451]: ('#skF_6'(A_451, '#skF_8')='#skF_7' | ~r2_hidden('#skF_5'(A_451, '#skF_8'), '#skF_8') | k1_tarski(A_451)='#skF_8')), inference(resolution, [status(thm)], [c_8674, c_333])).
% 8.29/2.88  tff(c_8902, plain, ('#skF_6'('#skF_7', '#skF_8')='#skF_7' | ~r2_hidden('#skF_7', '#skF_8') | k1_tarski('#skF_7')='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_8476, c_8899])).
% 8.29/2.88  tff(c_8904, plain, ('#skF_6'('#skF_7', '#skF_8')='#skF_7' | '#skF_9'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_5746, c_348, c_8902])).
% 8.29/2.88  tff(c_8906, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5782, c_8485, c_8904])).
% 8.29/2.88  tff(c_8908, plain, ('#skF_5'('#skF_7', '#skF_8')!='#skF_7'), inference(splitRight, [status(thm)], [c_8371])).
% 8.29/2.88  tff(c_8907, plain, ('#skF_6'('#skF_7', '#skF_8')='#skF_7'), inference(splitRight, [status(thm)], [c_8371])).
% 8.29/2.88  tff(c_60, plain, (![A_36, B_37]: ('#skF_5'(A_36, B_37)=A_36 | '#skF_6'(A_36, B_37)!=A_36 | k1_tarski(A_36)=B_37)), inference(cnfTransformation, [status(thm)], [f_88])).
% 8.29/2.88  tff(c_8914, plain, ('#skF_5'('#skF_7', '#skF_8')='#skF_7' | k1_tarski('#skF_7')='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_8907, c_60])).
% 8.29/2.88  tff(c_8920, plain, ('#skF_5'('#skF_7', '#skF_8')='#skF_7' | '#skF_9'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_5746, c_8914])).
% 8.29/2.88  tff(c_8921, plain, ('#skF_5'('#skF_7', '#skF_8')='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_5782, c_8920])).
% 8.29/2.88  tff(c_8923, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8908, c_8921])).
% 8.29/2.88  tff(c_8924, plain, (k1_tarski('#skF_7')='#skF_9'), inference(splitRight, [status(thm)], [c_5654])).
% 8.29/2.88  tff(c_8933, plain, ('#skF_9'!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_8924, c_136])).
% 8.29/2.88  tff(c_11509, plain, (![A_535, B_536]: ('#skF_5'(A_535, B_536)=A_535 | r2_hidden('#skF_6'(A_535, B_536), B_536) | k1_tarski(A_535)=B_536)), inference(cnfTransformation, [status(thm)], [f_88])).
% 8.29/2.88  tff(c_11611, plain, (![A_538]: ('#skF_6'(A_538, '#skF_8')='#skF_7' | '#skF_5'(A_538, '#skF_8')=A_538 | k1_tarski(A_538)='#skF_8')), inference(resolution, [status(thm)], [c_11509, c_333])).
% 8.29/2.88  tff(c_11653, plain, ('#skF_6'('#skF_7', '#skF_8')='#skF_7' | '#skF_5'('#skF_7', '#skF_8')='#skF_7' | '#skF_9'='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_8924, c_11611])).
% 8.29/2.88  tff(c_11660, plain, ('#skF_6'('#skF_7', '#skF_8')='#skF_7' | '#skF_5'('#skF_7', '#skF_8')='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_8933, c_11653])).
% 8.47/2.88  tff(c_11904, plain, ('#skF_5'('#skF_7', '#skF_8')='#skF_7'), inference(splitLeft, [status(thm)], [c_11660])).
% 8.47/2.88  tff(c_11908, plain, (~r2_hidden('#skF_7', '#skF_8') | '#skF_6'('#skF_7', '#skF_8')!='#skF_7' | k1_tarski('#skF_7')='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_11904, c_58])).
% 8.47/2.88  tff(c_11912, plain, ('#skF_6'('#skF_7', '#skF_8')!='#skF_7' | '#skF_9'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_8924, c_348, c_11908])).
% 8.47/2.88  tff(c_11913, plain, ('#skF_6'('#skF_7', '#skF_8')!='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_8933, c_11912])).
% 8.47/2.88  tff(c_12050, plain, (![A_551, B_552]: (~r2_hidden('#skF_5'(A_551, B_552), B_552) | r2_hidden('#skF_6'(A_551, B_552), B_552) | k1_tarski(A_551)=B_552)), inference(cnfTransformation, [status(thm)], [f_88])).
% 8.47/2.88  tff(c_12272, plain, (![A_570]: ('#skF_6'(A_570, '#skF_8')='#skF_7' | ~r2_hidden('#skF_5'(A_570, '#skF_8'), '#skF_8') | k1_tarski(A_570)='#skF_8')), inference(resolution, [status(thm)], [c_12050, c_333])).
% 8.47/2.88  tff(c_12275, plain, ('#skF_6'('#skF_7', '#skF_8')='#skF_7' | ~r2_hidden('#skF_7', '#skF_8') | k1_tarski('#skF_7')='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_11904, c_12272])).
% 8.47/2.88  tff(c_12277, plain, ('#skF_6'('#skF_7', '#skF_8')='#skF_7' | '#skF_9'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_8924, c_348, c_12275])).
% 8.47/2.88  tff(c_12279, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8933, c_11913, c_12277])).
% 8.47/2.88  tff(c_12281, plain, ('#skF_5'('#skF_7', '#skF_8')!='#skF_7'), inference(splitRight, [status(thm)], [c_11660])).
% 8.47/2.88  tff(c_12280, plain, ('#skF_6'('#skF_7', '#skF_8')='#skF_7'), inference(splitRight, [status(thm)], [c_11660])).
% 8.47/2.88  tff(c_12287, plain, ('#skF_5'('#skF_7', '#skF_8')='#skF_7' | k1_tarski('#skF_7')='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_12280, c_60])).
% 8.47/2.88  tff(c_12293, plain, ('#skF_5'('#skF_7', '#skF_8')='#skF_7' | '#skF_9'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_8924, c_12287])).
% 8.47/2.88  tff(c_12294, plain, ('#skF_5'('#skF_7', '#skF_8')='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_8933, c_12293])).
% 8.47/2.88  tff(c_12296, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12281, c_12294])).
% 8.47/2.88  tff(c_12298, plain, (k1_tarski('#skF_7')='#skF_8'), inference(splitRight, [status(thm)], [c_88])).
% 8.47/2.88  tff(c_92, plain, (k1_tarski('#skF_7')!='#skF_9' | k1_tarski('#skF_7')!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_129])).
% 8.47/2.88  tff(c_12320, plain, ('#skF_9'!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_12298, c_12298, c_92])).
% 8.47/2.88  tff(c_12299, plain, (k2_xboole_0('#skF_8', '#skF_9')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_12298, c_94])).
% 8.47/2.88  tff(c_12297, plain, (k1_xboole_0!='#skF_9'), inference(splitRight, [status(thm)], [c_88])).
% 8.47/2.88  tff(c_12548, plain, (![D_614, B_615, A_616]: (~r2_hidden(D_614, B_615) | r2_hidden(D_614, k2_xboole_0(A_616, B_615)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.47/2.88  tff(c_12560, plain, (![D_617]: (~r2_hidden(D_617, '#skF_9') | r2_hidden(D_617, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_12299, c_12548])).
% 8.47/2.88  tff(c_12568, plain, (r2_hidden('#skF_4'('#skF_9'), '#skF_8') | k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_36, c_12560])).
% 8.47/2.88  tff(c_12573, plain, (r2_hidden('#skF_4'('#skF_9'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_12297, c_12568])).
% 8.47/2.88  tff(c_12322, plain, (![C_574, A_575]: (C_574=A_575 | ~r2_hidden(C_574, k1_tarski(A_575)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 8.47/2.88  tff(c_12325, plain, (![C_574]: (C_574='#skF_7' | ~r2_hidden(C_574, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_12298, c_12322])).
% 8.47/2.88  tff(c_12577, plain, ('#skF_4'('#skF_9')='#skF_7'), inference(resolution, [status(thm)], [c_12573, c_12325])).
% 8.47/2.88  tff(c_12583, plain, (r2_hidden('#skF_7', '#skF_9') | k1_xboole_0='#skF_9'), inference(superposition, [status(thm), theory('equality')], [c_12577, c_36])).
% 8.47/2.88  tff(c_12586, plain, (r2_hidden('#skF_7', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_12297, c_12583])).
% 8.47/2.88  tff(c_12690, plain, (![A_629, B_630]: (r2_hidden('#skF_1'(A_629, B_630), A_629) | r1_tarski(A_629, B_630))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.47/2.88  tff(c_12712, plain, (![B_631]: ('#skF_1'('#skF_8', B_631)='#skF_7' | r1_tarski('#skF_8', B_631))), inference(resolution, [status(thm)], [c_12690, c_12325])).
% 8.47/2.88  tff(c_12781, plain, (![B_635]: (k2_xboole_0('#skF_8', B_635)=B_635 | '#skF_1'('#skF_8', B_635)='#skF_7')), inference(resolution, [status(thm)], [c_12712, c_42])).
% 8.47/2.88  tff(c_12805, plain, ('#skF_9'='#skF_8' | '#skF_1'('#skF_8', '#skF_9')='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_12781, c_12299])).
% 8.47/2.88  tff(c_12827, plain, ('#skF_1'('#skF_8', '#skF_9')='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_12320, c_12805])).
% 8.47/2.88  tff(c_12839, plain, (~r2_hidden('#skF_7', '#skF_9') | r1_tarski('#skF_8', '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_12827, c_4])).
% 8.47/2.88  tff(c_12844, plain, (r1_tarski('#skF_8', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_12586, c_12839])).
% 8.47/2.88  tff(c_12857, plain, (k2_xboole_0('#skF_8', '#skF_9')='#skF_9'), inference(resolution, [status(thm)], [c_12844, c_42])).
% 8.47/2.88  tff(c_12859, plain, ('#skF_9'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_12299, c_12857])).
% 8.47/2.88  tff(c_12861, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12320, c_12859])).
% 8.47/2.88  tff(c_12862, plain, (k1_tarski('#skF_7')!='#skF_9'), inference(splitRight, [status(thm)], [c_90])).
% 8.47/2.88  tff(c_12863, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_90])).
% 8.47/2.88  tff(c_12869, plain, ('#skF_9'!='#skF_8' | k1_tarski('#skF_7')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_12863, c_88])).
% 8.47/2.88  tff(c_12870, plain, (k1_tarski('#skF_7')!='#skF_8'), inference(splitLeft, [status(thm)], [c_12869])).
% 8.47/2.88  tff(c_12886, plain, (![A_18]: (r2_hidden('#skF_4'(A_18), A_18) | A_18='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_12863, c_36])).
% 8.47/2.88  tff(c_13097, plain, (![D_675, B_676, A_677]: (~r2_hidden(D_675, B_676) | r2_hidden(D_675, k2_xboole_0(A_677, B_676)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.47/2.88  tff(c_13115, plain, (![D_678]: (~r2_hidden(D_678, '#skF_9') | r2_hidden(D_678, k1_tarski('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_94, c_13097])).
% 8.47/2.88  tff(c_13125, plain, (![D_679]: (D_679='#skF_7' | ~r2_hidden(D_679, '#skF_9'))), inference(resolution, [status(thm)], [c_13115, c_54])).
% 8.47/2.88  tff(c_13135, plain, ('#skF_4'('#skF_9')='#skF_7' | '#skF_9'='#skF_8'), inference(resolution, [status(thm)], [c_12886, c_13125])).
% 8.47/2.88  tff(c_13136, plain, ('#skF_9'='#skF_8'), inference(splitLeft, [status(thm)], [c_13135])).
% 8.47/2.88  tff(c_13140, plain, (k2_xboole_0('#skF_8', '#skF_8')=k1_tarski('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_13136, c_94])).
% 8.47/2.88  tff(c_13141, plain, (k1_tarski('#skF_7')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_13140])).
% 8.47/2.88  tff(c_13143, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12870, c_13141])).
% 8.47/2.88  tff(c_13145, plain, ('#skF_9'!='#skF_8'), inference(splitRight, [status(thm)], [c_13135])).
% 8.47/2.88  tff(c_13144, plain, ('#skF_4'('#skF_9')='#skF_7'), inference(splitRight, [status(thm)], [c_13135])).
% 8.47/2.88  tff(c_13149, plain, (r2_hidden('#skF_7', '#skF_9') | '#skF_9'='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_13144, c_12886])).
% 8.47/2.88  tff(c_13152, plain, (r2_hidden('#skF_7', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_13145, c_13149])).
% 8.47/2.88  tff(c_13075, plain, (![A_672, B_673]: (r2_hidden('#skF_1'(A_672, B_673), A_672) | r1_tarski(A_672, B_673))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.47/2.88  tff(c_13022, plain, (![D_663, A_664, B_665]: (~r2_hidden(D_663, A_664) | r2_hidden(D_663, k2_xboole_0(A_664, B_665)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.47/2.88  tff(c_13035, plain, (![D_666]: (~r2_hidden(D_666, '#skF_8') | r2_hidden(D_666, k1_tarski('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_94, c_13022])).
% 8.47/2.88  tff(c_13039, plain, (![D_666]: (D_666='#skF_7' | ~r2_hidden(D_666, '#skF_8'))), inference(resolution, [status(thm)], [c_13035, c_54])).
% 8.47/2.88  tff(c_13092, plain, (![B_674]: ('#skF_1'('#skF_8', B_674)='#skF_7' | r1_tarski('#skF_8', B_674))), inference(resolution, [status(thm)], [c_13075, c_13039])).
% 8.47/2.88  tff(c_13273, plain, (![B_705]: (k2_xboole_0('#skF_8', B_705)=B_705 | '#skF_1'('#skF_8', B_705)='#skF_7')), inference(resolution, [status(thm)], [c_13092, c_42])).
% 8.47/2.88  tff(c_13298, plain, (k1_tarski('#skF_7')='#skF_9' | '#skF_1'('#skF_8', '#skF_9')='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_13273, c_94])).
% 8.47/2.88  tff(c_13324, plain, ('#skF_1'('#skF_8', '#skF_9')='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_12862, c_13298])).
% 8.47/2.88  tff(c_13337, plain, (~r2_hidden('#skF_7', '#skF_9') | r1_tarski('#skF_8', '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_13324, c_4])).
% 8.47/2.88  tff(c_13341, plain, (r1_tarski('#skF_8', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_13152, c_13337])).
% 8.47/2.88  tff(c_13347, plain, (k2_xboole_0('#skF_8', '#skF_9')='#skF_9'), inference(resolution, [status(thm)], [c_13341, c_42])).
% 8.47/2.88  tff(c_13348, plain, (k1_tarski('#skF_7')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_13347, c_94])).
% 8.47/2.88  tff(c_13350, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12862, c_13348])).
% 8.47/2.88  tff(c_13351, plain, ('#skF_9'!='#skF_8'), inference(splitRight, [status(thm)], [c_12869])).
% 8.47/2.88  tff(c_13352, plain, (k1_tarski('#skF_7')='#skF_8'), inference(splitRight, [status(thm)], [c_12869])).
% 8.47/2.88  tff(c_13354, plain, (k2_xboole_0('#skF_8', '#skF_9')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_13352, c_94])).
% 8.47/2.88  tff(c_13643, plain, (![A_753, B_754]: (r2_hidden('#skF_1'(A_753, B_754), A_753) | r1_tarski(A_753, B_754))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.47/2.88  tff(c_13384, plain, (![C_710, A_711]: (C_710=A_711 | ~r2_hidden(C_710, k1_tarski(A_711)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 8.47/2.88  tff(c_13387, plain, (![C_710]: (C_710='#skF_7' | ~r2_hidden(C_710, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_13352, c_13384])).
% 8.47/2.88  tff(c_13675, plain, (![B_758]: ('#skF_1'('#skF_8', B_758)='#skF_7' | r1_tarski('#skF_8', B_758))), inference(resolution, [status(thm)], [c_13643, c_13387])).
% 8.47/2.88  tff(c_13706, plain, (![B_760]: (k2_xboole_0('#skF_8', B_760)=B_760 | '#skF_1'('#skF_8', B_760)='#skF_7')), inference(resolution, [status(thm)], [c_13675, c_42])).
% 8.47/2.88  tff(c_13727, plain, ('#skF_9'='#skF_8' | '#skF_1'('#skF_8', '#skF_9')='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_13706, c_13354])).
% 8.47/2.88  tff(c_13749, plain, ('#skF_1'('#skF_8', '#skF_9')='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_13351, c_13727])).
% 8.47/2.88  tff(c_13761, plain, (~r2_hidden('#skF_7', '#skF_9') | r1_tarski('#skF_8', '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_13749, c_4])).
% 8.47/2.88  tff(c_13767, plain, (~r2_hidden('#skF_7', '#skF_9')), inference(splitLeft, [status(thm)], [c_13761])).
% 8.47/2.88  tff(c_13399, plain, (![A_18]: (r2_hidden('#skF_4'(A_18), A_18) | A_18='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_12863, c_36])).
% 8.47/2.88  tff(c_13814, plain, (![D_765, B_766, A_767]: (~r2_hidden(D_765, B_766) | r2_hidden(D_765, k2_xboole_0(A_767, B_766)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.47/2.88  tff(c_13832, plain, (![D_768]: (~r2_hidden(D_768, '#skF_9') | r2_hidden(D_768, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_13354, c_13814])).
% 8.47/2.88  tff(c_13848, plain, (r2_hidden('#skF_4'('#skF_9'), '#skF_8') | '#skF_9'='#skF_8'), inference(resolution, [status(thm)], [c_13399, c_13832])).
% 8.47/2.88  tff(c_13856, plain, (r2_hidden('#skF_4'('#skF_9'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_13351, c_13848])).
% 8.47/2.88  tff(c_13860, plain, ('#skF_4'('#skF_9')='#skF_7'), inference(resolution, [status(thm)], [c_13856, c_13387])).
% 8.47/2.88  tff(c_13866, plain, (r2_hidden('#skF_7', '#skF_9') | '#skF_9'='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_13860, c_13399])).
% 8.47/2.88  tff(c_13870, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13351, c_13767, c_13866])).
% 8.47/2.88  tff(c_13871, plain, (r1_tarski('#skF_8', '#skF_9')), inference(splitRight, [status(thm)], [c_13761])).
% 8.47/2.88  tff(c_13875, plain, (k2_xboole_0('#skF_8', '#skF_9')='#skF_9'), inference(resolution, [status(thm)], [c_13871, c_42])).
% 8.47/2.88  tff(c_13877, plain, ('#skF_9'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_13354, c_13875])).
% 8.47/2.88  tff(c_13879, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13351, c_13877])).
% 8.47/2.88  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.47/2.88  
% 8.47/2.88  Inference rules
% 8.47/2.88  ----------------------
% 8.47/2.88  #Ref     : 0
% 8.47/2.88  #Sup     : 3232
% 8.47/2.88  #Fact    : 4
% 8.47/2.88  #Define  : 0
% 8.47/2.88  #Split   : 16
% 8.47/2.88  #Chain   : 0
% 8.47/2.88  #Close   : 0
% 8.47/2.88  
% 8.47/2.88  Ordering : KBO
% 8.47/2.88  
% 8.47/2.88  Simplification rules
% 8.47/2.88  ----------------------
% 8.47/2.89  #Subsume      : 164
% 8.47/2.89  #Demod        : 2084
% 8.47/2.89  #Tautology    : 2038
% 8.47/2.89  #SimpNegUnit  : 70
% 8.47/2.89  #BackRed      : 73
% 8.47/2.89  
% 8.47/2.89  #Partial instantiations: 0
% 8.47/2.89  #Strategies tried      : 1
% 8.47/2.89  
% 8.47/2.89  Timing (in seconds)
% 8.47/2.89  ----------------------
% 8.47/2.89  Preprocessing        : 0.37
% 8.47/2.89  Parsing              : 0.19
% 8.47/2.89  CNF conversion       : 0.03
% 8.47/2.89  Main loop            : 1.62
% 8.47/2.89  Inferencing          : 0.52
% 8.47/2.89  Reduction            : 0.63
% 8.47/2.89  Demodulation         : 0.48
% 8.47/2.89  BG Simplification    : 0.06
% 8.47/2.89  Subsumption          : 0.29
% 8.47/2.89  Abstraction          : 0.07
% 8.47/2.89  MUC search           : 0.00
% 8.47/2.89  Cooper               : 0.00
% 8.47/2.89  Total                : 2.07
% 8.47/2.89  Index Insertion      : 0.00
% 8.47/2.89  Index Deletion       : 0.00
% 8.47/2.89  Index Matching       : 0.00
% 8.47/2.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------
