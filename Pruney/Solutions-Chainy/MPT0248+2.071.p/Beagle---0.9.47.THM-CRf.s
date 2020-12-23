%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:14 EST 2020

% Result     : Theorem 5.92s
% Output     : CNFRefutation 5.92s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 451 expanded)
%              Number of leaves         :   41 ( 167 expanded)
%              Depth                    :   11
%              Number of atoms          :  172 ( 748 expanded)
%              Number of equality atoms :  104 ( 602 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

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

tff(f_114,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_58,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_75,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_93,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_62,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_64,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_60,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(c_76,plain,
    ( k1_xboole_0 != '#skF_7'
    | k1_tarski('#skF_5') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_112,plain,(
    k1_tarski('#skF_5') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_82,plain,(
    k2_xboole_0('#skF_6','#skF_7') = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_28,plain,(
    ! [A_22,B_23] : r1_tarski(A_22,k2_xboole_0(A_22,B_23)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_738,plain,(
    ! [B_166,A_167] :
      ( B_166 = A_167
      | ~ r1_tarski(B_166,A_167)
      | ~ r1_tarski(A_167,B_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_3646,plain,(
    ! [A_312,B_313] :
      ( k2_xboole_0(A_312,B_313) = A_312
      | ~ r1_tarski(k2_xboole_0(A_312,B_313),A_312) ) ),
    inference(resolution,[status(thm)],[c_28,c_738])).

tff(c_3665,plain,
    ( k2_xboole_0('#skF_6','#skF_7') = '#skF_6'
    | ~ r1_tarski(k1_tarski('#skF_5'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_3646])).

tff(c_3673,plain,
    ( k1_tarski('#skF_5') = '#skF_6'
    | ~ r1_tarski(k1_tarski('#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_3665])).

tff(c_3674,plain,(
    ~ r1_tarski(k1_tarski('#skF_5'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_3673])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_2'(A_7,B_8),A_7)
      | r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_54,plain,(
    ! [A_36] : k2_tarski(A_36,A_36) = k1_tarski(A_36) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_888,plain,(
    ! [D_193,B_194,A_195] :
      ( D_193 = B_194
      | D_193 = A_195
      | ~ r2_hidden(D_193,k2_tarski(A_195,B_194)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1035,plain,(
    ! [D_215,A_216] :
      ( D_215 = A_216
      | D_215 = A_216
      | ~ r2_hidden(D_215,k1_tarski(A_216)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_888])).

tff(c_3789,plain,(
    ! [A_315,B_316] :
      ( '#skF_2'(k1_tarski(A_315),B_316) = A_315
      | r1_tarski(k1_tarski(A_315),B_316) ) ),
    inference(resolution,[status(thm)],[c_12,c_1035])).

tff(c_3819,plain,(
    '#skF_2'(k1_tarski('#skF_5'),'#skF_6') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_3789,c_3674])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( ~ r2_hidden('#skF_2'(A_7,B_8),B_8)
      | r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_3833,plain,
    ( ~ r2_hidden('#skF_5','#skF_6')
    | r1_tarski(k1_tarski('#skF_5'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_3819,c_10])).

tff(c_3839,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_3674,c_3833])).

tff(c_78,plain,
    ( k1_tarski('#skF_5') != '#skF_7'
    | k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_126,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_150,plain,(
    ! [A_81,B_82] : r1_tarski(A_81,k2_xboole_0(A_81,B_82)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_153,plain,(
    r1_tarski('#skF_6',k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_150])).

tff(c_539,plain,(
    ! [B_137,A_138] :
      ( k1_tarski(B_137) = A_138
      | k1_xboole_0 = A_138
      | ~ r1_tarski(A_138,k1_tarski(B_137)) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_550,plain,
    ( k1_tarski('#skF_5') = '#skF_6'
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_153,c_539])).

tff(c_563,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_126,c_112,c_550])).

tff(c_564,plain,(
    k1_tarski('#skF_5') != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_16,plain,(
    ! [A_14] : k3_xboole_0(A_14,A_14) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_14,plain,(
    ! [A_12] : k2_xboole_0(A_12,A_12) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_565,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_32,plain,(
    ! [A_27] : k5_xboole_0(A_27,A_27) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_566,plain,(
    ! [A_27] : k5_xboole_0(A_27,A_27) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_565,c_32])).

tff(c_1053,plain,(
    ! [A_217,B_218] : k5_xboole_0(k5_xboole_0(A_217,B_218),k2_xboole_0(A_217,B_218)) = k3_xboole_0(A_217,B_218) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1098,plain,(
    ! [A_27] : k5_xboole_0('#skF_6',k2_xboole_0(A_27,A_27)) = k3_xboole_0(A_27,A_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_566,c_1053])).

tff(c_1105,plain,(
    ! [A_27] : k5_xboole_0('#skF_6',A_27) = A_27 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_1098])).

tff(c_1239,plain,(
    ! [A_225,B_226,C_227] : k5_xboole_0(k5_xboole_0(A_225,B_226),C_227) = k5_xboole_0(A_225,k5_xboole_0(B_226,C_227)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1308,plain,(
    ! [A_27,C_227] : k5_xboole_0(A_27,k5_xboole_0(A_27,C_227)) = k5_xboole_0('#skF_6',C_227) ),
    inference(superposition,[status(thm),theory(equality)],[c_566,c_1239])).

tff(c_1322,plain,(
    ! [A_228,C_229] : k5_xboole_0(A_228,k5_xboole_0(A_228,C_229)) = C_229 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1105,c_1308])).

tff(c_1374,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k5_xboole_0(B_2,A_1)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1322])).

tff(c_72,plain,(
    ! [B_65] : r1_tarski(k1_xboole_0,k1_tarski(B_65)) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_567,plain,(
    ! [B_65] : r1_tarski('#skF_6',k1_tarski(B_65)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_565,c_72])).

tff(c_6,plain,(
    ! [A_3] :
      ( v1_xboole_0(A_3)
      | r2_hidden('#skF_1'(A_3),A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_872,plain,(
    ! [C_190,B_191,A_192] :
      ( r2_hidden(C_190,B_191)
      | ~ r2_hidden(C_190,A_192)
      | ~ r1_tarski(A_192,B_191) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_3422,plain,(
    ! [A_292,B_293] :
      ( r2_hidden('#skF_1'(A_292),B_293)
      | ~ r1_tarski(A_292,B_293)
      | v1_xboole_0(A_292) ) ),
    inference(resolution,[status(thm)],[c_6,c_872])).

tff(c_905,plain,(
    ! [D_193,A_36] :
      ( D_193 = A_36
      | D_193 = A_36
      | ~ r2_hidden(D_193,k1_tarski(A_36)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_888])).

tff(c_3947,plain,(
    ! [A_325,A_326] :
      ( A_325 = '#skF_1'(A_326)
      | ~ r1_tarski(A_326,k1_tarski(A_325))
      | v1_xboole_0(A_326) ) ),
    inference(resolution,[status(thm)],[c_3422,c_905])).

tff(c_3977,plain,(
    ! [B_65] :
      ( B_65 = '#skF_1'('#skF_6')
      | v1_xboole_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_567,c_3947])).

tff(c_3981,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_3977])).

tff(c_26,plain,(
    ! [A_20,B_21] : r1_tarski(k3_xboole_0(A_20,B_21),A_20) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_755,plain,(
    ! [A_169,B_170] :
      ( r2_hidden('#skF_2'(A_169,B_170),A_169)
      | r1_tarski(A_169,B_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_4,plain,(
    ! [B_6,A_3] :
      ( ~ r2_hidden(B_6,A_3)
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_767,plain,(
    ! [A_173,B_174] :
      ( ~ v1_xboole_0(A_173)
      | r1_tarski(A_173,B_174) ) ),
    inference(resolution,[status(thm)],[c_755,c_4])).

tff(c_18,plain,(
    ! [B_17,A_16] :
      ( B_17 = A_16
      | ~ r1_tarski(B_17,A_16)
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_780,plain,(
    ! [B_177,A_178] :
      ( B_177 = A_178
      | ~ r1_tarski(B_177,A_178)
      | ~ v1_xboole_0(A_178) ) ),
    inference(resolution,[status(thm)],[c_767,c_18])).

tff(c_797,plain,(
    ! [A_20,B_21] :
      ( k3_xboole_0(A_20,B_21) = A_20
      | ~ v1_xboole_0(A_20) ) ),
    inference(resolution,[status(thm)],[c_26,c_780])).

tff(c_4160,plain,(
    ! [B_21] : k3_xboole_0('#skF_6',B_21) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_3981,c_797])).

tff(c_1095,plain,(
    k5_xboole_0(k5_xboole_0('#skF_6','#skF_7'),k1_tarski('#skF_5')) = k3_xboole_0('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_1053])).

tff(c_1158,plain,(
    k5_xboole_0('#skF_7',k1_tarski('#skF_5')) = k3_xboole_0('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1105,c_1095])).

tff(c_1921,plain,(
    ! [C_248] : k5_xboole_0('#skF_7',k5_xboole_0(k1_tarski('#skF_5'),C_248)) = k5_xboole_0(k3_xboole_0('#skF_6','#skF_7'),C_248) ),
    inference(superposition,[status(thm),theory(equality)],[c_1158,c_1239])).

tff(c_1933,plain,(
    ! [C_248] : k5_xboole_0(k5_xboole_0(k1_tarski('#skF_5'),C_248),k5_xboole_0(k3_xboole_0('#skF_6','#skF_7'),C_248)) = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_1921,c_1374])).

tff(c_4172,plain,(
    ! [C_248] : k5_xboole_0(k5_xboole_0(k1_tarski('#skF_5'),C_248),k5_xboole_0('#skF_6',C_248)) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4160,c_1933])).

tff(c_4194,plain,(
    k1_tarski('#skF_5') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1374,c_2,c_1105,c_4172])).

tff(c_4196,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_564,c_4194])).

tff(c_4198,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_3977])).

tff(c_4590,plain,(
    '#skF_1'('#skF_6') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_3977])).

tff(c_4593,plain,
    ( v1_xboole_0('#skF_6')
    | r2_hidden('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_4590,c_6])).

tff(c_4688,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3839,c_4198,c_4593])).

tff(c_4689,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_4690,plain,(
    k1_tarski('#skF_5') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_80,plain,
    ( k1_tarski('#skF_5') != '#skF_7'
    | k1_tarski('#skF_5') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_4758,plain,(
    '#skF_7' != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4690,c_4690,c_80])).

tff(c_5889,plain,(
    ! [A_6592,B_6593] : k5_xboole_0(k5_xboole_0(A_6592,B_6593),k2_xboole_0(A_6592,B_6593)) = k3_xboole_0(A_6592,B_6593) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_5962,plain,(
    ! [A_27] : k5_xboole_0(k1_xboole_0,k2_xboole_0(A_27,A_27)) = k3_xboole_0(A_27,A_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_5889])).

tff(c_5974,plain,(
    ! [A_6594] : k5_xboole_0(k1_xboole_0,A_6594) = A_6594 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_5962])).

tff(c_6005,plain,(
    ! [A_6594] : k5_xboole_0(A_6594,k1_xboole_0) = A_6594 ),
    inference(superposition,[status(thm),theory(equality)],[c_5974,c_2])).

tff(c_5559,plain,(
    ! [A_6573,B_6574,C_6575] : k5_xboole_0(k5_xboole_0(A_6573,B_6574),C_6575) = k5_xboole_0(A_6573,k5_xboole_0(B_6574,C_6575)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_5575,plain,(
    ! [A_6573,B_6574] : k5_xboole_0(A_6573,k5_xboole_0(B_6574,k5_xboole_0(A_6573,B_6574))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_5559,c_32])).

tff(c_5970,plain,(
    ! [A_27] : k5_xboole_0(k1_xboole_0,A_27) = A_27 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_5962])).

tff(c_5598,plain,(
    ! [A_27,C_6575] : k5_xboole_0(A_27,k5_xboole_0(A_27,C_6575)) = k5_xboole_0(k1_xboole_0,C_6575) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_5559])).

tff(c_6168,plain,(
    ! [A_6596,C_6597] : k5_xboole_0(A_6596,k5_xboole_0(A_6596,C_6597)) = C_6597 ),
    inference(demodulation,[status(thm),theory(equality)],[c_5970,c_5598])).

tff(c_6224,plain,(
    ! [B_6574,A_6573] : k5_xboole_0(B_6574,k5_xboole_0(A_6573,B_6574)) = k5_xboole_0(A_6573,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_5575,c_6168])).

tff(c_6273,plain,(
    ! [B_6602,A_6603] : k5_xboole_0(B_6602,k5_xboole_0(A_6603,B_6602)) = A_6603 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6005,c_6224])).

tff(c_6258,plain,(
    ! [B_6574,A_6573] : k5_xboole_0(B_6574,k5_xboole_0(A_6573,B_6574)) = A_6573 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6005,c_6224])).

tff(c_6276,plain,(
    ! [A_6603,B_6602] : k5_xboole_0(k5_xboole_0(A_6603,B_6602),A_6603) = B_6602 ),
    inference(superposition,[status(thm),theory(equality)],[c_6273,c_6258])).

tff(c_4697,plain,(
    k2_xboole_0('#skF_6','#skF_7') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4690,c_82])).

tff(c_5959,plain,(
    k5_xboole_0(k5_xboole_0('#skF_6','#skF_7'),'#skF_6') = k3_xboole_0('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_4697,c_5889])).

tff(c_6503,plain,(
    k3_xboole_0('#skF_6','#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6276,c_5959])).

tff(c_5031,plain,(
    ! [B_6527,A_6528] :
      ( k1_tarski(B_6527) = A_6528
      | k1_xboole_0 = A_6528
      | ~ r1_tarski(A_6528,k1_tarski(B_6527)) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_5042,plain,(
    ! [A_6528] :
      ( k1_tarski('#skF_5') = A_6528
      | k1_xboole_0 = A_6528
      | ~ r1_tarski(A_6528,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4690,c_5031])).

tff(c_5057,plain,(
    ! [A_6529] :
      ( A_6529 = '#skF_6'
      | k1_xboole_0 = A_6529
      | ~ r1_tarski(A_6529,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4690,c_5042])).

tff(c_5074,plain,(
    ! [B_21] :
      ( k3_xboole_0('#skF_6',B_21) = '#skF_6'
      | k3_xboole_0('#skF_6',B_21) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_26,c_5057])).

tff(c_6631,plain,
    ( k3_xboole_0('#skF_6','#skF_7') = '#skF_6'
    | k1_xboole_0 = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_6503,c_5074])).

tff(c_6643,plain,
    ( '#skF_7' = '#skF_6'
    | k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6503,c_6631])).

tff(c_6645,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4689,c_4758,c_6643])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:07:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.92/2.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.92/2.20  
% 5.92/2.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.92/2.20  %$ r2_hidden > r1_tarski > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2
% 5.92/2.20  
% 5.92/2.20  %Foreground sorts:
% 5.92/2.20  
% 5.92/2.20  
% 5.92/2.20  %Background operators:
% 5.92/2.20  
% 5.92/2.20  
% 5.92/2.20  %Foreground operators:
% 5.92/2.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.92/2.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.92/2.20  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.92/2.20  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.92/2.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.92/2.20  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.92/2.20  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 5.92/2.20  tff('#skF_7', type, '#skF_7': $i).
% 5.92/2.20  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.92/2.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.92/2.20  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.92/2.20  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.92/2.20  tff('#skF_5', type, '#skF_5': $i).
% 5.92/2.20  tff('#skF_6', type, '#skF_6': $i).
% 5.92/2.20  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.92/2.20  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.92/2.20  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.92/2.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.92/2.20  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.92/2.20  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 5.92/2.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.92/2.20  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.92/2.20  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.92/2.20  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.92/2.20  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.92/2.20  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.92/2.20  
% 5.92/2.22  tff(f_114, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 5.92/2.22  tff(f_58, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 5.92/2.22  tff(f_50, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.92/2.22  tff(f_40, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 5.92/2.22  tff(f_75, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 5.92/2.22  tff(f_73, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 5.92/2.22  tff(f_93, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 5.92/2.22  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 5.92/2.22  tff(f_44, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 5.92/2.22  tff(f_42, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 5.92/2.22  tff(f_62, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 5.92/2.22  tff(f_64, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 5.92/2.22  tff(f_60, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 5.92/2.22  tff(f_33, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 5.92/2.22  tff(f_56, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 5.92/2.22  tff(c_76, plain, (k1_xboole_0!='#skF_7' | k1_tarski('#skF_5')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.92/2.22  tff(c_112, plain, (k1_tarski('#skF_5')!='#skF_6'), inference(splitLeft, [status(thm)], [c_76])).
% 5.92/2.22  tff(c_82, plain, (k2_xboole_0('#skF_6', '#skF_7')=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.92/2.22  tff(c_28, plain, (![A_22, B_23]: (r1_tarski(A_22, k2_xboole_0(A_22, B_23)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.92/2.22  tff(c_738, plain, (![B_166, A_167]: (B_166=A_167 | ~r1_tarski(B_166, A_167) | ~r1_tarski(A_167, B_166))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.92/2.22  tff(c_3646, plain, (![A_312, B_313]: (k2_xboole_0(A_312, B_313)=A_312 | ~r1_tarski(k2_xboole_0(A_312, B_313), A_312))), inference(resolution, [status(thm)], [c_28, c_738])).
% 5.92/2.22  tff(c_3665, plain, (k2_xboole_0('#skF_6', '#skF_7')='#skF_6' | ~r1_tarski(k1_tarski('#skF_5'), '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_82, c_3646])).
% 5.92/2.22  tff(c_3673, plain, (k1_tarski('#skF_5')='#skF_6' | ~r1_tarski(k1_tarski('#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_3665])).
% 5.92/2.22  tff(c_3674, plain, (~r1_tarski(k1_tarski('#skF_5'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_112, c_3673])).
% 5.92/2.22  tff(c_12, plain, (![A_7, B_8]: (r2_hidden('#skF_2'(A_7, B_8), A_7) | r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.92/2.22  tff(c_54, plain, (![A_36]: (k2_tarski(A_36, A_36)=k1_tarski(A_36))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.92/2.22  tff(c_888, plain, (![D_193, B_194, A_195]: (D_193=B_194 | D_193=A_195 | ~r2_hidden(D_193, k2_tarski(A_195, B_194)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.92/2.22  tff(c_1035, plain, (![D_215, A_216]: (D_215=A_216 | D_215=A_216 | ~r2_hidden(D_215, k1_tarski(A_216)))), inference(superposition, [status(thm), theory('equality')], [c_54, c_888])).
% 5.92/2.22  tff(c_3789, plain, (![A_315, B_316]: ('#skF_2'(k1_tarski(A_315), B_316)=A_315 | r1_tarski(k1_tarski(A_315), B_316))), inference(resolution, [status(thm)], [c_12, c_1035])).
% 5.92/2.22  tff(c_3819, plain, ('#skF_2'(k1_tarski('#skF_5'), '#skF_6')='#skF_5'), inference(resolution, [status(thm)], [c_3789, c_3674])).
% 5.92/2.22  tff(c_10, plain, (![A_7, B_8]: (~r2_hidden('#skF_2'(A_7, B_8), B_8) | r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.92/2.22  tff(c_3833, plain, (~r2_hidden('#skF_5', '#skF_6') | r1_tarski(k1_tarski('#skF_5'), '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_3819, c_10])).
% 5.92/2.22  tff(c_3839, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_3674, c_3833])).
% 5.92/2.22  tff(c_78, plain, (k1_tarski('#skF_5')!='#skF_7' | k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.92/2.22  tff(c_126, plain, (k1_xboole_0!='#skF_6'), inference(splitLeft, [status(thm)], [c_78])).
% 5.92/2.22  tff(c_150, plain, (![A_81, B_82]: (r1_tarski(A_81, k2_xboole_0(A_81, B_82)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.92/2.22  tff(c_153, plain, (r1_tarski('#skF_6', k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_82, c_150])).
% 5.92/2.22  tff(c_539, plain, (![B_137, A_138]: (k1_tarski(B_137)=A_138 | k1_xboole_0=A_138 | ~r1_tarski(A_138, k1_tarski(B_137)))), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.92/2.22  tff(c_550, plain, (k1_tarski('#skF_5')='#skF_6' | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_153, c_539])).
% 5.92/2.22  tff(c_563, plain, $false, inference(negUnitSimplification, [status(thm)], [c_126, c_112, c_550])).
% 5.92/2.22  tff(c_564, plain, (k1_tarski('#skF_5')!='#skF_7'), inference(splitRight, [status(thm)], [c_78])).
% 5.92/2.22  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.92/2.22  tff(c_16, plain, (![A_14]: (k3_xboole_0(A_14, A_14)=A_14)), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.92/2.22  tff(c_14, plain, (![A_12]: (k2_xboole_0(A_12, A_12)=A_12)), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.92/2.22  tff(c_565, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_78])).
% 5.92/2.22  tff(c_32, plain, (![A_27]: (k5_xboole_0(A_27, A_27)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.92/2.22  tff(c_566, plain, (![A_27]: (k5_xboole_0(A_27, A_27)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_565, c_32])).
% 5.92/2.22  tff(c_1053, plain, (![A_217, B_218]: (k5_xboole_0(k5_xboole_0(A_217, B_218), k2_xboole_0(A_217, B_218))=k3_xboole_0(A_217, B_218))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.92/2.22  tff(c_1098, plain, (![A_27]: (k5_xboole_0('#skF_6', k2_xboole_0(A_27, A_27))=k3_xboole_0(A_27, A_27))), inference(superposition, [status(thm), theory('equality')], [c_566, c_1053])).
% 5.92/2.22  tff(c_1105, plain, (![A_27]: (k5_xboole_0('#skF_6', A_27)=A_27)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_14, c_1098])).
% 5.92/2.22  tff(c_1239, plain, (![A_225, B_226, C_227]: (k5_xboole_0(k5_xboole_0(A_225, B_226), C_227)=k5_xboole_0(A_225, k5_xboole_0(B_226, C_227)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.92/2.22  tff(c_1308, plain, (![A_27, C_227]: (k5_xboole_0(A_27, k5_xboole_0(A_27, C_227))=k5_xboole_0('#skF_6', C_227))), inference(superposition, [status(thm), theory('equality')], [c_566, c_1239])).
% 5.92/2.22  tff(c_1322, plain, (![A_228, C_229]: (k5_xboole_0(A_228, k5_xboole_0(A_228, C_229))=C_229)), inference(demodulation, [status(thm), theory('equality')], [c_1105, c_1308])).
% 5.92/2.22  tff(c_1374, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k5_xboole_0(B_2, A_1))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_1322])).
% 5.92/2.22  tff(c_72, plain, (![B_65]: (r1_tarski(k1_xboole_0, k1_tarski(B_65)))), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.92/2.22  tff(c_567, plain, (![B_65]: (r1_tarski('#skF_6', k1_tarski(B_65)))), inference(demodulation, [status(thm), theory('equality')], [c_565, c_72])).
% 5.92/2.22  tff(c_6, plain, (![A_3]: (v1_xboole_0(A_3) | r2_hidden('#skF_1'(A_3), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.92/2.22  tff(c_872, plain, (![C_190, B_191, A_192]: (r2_hidden(C_190, B_191) | ~r2_hidden(C_190, A_192) | ~r1_tarski(A_192, B_191))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.92/2.22  tff(c_3422, plain, (![A_292, B_293]: (r2_hidden('#skF_1'(A_292), B_293) | ~r1_tarski(A_292, B_293) | v1_xboole_0(A_292))), inference(resolution, [status(thm)], [c_6, c_872])).
% 5.92/2.22  tff(c_905, plain, (![D_193, A_36]: (D_193=A_36 | D_193=A_36 | ~r2_hidden(D_193, k1_tarski(A_36)))), inference(superposition, [status(thm), theory('equality')], [c_54, c_888])).
% 5.92/2.22  tff(c_3947, plain, (![A_325, A_326]: (A_325='#skF_1'(A_326) | ~r1_tarski(A_326, k1_tarski(A_325)) | v1_xboole_0(A_326))), inference(resolution, [status(thm)], [c_3422, c_905])).
% 5.92/2.22  tff(c_3977, plain, (![B_65]: (B_65='#skF_1'('#skF_6') | v1_xboole_0('#skF_6'))), inference(resolution, [status(thm)], [c_567, c_3947])).
% 5.92/2.22  tff(c_3981, plain, (v1_xboole_0('#skF_6')), inference(splitLeft, [status(thm)], [c_3977])).
% 5.92/2.22  tff(c_26, plain, (![A_20, B_21]: (r1_tarski(k3_xboole_0(A_20, B_21), A_20))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.92/2.22  tff(c_755, plain, (![A_169, B_170]: (r2_hidden('#skF_2'(A_169, B_170), A_169) | r1_tarski(A_169, B_170))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.92/2.22  tff(c_4, plain, (![B_6, A_3]: (~r2_hidden(B_6, A_3) | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.92/2.22  tff(c_767, plain, (![A_173, B_174]: (~v1_xboole_0(A_173) | r1_tarski(A_173, B_174))), inference(resolution, [status(thm)], [c_755, c_4])).
% 5.92/2.22  tff(c_18, plain, (![B_17, A_16]: (B_17=A_16 | ~r1_tarski(B_17, A_16) | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.92/2.22  tff(c_780, plain, (![B_177, A_178]: (B_177=A_178 | ~r1_tarski(B_177, A_178) | ~v1_xboole_0(A_178))), inference(resolution, [status(thm)], [c_767, c_18])).
% 5.92/2.22  tff(c_797, plain, (![A_20, B_21]: (k3_xboole_0(A_20, B_21)=A_20 | ~v1_xboole_0(A_20))), inference(resolution, [status(thm)], [c_26, c_780])).
% 5.92/2.22  tff(c_4160, plain, (![B_21]: (k3_xboole_0('#skF_6', B_21)='#skF_6')), inference(resolution, [status(thm)], [c_3981, c_797])).
% 5.92/2.22  tff(c_1095, plain, (k5_xboole_0(k5_xboole_0('#skF_6', '#skF_7'), k1_tarski('#skF_5'))=k3_xboole_0('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_82, c_1053])).
% 5.92/2.22  tff(c_1158, plain, (k5_xboole_0('#skF_7', k1_tarski('#skF_5'))=k3_xboole_0('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1105, c_1095])).
% 5.92/2.22  tff(c_1921, plain, (![C_248]: (k5_xboole_0('#skF_7', k5_xboole_0(k1_tarski('#skF_5'), C_248))=k5_xboole_0(k3_xboole_0('#skF_6', '#skF_7'), C_248))), inference(superposition, [status(thm), theory('equality')], [c_1158, c_1239])).
% 5.92/2.22  tff(c_1933, plain, (![C_248]: (k5_xboole_0(k5_xboole_0(k1_tarski('#skF_5'), C_248), k5_xboole_0(k3_xboole_0('#skF_6', '#skF_7'), C_248))='#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_1921, c_1374])).
% 5.92/2.22  tff(c_4172, plain, (![C_248]: (k5_xboole_0(k5_xboole_0(k1_tarski('#skF_5'), C_248), k5_xboole_0('#skF_6', C_248))='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_4160, c_1933])).
% 5.92/2.22  tff(c_4194, plain, (k1_tarski('#skF_5')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_1374, c_2, c_1105, c_4172])).
% 5.92/2.22  tff(c_4196, plain, $false, inference(negUnitSimplification, [status(thm)], [c_564, c_4194])).
% 5.92/2.22  tff(c_4198, plain, (~v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_3977])).
% 5.92/2.22  tff(c_4590, plain, ('#skF_1'('#skF_6')='#skF_5'), inference(splitRight, [status(thm)], [c_3977])).
% 5.92/2.22  tff(c_4593, plain, (v1_xboole_0('#skF_6') | r2_hidden('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_4590, c_6])).
% 5.92/2.22  tff(c_4688, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3839, c_4198, c_4593])).
% 5.92/2.22  tff(c_4689, plain, (k1_xboole_0!='#skF_7'), inference(splitRight, [status(thm)], [c_76])).
% 5.92/2.22  tff(c_4690, plain, (k1_tarski('#skF_5')='#skF_6'), inference(splitRight, [status(thm)], [c_76])).
% 5.92/2.22  tff(c_80, plain, (k1_tarski('#skF_5')!='#skF_7' | k1_tarski('#skF_5')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.92/2.22  tff(c_4758, plain, ('#skF_7'!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_4690, c_4690, c_80])).
% 5.92/2.22  tff(c_5889, plain, (![A_6592, B_6593]: (k5_xboole_0(k5_xboole_0(A_6592, B_6593), k2_xboole_0(A_6592, B_6593))=k3_xboole_0(A_6592, B_6593))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.92/2.22  tff(c_5962, plain, (![A_27]: (k5_xboole_0(k1_xboole_0, k2_xboole_0(A_27, A_27))=k3_xboole_0(A_27, A_27))), inference(superposition, [status(thm), theory('equality')], [c_32, c_5889])).
% 5.92/2.22  tff(c_5974, plain, (![A_6594]: (k5_xboole_0(k1_xboole_0, A_6594)=A_6594)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_14, c_5962])).
% 5.92/2.22  tff(c_6005, plain, (![A_6594]: (k5_xboole_0(A_6594, k1_xboole_0)=A_6594)), inference(superposition, [status(thm), theory('equality')], [c_5974, c_2])).
% 5.92/2.22  tff(c_5559, plain, (![A_6573, B_6574, C_6575]: (k5_xboole_0(k5_xboole_0(A_6573, B_6574), C_6575)=k5_xboole_0(A_6573, k5_xboole_0(B_6574, C_6575)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.92/2.22  tff(c_5575, plain, (![A_6573, B_6574]: (k5_xboole_0(A_6573, k5_xboole_0(B_6574, k5_xboole_0(A_6573, B_6574)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_5559, c_32])).
% 5.92/2.22  tff(c_5970, plain, (![A_27]: (k5_xboole_0(k1_xboole_0, A_27)=A_27)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_14, c_5962])).
% 5.92/2.22  tff(c_5598, plain, (![A_27, C_6575]: (k5_xboole_0(A_27, k5_xboole_0(A_27, C_6575))=k5_xboole_0(k1_xboole_0, C_6575))), inference(superposition, [status(thm), theory('equality')], [c_32, c_5559])).
% 5.92/2.22  tff(c_6168, plain, (![A_6596, C_6597]: (k5_xboole_0(A_6596, k5_xboole_0(A_6596, C_6597))=C_6597)), inference(demodulation, [status(thm), theory('equality')], [c_5970, c_5598])).
% 5.92/2.22  tff(c_6224, plain, (![B_6574, A_6573]: (k5_xboole_0(B_6574, k5_xboole_0(A_6573, B_6574))=k5_xboole_0(A_6573, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_5575, c_6168])).
% 5.92/2.22  tff(c_6273, plain, (![B_6602, A_6603]: (k5_xboole_0(B_6602, k5_xboole_0(A_6603, B_6602))=A_6603)), inference(demodulation, [status(thm), theory('equality')], [c_6005, c_6224])).
% 5.92/2.22  tff(c_6258, plain, (![B_6574, A_6573]: (k5_xboole_0(B_6574, k5_xboole_0(A_6573, B_6574))=A_6573)), inference(demodulation, [status(thm), theory('equality')], [c_6005, c_6224])).
% 5.92/2.22  tff(c_6276, plain, (![A_6603, B_6602]: (k5_xboole_0(k5_xboole_0(A_6603, B_6602), A_6603)=B_6602)), inference(superposition, [status(thm), theory('equality')], [c_6273, c_6258])).
% 5.92/2.22  tff(c_4697, plain, (k2_xboole_0('#skF_6', '#skF_7')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_4690, c_82])).
% 5.92/2.22  tff(c_5959, plain, (k5_xboole_0(k5_xboole_0('#skF_6', '#skF_7'), '#skF_6')=k3_xboole_0('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_4697, c_5889])).
% 5.92/2.22  tff(c_6503, plain, (k3_xboole_0('#skF_6', '#skF_7')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_6276, c_5959])).
% 5.92/2.22  tff(c_5031, plain, (![B_6527, A_6528]: (k1_tarski(B_6527)=A_6528 | k1_xboole_0=A_6528 | ~r1_tarski(A_6528, k1_tarski(B_6527)))), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.92/2.22  tff(c_5042, plain, (![A_6528]: (k1_tarski('#skF_5')=A_6528 | k1_xboole_0=A_6528 | ~r1_tarski(A_6528, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_4690, c_5031])).
% 5.92/2.22  tff(c_5057, plain, (![A_6529]: (A_6529='#skF_6' | k1_xboole_0=A_6529 | ~r1_tarski(A_6529, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_4690, c_5042])).
% 5.92/2.22  tff(c_5074, plain, (![B_21]: (k3_xboole_0('#skF_6', B_21)='#skF_6' | k3_xboole_0('#skF_6', B_21)=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_5057])).
% 5.92/2.22  tff(c_6631, plain, (k3_xboole_0('#skF_6', '#skF_7')='#skF_6' | k1_xboole_0='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_6503, c_5074])).
% 5.92/2.22  tff(c_6643, plain, ('#skF_7'='#skF_6' | k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_6503, c_6631])).
% 5.92/2.22  tff(c_6645, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4689, c_4758, c_6643])).
% 5.92/2.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.92/2.22  
% 5.92/2.22  Inference rules
% 5.92/2.22  ----------------------
% 5.92/2.22  #Ref     : 0
% 5.92/2.22  #Sup     : 1649
% 5.92/2.22  #Fact    : 1
% 5.92/2.22  #Define  : 0
% 5.92/2.22  #Split   : 4
% 5.92/2.22  #Chain   : 0
% 5.92/2.22  #Close   : 0
% 5.92/2.22  
% 5.92/2.22  Ordering : KBO
% 5.92/2.22  
% 5.92/2.22  Simplification rules
% 5.92/2.22  ----------------------
% 5.92/2.22  #Subsume      : 172
% 5.92/2.22  #Demod        : 946
% 5.92/2.22  #Tautology    : 869
% 5.92/2.22  #SimpNegUnit  : 51
% 5.92/2.22  #BackRed      : 26
% 5.92/2.22  
% 5.92/2.22  #Partial instantiations: 936
% 5.92/2.22  #Strategies tried      : 1
% 5.92/2.22  
% 5.92/2.22  Timing (in seconds)
% 5.92/2.22  ----------------------
% 5.92/2.22  Preprocessing        : 0.34
% 5.92/2.23  Parsing              : 0.17
% 5.92/2.23  CNF conversion       : 0.03
% 5.92/2.23  Main loop            : 1.09
% 5.92/2.23  Inferencing          : 0.38
% 5.92/2.23  Reduction            : 0.43
% 5.92/2.23  Demodulation         : 0.34
% 5.92/2.23  BG Simplification    : 0.04
% 5.92/2.23  Subsumption          : 0.17
% 5.92/2.23  Abstraction          : 0.05
% 5.92/2.23  MUC search           : 0.00
% 5.92/2.23  Cooper               : 0.00
% 5.92/2.23  Total                : 1.49
% 5.92/2.23  Index Insertion      : 0.00
% 5.92/2.23  Index Deletion       : 0.00
% 5.92/2.23  Index Matching       : 0.00
% 5.92/2.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
