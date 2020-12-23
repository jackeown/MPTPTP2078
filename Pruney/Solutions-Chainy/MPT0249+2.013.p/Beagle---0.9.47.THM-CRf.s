%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:25 EST 2020

% Result     : Theorem 6.08s
% Output     : CNFRefutation 6.41s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 502 expanded)
%              Number of leaves         :   44 ( 190 expanded)
%              Depth                    :   16
%              Number of atoms          :  152 ( 744 expanded)
%              Number of equality atoms :   52 ( 425 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_8 > #skF_2 > #skF_5 > #skF_4

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

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

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_118,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & B != C
          & B != k1_xboole_0
          & C != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).

tff(f_76,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_46,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_78,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_74,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_103,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_72,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_85,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_62,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_70,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(c_74,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_78,plain,(
    '#skF_7' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_38,plain,(
    ! [A_32] : k5_xboole_0(A_32,A_32) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_20,plain,(
    ! [A_16] : k3_xboole_0(A_16,A_16) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_18,plain,(
    ! [A_14] : k2_xboole_0(A_14,A_14) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_4903,plain,(
    ! [A_402,B_403] : k5_xboole_0(k5_xboole_0(A_402,B_403),k2_xboole_0(A_402,B_403)) = k3_xboole_0(A_402,B_403) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_4961,plain,(
    ! [A_14] : k5_xboole_0(k5_xboole_0(A_14,A_14),A_14) = k3_xboole_0(A_14,A_14) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_4903])).

tff(c_4970,plain,(
    ! [A_404] : k5_xboole_0(k1_xboole_0,A_404) = A_404 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_20,c_4961])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_5001,plain,(
    ! [A_404] : k5_xboole_0(A_404,k1_xboole_0) = A_404 ),
    inference(superposition,[status(thm),theory(equality)],[c_4970,c_2])).

tff(c_36,plain,(
    ! [A_29,B_30,C_31] : k5_xboole_0(k5_xboole_0(A_29,B_30),C_31) = k5_xboole_0(A_29,k5_xboole_0(B_30,C_31)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_70,plain,(
    ! [A_68,B_69] :
      ( r1_tarski(k1_tarski(A_68),B_69)
      | ~ r2_hidden(A_68,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_80,plain,(
    k2_xboole_0('#skF_7','#skF_8') = k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_133,plain,(
    ! [A_83,B_84] : r1_tarski(A_83,k2_xboole_0(A_83,B_84)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_136,plain,(
    r1_tarski('#skF_7',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_133])).

tff(c_275,plain,(
    ! [B_108,A_109] :
      ( B_108 = A_109
      | ~ r1_tarski(B_108,A_109)
      | ~ r1_tarski(A_109,B_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_287,plain,
    ( k1_tarski('#skF_6') = '#skF_7'
    | ~ r1_tarski(k1_tarski('#skF_6'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_136,c_275])).

tff(c_294,plain,(
    ~ r1_tarski(k1_tarski('#skF_6'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_287])).

tff(c_298,plain,(
    ~ r2_hidden('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_70,c_294])).

tff(c_76,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_6,plain,(
    ! [A_3] :
      ( v1_xboole_0(A_3)
      | r2_hidden('#skF_1'(A_3),A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_368,plain,(
    ! [C_124,B_125,A_126] :
      ( r2_hidden(C_124,B_125)
      | ~ r2_hidden(C_124,A_126)
      | ~ r1_tarski(A_126,B_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2545,plain,(
    ! [A_238,B_239] :
      ( r2_hidden('#skF_1'(A_238),B_239)
      | ~ r1_tarski(A_238,B_239)
      | v1_xboole_0(A_238) ) ),
    inference(resolution,[status(thm)],[c_6,c_368])).

tff(c_42,plain,(
    ! [C_39,A_35] :
      ( C_39 = A_35
      | ~ r2_hidden(C_39,k1_tarski(A_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_3717,plain,(
    ! [A_309,A_310] :
      ( A_309 = '#skF_1'(A_310)
      | ~ r1_tarski(A_310,k1_tarski(A_309))
      | v1_xboole_0(A_310) ) ),
    inference(resolution,[status(thm)],[c_2545,c_42])).

tff(c_3768,plain,
    ( '#skF_1'('#skF_7') = '#skF_6'
    | v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_136,c_3717])).

tff(c_3773,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_3768])).

tff(c_467,plain,(
    ! [A_142,B_143] :
      ( r2_hidden('#skF_3'(A_142,B_143),k3_xboole_0(A_142,B_143))
      | r1_xboole_0(A_142,B_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_4,plain,(
    ! [B_6,A_3] :
      ( ~ r2_hidden(B_6,A_3)
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_707,plain,(
    ! [A_157,B_158] :
      ( ~ v1_xboole_0(k3_xboole_0(A_157,B_158))
      | r1_xboole_0(A_157,B_158) ) ),
    inference(resolution,[status(thm)],[c_467,c_4])).

tff(c_818,plain,(
    ! [A_162] :
      ( ~ v1_xboole_0(A_162)
      | r1_xboole_0(A_162,A_162) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_707])).

tff(c_14,plain,(
    ! [A_12,B_13] :
      ( k3_xboole_0(A_12,B_13) = k1_xboole_0
      | ~ r1_xboole_0(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_826,plain,(
    ! [A_162] :
      ( k3_xboole_0(A_162,A_162) = k1_xboole_0
      | ~ v1_xboole_0(A_162) ) ),
    inference(resolution,[status(thm)],[c_818,c_14])).

tff(c_830,plain,(
    ! [A_162] :
      ( k1_xboole_0 = A_162
      | ~ v1_xboole_0(A_162) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_826])).

tff(c_3786,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_3773,c_830])).

tff(c_3801,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_3786])).

tff(c_3803,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_3768])).

tff(c_3802,plain,(
    '#skF_1'('#skF_7') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_3768])).

tff(c_3814,plain,
    ( v1_xboole_0('#skF_7')
    | r2_hidden('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_3802,c_6])).

tff(c_3819,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_298,c_3803,c_3814])).

tff(c_3820,plain,(
    k1_tarski('#skF_6') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_287])).

tff(c_3832,plain,(
    k2_xboole_0('#skF_7','#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3820,c_80])).

tff(c_4946,plain,(
    k5_xboole_0(k5_xboole_0('#skF_7','#skF_8'),'#skF_7') = k3_xboole_0('#skF_7','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_3832,c_4903])).

tff(c_4967,plain,(
    k5_xboole_0('#skF_8',k1_xboole_0) = k3_xboole_0('#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_2,c_4946])).

tff(c_5116,plain,(
    k3_xboole_0('#skF_7','#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5001,c_4967])).

tff(c_32,plain,(
    ! [A_25,B_26] : r1_tarski(k3_xboole_0(A_25,B_26),A_25) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_5141,plain,(
    r1_tarski('#skF_8','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_5116,c_32])).

tff(c_26,plain,(
    ! [B_24,A_23] :
      ( B_24 = A_23
      | ~ r1_tarski(B_24,A_23)
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_5157,plain,
    ( '#skF_7' = '#skF_8'
    | ~ r1_tarski('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_5141,c_26])).

tff(c_5164,plain,(
    ~ r1_tarski('#skF_7','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_5157])).

tff(c_4002,plain,(
    ! [A_327,B_328] :
      ( r2_hidden('#skF_2'(A_327,B_328),A_327)
      | r1_tarski(A_327,B_328) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_3854,plain,(
    ! [C_39] :
      ( C_39 = '#skF_6'
      | ~ r2_hidden(C_39,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3820,c_42])).

tff(c_4026,plain,(
    ! [B_328] :
      ( '#skF_2'('#skF_7',B_328) = '#skF_6'
      | r1_tarski('#skF_7',B_328) ) ),
    inference(resolution,[status(thm)],[c_4002,c_3854])).

tff(c_5174,plain,(
    '#skF_2'('#skF_7','#skF_8') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_4026,c_5164])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( ~ r2_hidden('#skF_2'(A_7,B_8),B_8)
      | r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_5190,plain,
    ( ~ r2_hidden('#skF_6','#skF_8')
    | r1_tarski('#skF_7','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_5174,c_10])).

tff(c_5198,plain,(
    ~ r2_hidden('#skF_6','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_5164,c_5190])).

tff(c_3822,plain,(
    ! [A_311,B_312,C_313] :
      ( ~ r1_xboole_0(A_311,B_312)
      | ~ r2_hidden(C_313,k3_xboole_0(A_311,B_312)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_3830,plain,(
    ! [A_311,B_312] :
      ( ~ r1_xboole_0(A_311,B_312)
      | v1_xboole_0(k3_xboole_0(A_311,B_312)) ) ),
    inference(resolution,[status(thm)],[c_6,c_3822])).

tff(c_5135,plain,
    ( ~ r1_xboole_0('#skF_7','#skF_8')
    | v1_xboole_0('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_5116,c_3830])).

tff(c_5205,plain,(
    ~ r1_xboole_0('#skF_7','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_5135])).

tff(c_22,plain,(
    ! [A_18,B_19] :
      ( r2_hidden('#skF_3'(A_18,B_19),k3_xboole_0(A_18,B_19))
      | r1_xboole_0(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_5123,plain,
    ( r2_hidden('#skF_3'('#skF_7','#skF_8'),'#skF_8')
    | r1_xboole_0('#skF_7','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_5116,c_22])).

tff(c_5272,plain,(
    r2_hidden('#skF_3'('#skF_7','#skF_8'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_5205,c_5123])).

tff(c_8,plain,(
    ! [C_11,B_8,A_7] :
      ( r2_hidden(C_11,B_8)
      | ~ r2_hidden(C_11,A_7)
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_6854,plain,(
    ! [B_468] :
      ( r2_hidden('#skF_3'('#skF_7','#skF_8'),B_468)
      | ~ r1_tarski('#skF_8',B_468) ) ),
    inference(resolution,[status(thm)],[c_5272,c_8])).

tff(c_6863,plain,
    ( '#skF_3'('#skF_7','#skF_8') = '#skF_6'
    | ~ r1_tarski('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_6854,c_3854])).

tff(c_6879,plain,(
    '#skF_3'('#skF_7','#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5141,c_6863])).

tff(c_6893,plain,(
    r2_hidden('#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6879,c_5272])).

tff(c_6895,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5198,c_6893])).

tff(c_6896,plain,(
    v1_xboole_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_5135])).

tff(c_4425,plain,(
    ! [A_374,B_375] :
      ( r2_hidden('#skF_3'(A_374,B_375),k3_xboole_0(A_374,B_375))
      | r1_xboole_0(A_374,B_375) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_4447,plain,(
    ! [A_376,B_377] :
      ( ~ v1_xboole_0(k3_xboole_0(A_376,B_377))
      | r1_xboole_0(A_376,B_377) ) ),
    inference(resolution,[status(thm)],[c_4425,c_4])).

tff(c_4462,plain,(
    ! [A_378] :
      ( ~ v1_xboole_0(A_378)
      | r1_xboole_0(A_378,A_378) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_4447])).

tff(c_4475,plain,(
    ! [A_378] :
      ( k3_xboole_0(A_378,A_378) = k1_xboole_0
      | ~ v1_xboole_0(A_378) ) ),
    inference(resolution,[status(thm)],[c_4462,c_14])).

tff(c_4481,plain,(
    ! [A_378] :
      ( k1_xboole_0 = A_378
      | ~ v1_xboole_0(A_378) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_4475])).

tff(c_6900,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_6896,c_4481])).

tff(c_6913,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_6900])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 10:17:12 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.08/2.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.08/2.28  
% 6.08/2.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.08/2.29  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_8 > #skF_2 > #skF_5 > #skF_4
% 6.08/2.29  
% 6.08/2.29  %Foreground sorts:
% 6.08/2.29  
% 6.08/2.29  
% 6.08/2.29  %Background operators:
% 6.08/2.29  
% 6.08/2.29  
% 6.08/2.29  %Foreground operators:
% 6.08/2.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.08/2.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.08/2.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.08/2.29  tff('#skF_1', type, '#skF_1': $i > $i).
% 6.08/2.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.08/2.29  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.08/2.29  tff('#skF_7', type, '#skF_7': $i).
% 6.08/2.29  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.08/2.29  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 6.08/2.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.08/2.29  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.08/2.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.08/2.29  tff('#skF_6', type, '#skF_6': $i).
% 6.08/2.29  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.08/2.29  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.08/2.29  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.08/2.29  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.08/2.29  tff('#skF_8', type, '#skF_8': $i).
% 6.08/2.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.08/2.29  tff(k3_tarski, type, k3_tarski: $i > $i).
% 6.08/2.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.08/2.29  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.08/2.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.08/2.29  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.08/2.29  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.08/2.29  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.08/2.29  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 6.08/2.29  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 6.08/2.29  
% 6.41/2.32  tff(f_118, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~(B = C)) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 6.41/2.32  tff(f_76, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 6.41/2.32  tff(f_48, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 6.41/2.32  tff(f_46, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 6.41/2.32  tff(f_78, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 6.41/2.32  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 6.41/2.32  tff(f_74, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 6.41/2.32  tff(f_103, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 6.41/2.32  tff(f_72, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 6.41/2.32  tff(f_68, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.41/2.32  tff(f_33, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 6.41/2.32  tff(f_40, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 6.41/2.32  tff(f_85, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 6.41/2.32  tff(f_62, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 6.41/2.32  tff(f_44, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 6.41/2.32  tff(f_70, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 6.41/2.32  tff(c_74, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_118])).
% 6.41/2.32  tff(c_78, plain, ('#skF_7'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_118])).
% 6.41/2.32  tff(c_38, plain, (![A_32]: (k5_xboole_0(A_32, A_32)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.41/2.32  tff(c_20, plain, (![A_16]: (k3_xboole_0(A_16, A_16)=A_16)), inference(cnfTransformation, [status(thm)], [f_48])).
% 6.41/2.32  tff(c_18, plain, (![A_14]: (k2_xboole_0(A_14, A_14)=A_14)), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.41/2.32  tff(c_4903, plain, (![A_402, B_403]: (k5_xboole_0(k5_xboole_0(A_402, B_403), k2_xboole_0(A_402, B_403))=k3_xboole_0(A_402, B_403))), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.41/2.32  tff(c_4961, plain, (![A_14]: (k5_xboole_0(k5_xboole_0(A_14, A_14), A_14)=k3_xboole_0(A_14, A_14))), inference(superposition, [status(thm), theory('equality')], [c_18, c_4903])).
% 6.41/2.32  tff(c_4970, plain, (![A_404]: (k5_xboole_0(k1_xboole_0, A_404)=A_404)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_20, c_4961])).
% 6.41/2.32  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.41/2.32  tff(c_5001, plain, (![A_404]: (k5_xboole_0(A_404, k1_xboole_0)=A_404)), inference(superposition, [status(thm), theory('equality')], [c_4970, c_2])).
% 6.41/2.32  tff(c_36, plain, (![A_29, B_30, C_31]: (k5_xboole_0(k5_xboole_0(A_29, B_30), C_31)=k5_xboole_0(A_29, k5_xboole_0(B_30, C_31)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.41/2.32  tff(c_70, plain, (![A_68, B_69]: (r1_tarski(k1_tarski(A_68), B_69) | ~r2_hidden(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.41/2.32  tff(c_80, plain, (k2_xboole_0('#skF_7', '#skF_8')=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_118])).
% 6.41/2.32  tff(c_133, plain, (![A_83, B_84]: (r1_tarski(A_83, k2_xboole_0(A_83, B_84)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.41/2.32  tff(c_136, plain, (r1_tarski('#skF_7', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_80, c_133])).
% 6.41/2.32  tff(c_275, plain, (![B_108, A_109]: (B_108=A_109 | ~r1_tarski(B_108, A_109) | ~r1_tarski(A_109, B_108))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.41/2.32  tff(c_287, plain, (k1_tarski('#skF_6')='#skF_7' | ~r1_tarski(k1_tarski('#skF_6'), '#skF_7')), inference(resolution, [status(thm)], [c_136, c_275])).
% 6.41/2.32  tff(c_294, plain, (~r1_tarski(k1_tarski('#skF_6'), '#skF_7')), inference(splitLeft, [status(thm)], [c_287])).
% 6.41/2.32  tff(c_298, plain, (~r2_hidden('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_70, c_294])).
% 6.41/2.32  tff(c_76, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_118])).
% 6.41/2.32  tff(c_6, plain, (![A_3]: (v1_xboole_0(A_3) | r2_hidden('#skF_1'(A_3), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.41/2.32  tff(c_368, plain, (![C_124, B_125, A_126]: (r2_hidden(C_124, B_125) | ~r2_hidden(C_124, A_126) | ~r1_tarski(A_126, B_125))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.41/2.32  tff(c_2545, plain, (![A_238, B_239]: (r2_hidden('#skF_1'(A_238), B_239) | ~r1_tarski(A_238, B_239) | v1_xboole_0(A_238))), inference(resolution, [status(thm)], [c_6, c_368])).
% 6.41/2.32  tff(c_42, plain, (![C_39, A_35]: (C_39=A_35 | ~r2_hidden(C_39, k1_tarski(A_35)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.41/2.32  tff(c_3717, plain, (![A_309, A_310]: (A_309='#skF_1'(A_310) | ~r1_tarski(A_310, k1_tarski(A_309)) | v1_xboole_0(A_310))), inference(resolution, [status(thm)], [c_2545, c_42])).
% 6.41/2.32  tff(c_3768, plain, ('#skF_1'('#skF_7')='#skF_6' | v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_136, c_3717])).
% 6.41/2.32  tff(c_3773, plain, (v1_xboole_0('#skF_7')), inference(splitLeft, [status(thm)], [c_3768])).
% 6.41/2.32  tff(c_467, plain, (![A_142, B_143]: (r2_hidden('#skF_3'(A_142, B_143), k3_xboole_0(A_142, B_143)) | r1_xboole_0(A_142, B_143))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.41/2.32  tff(c_4, plain, (![B_6, A_3]: (~r2_hidden(B_6, A_3) | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.41/2.32  tff(c_707, plain, (![A_157, B_158]: (~v1_xboole_0(k3_xboole_0(A_157, B_158)) | r1_xboole_0(A_157, B_158))), inference(resolution, [status(thm)], [c_467, c_4])).
% 6.41/2.32  tff(c_818, plain, (![A_162]: (~v1_xboole_0(A_162) | r1_xboole_0(A_162, A_162))), inference(superposition, [status(thm), theory('equality')], [c_20, c_707])).
% 6.41/2.32  tff(c_14, plain, (![A_12, B_13]: (k3_xboole_0(A_12, B_13)=k1_xboole_0 | ~r1_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.41/2.32  tff(c_826, plain, (![A_162]: (k3_xboole_0(A_162, A_162)=k1_xboole_0 | ~v1_xboole_0(A_162))), inference(resolution, [status(thm)], [c_818, c_14])).
% 6.41/2.32  tff(c_830, plain, (![A_162]: (k1_xboole_0=A_162 | ~v1_xboole_0(A_162))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_826])).
% 6.41/2.32  tff(c_3786, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_3773, c_830])).
% 6.41/2.32  tff(c_3801, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_3786])).
% 6.41/2.32  tff(c_3803, plain, (~v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_3768])).
% 6.41/2.32  tff(c_3802, plain, ('#skF_1'('#skF_7')='#skF_6'), inference(splitRight, [status(thm)], [c_3768])).
% 6.41/2.32  tff(c_3814, plain, (v1_xboole_0('#skF_7') | r2_hidden('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_3802, c_6])).
% 6.41/2.32  tff(c_3819, plain, $false, inference(negUnitSimplification, [status(thm)], [c_298, c_3803, c_3814])).
% 6.41/2.32  tff(c_3820, plain, (k1_tarski('#skF_6')='#skF_7'), inference(splitRight, [status(thm)], [c_287])).
% 6.41/2.32  tff(c_3832, plain, (k2_xboole_0('#skF_7', '#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_3820, c_80])).
% 6.41/2.32  tff(c_4946, plain, (k5_xboole_0(k5_xboole_0('#skF_7', '#skF_8'), '#skF_7')=k3_xboole_0('#skF_7', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_3832, c_4903])).
% 6.41/2.32  tff(c_4967, plain, (k5_xboole_0('#skF_8', k1_xboole_0)=k3_xboole_0('#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_2, c_4946])).
% 6.41/2.32  tff(c_5116, plain, (k3_xboole_0('#skF_7', '#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_5001, c_4967])).
% 6.41/2.32  tff(c_32, plain, (![A_25, B_26]: (r1_tarski(k3_xboole_0(A_25, B_26), A_25))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.41/2.32  tff(c_5141, plain, (r1_tarski('#skF_8', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_5116, c_32])).
% 6.41/2.32  tff(c_26, plain, (![B_24, A_23]: (B_24=A_23 | ~r1_tarski(B_24, A_23) | ~r1_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.41/2.32  tff(c_5157, plain, ('#skF_7'='#skF_8' | ~r1_tarski('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_5141, c_26])).
% 6.41/2.32  tff(c_5164, plain, (~r1_tarski('#skF_7', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_78, c_5157])).
% 6.41/2.32  tff(c_4002, plain, (![A_327, B_328]: (r2_hidden('#skF_2'(A_327, B_328), A_327) | r1_tarski(A_327, B_328))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.41/2.32  tff(c_3854, plain, (![C_39]: (C_39='#skF_6' | ~r2_hidden(C_39, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_3820, c_42])).
% 6.41/2.32  tff(c_4026, plain, (![B_328]: ('#skF_2'('#skF_7', B_328)='#skF_6' | r1_tarski('#skF_7', B_328))), inference(resolution, [status(thm)], [c_4002, c_3854])).
% 6.41/2.32  tff(c_5174, plain, ('#skF_2'('#skF_7', '#skF_8')='#skF_6'), inference(resolution, [status(thm)], [c_4026, c_5164])).
% 6.41/2.32  tff(c_10, plain, (![A_7, B_8]: (~r2_hidden('#skF_2'(A_7, B_8), B_8) | r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.41/2.32  tff(c_5190, plain, (~r2_hidden('#skF_6', '#skF_8') | r1_tarski('#skF_7', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_5174, c_10])).
% 6.41/2.32  tff(c_5198, plain, (~r2_hidden('#skF_6', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_5164, c_5190])).
% 6.41/2.32  tff(c_3822, plain, (![A_311, B_312, C_313]: (~r1_xboole_0(A_311, B_312) | ~r2_hidden(C_313, k3_xboole_0(A_311, B_312)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.41/2.32  tff(c_3830, plain, (![A_311, B_312]: (~r1_xboole_0(A_311, B_312) | v1_xboole_0(k3_xboole_0(A_311, B_312)))), inference(resolution, [status(thm)], [c_6, c_3822])).
% 6.41/2.32  tff(c_5135, plain, (~r1_xboole_0('#skF_7', '#skF_8') | v1_xboole_0('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_5116, c_3830])).
% 6.41/2.32  tff(c_5205, plain, (~r1_xboole_0('#skF_7', '#skF_8')), inference(splitLeft, [status(thm)], [c_5135])).
% 6.41/2.32  tff(c_22, plain, (![A_18, B_19]: (r2_hidden('#skF_3'(A_18, B_19), k3_xboole_0(A_18, B_19)) | r1_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.41/2.32  tff(c_5123, plain, (r2_hidden('#skF_3'('#skF_7', '#skF_8'), '#skF_8') | r1_xboole_0('#skF_7', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_5116, c_22])).
% 6.41/2.32  tff(c_5272, plain, (r2_hidden('#skF_3'('#skF_7', '#skF_8'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_5205, c_5123])).
% 6.41/2.32  tff(c_8, plain, (![C_11, B_8, A_7]: (r2_hidden(C_11, B_8) | ~r2_hidden(C_11, A_7) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.41/2.32  tff(c_6854, plain, (![B_468]: (r2_hidden('#skF_3'('#skF_7', '#skF_8'), B_468) | ~r1_tarski('#skF_8', B_468))), inference(resolution, [status(thm)], [c_5272, c_8])).
% 6.41/2.32  tff(c_6863, plain, ('#skF_3'('#skF_7', '#skF_8')='#skF_6' | ~r1_tarski('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_6854, c_3854])).
% 6.41/2.32  tff(c_6879, plain, ('#skF_3'('#skF_7', '#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_5141, c_6863])).
% 6.41/2.32  tff(c_6893, plain, (r2_hidden('#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_6879, c_5272])).
% 6.41/2.32  tff(c_6895, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5198, c_6893])).
% 6.41/2.32  tff(c_6896, plain, (v1_xboole_0('#skF_8')), inference(splitRight, [status(thm)], [c_5135])).
% 6.41/2.32  tff(c_4425, plain, (![A_374, B_375]: (r2_hidden('#skF_3'(A_374, B_375), k3_xboole_0(A_374, B_375)) | r1_xboole_0(A_374, B_375))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.41/2.32  tff(c_4447, plain, (![A_376, B_377]: (~v1_xboole_0(k3_xboole_0(A_376, B_377)) | r1_xboole_0(A_376, B_377))), inference(resolution, [status(thm)], [c_4425, c_4])).
% 6.41/2.32  tff(c_4462, plain, (![A_378]: (~v1_xboole_0(A_378) | r1_xboole_0(A_378, A_378))), inference(superposition, [status(thm), theory('equality')], [c_20, c_4447])).
% 6.41/2.32  tff(c_4475, plain, (![A_378]: (k3_xboole_0(A_378, A_378)=k1_xboole_0 | ~v1_xboole_0(A_378))), inference(resolution, [status(thm)], [c_4462, c_14])).
% 6.41/2.32  tff(c_4481, plain, (![A_378]: (k1_xboole_0=A_378 | ~v1_xboole_0(A_378))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_4475])).
% 6.41/2.32  tff(c_6900, plain, (k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_6896, c_4481])).
% 6.41/2.32  tff(c_6913, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_6900])).
% 6.41/2.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.41/2.32  
% 6.41/2.32  Inference rules
% 6.41/2.32  ----------------------
% 6.41/2.32  #Ref     : 3
% 6.41/2.32  #Sup     : 1641
% 6.41/2.32  #Fact    : 0
% 6.41/2.32  #Define  : 0
% 6.41/2.32  #Split   : 7
% 6.41/2.32  #Chain   : 0
% 6.41/2.32  #Close   : 0
% 6.41/2.32  
% 6.41/2.32  Ordering : KBO
% 6.41/2.32  
% 6.41/2.32  Simplification rules
% 6.41/2.32  ----------------------
% 6.41/2.32  #Subsume      : 457
% 6.41/2.32  #Demod        : 702
% 6.41/2.32  #Tautology    : 722
% 6.41/2.32  #SimpNegUnit  : 55
% 6.41/2.32  #BackRed      : 11
% 6.41/2.32  
% 6.41/2.32  #Partial instantiations: 0
% 6.41/2.32  #Strategies tried      : 1
% 6.41/2.32  
% 6.41/2.32  Timing (in seconds)
% 6.41/2.32  ----------------------
% 6.41/2.33  Preprocessing        : 0.38
% 6.41/2.33  Parsing              : 0.20
% 6.41/2.33  CNF conversion       : 0.03
% 6.41/2.33  Main loop            : 1.11
% 6.41/2.33  Inferencing          : 0.36
% 6.41/2.33  Reduction            : 0.42
% 6.41/2.33  Demodulation         : 0.31
% 6.41/2.33  BG Simplification    : 0.04
% 6.41/2.33  Subsumption          : 0.21
% 6.41/2.33  Abstraction          : 0.05
% 6.41/2.33  MUC search           : 0.00
% 6.41/2.33  Cooper               : 0.00
% 6.41/2.33  Total                : 1.55
% 6.41/2.33  Index Insertion      : 0.00
% 6.41/2.33  Index Deletion       : 0.00
% 6.41/2.33  Index Matching       : 0.00
% 6.41/2.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
