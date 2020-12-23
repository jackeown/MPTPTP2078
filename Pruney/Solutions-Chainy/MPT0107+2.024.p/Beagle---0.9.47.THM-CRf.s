%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:55 EST 2020

% Result     : Theorem 29.65s
% Output     : CNFRefutation 29.78s
% Verified   : 
% Statistics : Number of formulae       :  113 (11614 expanded)
%              Number of leaves         :   21 (4083 expanded)
%              Depth                    :   25
%              Number of atoms          :  130 (12694 expanded)
%              Number of equality atoms :   91 (11337 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k4_xboole_0(k2_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l98_xboole_1)).

tff(f_52,negated_conjecture,(
    ~ ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_626,plain,(
    ! [A_78,B_79,C_80] :
      ( r2_hidden('#skF_1'(A_78,B_79,C_80),A_78)
      | r2_hidden('#skF_2'(A_78,B_79,C_80),C_80)
      | k4_xboole_0(A_78,B_79) = C_80 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_16,plain,(
    ! [A_3,B_4,C_5] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4,C_5),C_5)
      | r2_hidden('#skF_2'(A_3,B_4,C_5),C_5)
      | k4_xboole_0(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_698,plain,(
    ! [A_78,B_79] :
      ( r2_hidden('#skF_2'(A_78,B_79,A_78),A_78)
      | k4_xboole_0(A_78,B_79) = A_78 ) ),
    inference(resolution,[status(thm)],[c_626,c_16])).

tff(c_14,plain,(
    ! [A_3,B_4,C_5] :
      ( r2_hidden('#skF_1'(A_3,B_4,C_5),A_3)
      | r2_hidden('#skF_2'(A_3,B_4,C_5),B_4)
      | ~ r2_hidden('#skF_2'(A_3,B_4,C_5),A_3)
      | k4_xboole_0(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1493,plain,(
    ! [A_110,B_111,C_112] :
      ( ~ r2_hidden('#skF_1'(A_110,B_111,C_112),C_112)
      | r2_hidden('#skF_2'(A_110,B_111,C_112),B_111)
      | ~ r2_hidden('#skF_2'(A_110,B_111,C_112),A_110)
      | k4_xboole_0(A_110,B_111) = C_112 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_21458,plain,(
    ! [A_377,B_378] :
      ( r2_hidden('#skF_2'(A_377,B_378,A_377),B_378)
      | ~ r2_hidden('#skF_2'(A_377,B_378,A_377),A_377)
      | k4_xboole_0(A_377,B_378) = A_377 ) ),
    inference(resolution,[status(thm)],[c_14,c_1493])).

tff(c_34172,plain,(
    ! [A_552,B_553] :
      ( r2_hidden('#skF_2'(A_552,B_553,A_552),B_553)
      | k4_xboole_0(A_552,B_553) = A_552 ) ),
    inference(resolution,[status(thm)],[c_698,c_21458])).

tff(c_28,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k3_xboole_0(A_16,B_17)) = k4_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_78,plain,(
    ! [A_26,B_27] : k4_xboole_0(A_26,k4_xboole_0(A_26,B_27)) = k3_xboole_0(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_30,plain,(
    ! [A_18,B_19] : k4_xboole_0(A_18,k4_xboole_0(A_18,B_19)) = k3_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_81,plain,(
    ! [A_26,B_27] : k4_xboole_0(A_26,k3_xboole_0(A_26,B_27)) = k3_xboole_0(A_26,k4_xboole_0(A_26,B_27)) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_30])).

tff(c_477,plain,(
    ! [A_26,B_27] : k3_xboole_0(A_26,k4_xboole_0(A_26,B_27)) = k4_xboole_0(A_26,B_27) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_81])).

tff(c_478,plain,(
    ! [A_64,B_65] : k3_xboole_0(A_64,k4_xboole_0(A_64,B_65)) = k4_xboole_0(A_64,B_65) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_81])).

tff(c_96,plain,(
    ! [A_28,B_29] : k4_xboole_0(A_28,k3_xboole_0(A_28,B_29)) = k4_xboole_0(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_139,plain,(
    ! [B_39,A_40] : k4_xboole_0(B_39,k3_xboole_0(A_40,B_39)) = k4_xboole_0(B_39,A_40) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_96])).

tff(c_155,plain,(
    ! [B_39,A_40] : k4_xboole_0(B_39,k4_xboole_0(B_39,A_40)) = k3_xboole_0(B_39,k3_xboole_0(A_40,B_39)) ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_30])).

tff(c_174,plain,(
    ! [B_39,A_40] : k3_xboole_0(B_39,k3_xboole_0(A_40,B_39)) = k3_xboole_0(B_39,A_40) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_155])).

tff(c_490,plain,(
    ! [A_64,B_65] : k3_xboole_0(k4_xboole_0(A_64,B_65),k4_xboole_0(A_64,B_65)) = k3_xboole_0(k4_xboole_0(A_64,B_65),A_64) ),
    inference(superposition,[status(thm),theory(equality)],[c_478,c_174])).

tff(c_522,plain,(
    ! [A_64,B_65] : k3_xboole_0(k4_xboole_0(A_64,B_65),k4_xboole_0(A_64,B_65)) = k4_xboole_0(A_64,B_65) ),
    inference(demodulation,[status(thm),theory(equality)],[c_477,c_2,c_490])).

tff(c_22,plain,(
    ! [A_9,B_10] : k2_xboole_0(k4_xboole_0(A_9,B_10),k4_xboole_0(B_10,A_9)) = k5_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_32,plain,(
    ! [A_20,B_21] : k5_xboole_0(A_20,k4_xboole_0(B_21,A_20)) = k2_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_348,plain,(
    ! [A_52,B_53,C_54] : k4_xboole_0(k4_xboole_0(A_52,B_53),C_54) = k4_xboole_0(A_52,k2_xboole_0(B_53,C_54)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1971,plain,(
    ! [A_122,B_123,C_124] : k4_xboole_0(A_122,k2_xboole_0(k4_xboole_0(A_122,B_123),C_124)) = k4_xboole_0(k3_xboole_0(A_122,B_123),C_124) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_348])).

tff(c_5093,plain,(
    ! [A_208,B_209] : k4_xboole_0(k3_xboole_0(A_208,B_209),k4_xboole_0(B_209,A_208)) = k4_xboole_0(A_208,k5_xboole_0(A_208,B_209)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_1971])).

tff(c_5245,plain,(
    ! [A_26,B_27] : k4_xboole_0(k4_xboole_0(A_26,B_27),k4_xboole_0(k4_xboole_0(A_26,B_27),A_26)) = k4_xboole_0(A_26,k5_xboole_0(A_26,k4_xboole_0(A_26,B_27))) ),
    inference(superposition,[status(thm),theory(equality)],[c_477,c_5093])).

tff(c_5307,plain,(
    ! [A_210,B_211] : k4_xboole_0(A_210,k5_xboole_0(A_210,k4_xboole_0(A_210,B_211))) = k4_xboole_0(A_210,B_211) ),
    inference(demodulation,[status(thm),theory(equality)],[c_477,c_2,c_30,c_5245])).

tff(c_5498,plain,(
    ! [B_212] : k4_xboole_0(B_212,k2_xboole_0(B_212,B_212)) = k4_xboole_0(B_212,B_212) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_5307])).

tff(c_5607,plain,(
    ! [B_212] : k4_xboole_0(B_212,k4_xboole_0(B_212,B_212)) = k3_xboole_0(B_212,k2_xboole_0(B_212,B_212)) ),
    inference(superposition,[status(thm),theory(equality)],[c_5498,c_30])).

tff(c_5727,plain,(
    ! [B_214] : k3_xboole_0(B_214,k2_xboole_0(B_214,B_214)) = k3_xboole_0(B_214,B_214) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_5607])).

tff(c_5856,plain,(
    ! [B_10] : k3_xboole_0(k4_xboole_0(B_10,B_10),k5_xboole_0(B_10,B_10)) = k3_xboole_0(k4_xboole_0(B_10,B_10),k4_xboole_0(B_10,B_10)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_5727])).

tff(c_7903,plain,(
    ! [B_242] : k3_xboole_0(k4_xboole_0(B_242,B_242),k5_xboole_0(B_242,B_242)) = k4_xboole_0(B_242,B_242) ),
    inference(demodulation,[status(thm),theory(equality)],[c_522,c_5856])).

tff(c_118,plain,(
    ! [D_30,A_31,B_32] :
      ( r2_hidden(D_30,A_31)
      | ~ r2_hidden(D_30,k4_xboole_0(A_31,B_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_132,plain,(
    ! [D_36,A_37,B_38] :
      ( r2_hidden(D_36,A_37)
      | ~ r2_hidden(D_36,k3_xboole_0(A_37,B_38)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_118])).

tff(c_135,plain,(
    ! [D_36,A_1,B_2] :
      ( r2_hidden(D_36,A_1)
      | ~ r2_hidden(D_36,k3_xboole_0(B_2,A_1)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_132])).

tff(c_8016,plain,(
    ! [D_36,B_242] :
      ( r2_hidden(D_36,k5_xboole_0(B_242,B_242))
      | ~ r2_hidden(D_36,k4_xboole_0(B_242,B_242)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7903,c_135])).

tff(c_5468,plain,(
    ! [B_21] : k4_xboole_0(B_21,k2_xboole_0(B_21,B_21)) = k4_xboole_0(B_21,B_21) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_5307])).

tff(c_384,plain,(
    ! [C_54,A_52,B_53] : k5_xboole_0(C_54,k4_xboole_0(A_52,k2_xboole_0(B_53,C_54))) = k2_xboole_0(C_54,k4_xboole_0(A_52,B_53)) ),
    inference(superposition,[status(thm),theory(equality)],[c_348,c_32])).

tff(c_5538,plain,(
    ! [B_212] : k5_xboole_0(B_212,k4_xboole_0(B_212,B_212)) = k2_xboole_0(B_212,k4_xboole_0(B_212,B_212)) ),
    inference(superposition,[status(thm),theory(equality)],[c_5498,c_384])).

tff(c_5639,plain,(
    ! [B_212] : k2_xboole_0(B_212,k4_xboole_0(B_212,B_212)) = k2_xboole_0(B_212,B_212) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_5538])).

tff(c_26,plain,(
    ! [A_13,B_14,C_15] : k4_xboole_0(k4_xboole_0(A_13,B_14),C_15) = k4_xboole_0(A_13,k2_xboole_0(B_14,C_15)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_5882,plain,(
    ! [B_10] : k3_xboole_0(k4_xboole_0(B_10,B_10),k5_xboole_0(B_10,B_10)) = k4_xboole_0(B_10,B_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_522,c_5856])).

tff(c_102,plain,(
    ! [A_28,B_29] : k4_xboole_0(A_28,k4_xboole_0(A_28,B_29)) = k3_xboole_0(A_28,k3_xboole_0(A_28,B_29)) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_30])).

tff(c_207,plain,(
    ! [A_43,B_44] : k3_xboole_0(A_43,k3_xboole_0(A_43,B_44)) = k3_xboole_0(A_43,B_44) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_102])).

tff(c_114,plain,(
    ! [B_2,A_1] : k4_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_96])).

tff(c_216,plain,(
    ! [A_43,B_44] : k4_xboole_0(k3_xboole_0(A_43,B_44),k3_xboole_0(A_43,B_44)) = k4_xboole_0(k3_xboole_0(A_43,B_44),A_43) ),
    inference(superposition,[status(thm),theory(equality)],[c_207,c_114])).

tff(c_7933,plain,(
    ! [B_242] : k4_xboole_0(k3_xboole_0(k4_xboole_0(B_242,B_242),k5_xboole_0(B_242,B_242)),k4_xboole_0(B_242,B_242)) = k4_xboole_0(k4_xboole_0(B_242,B_242),k3_xboole_0(k4_xboole_0(B_242,B_242),k5_xboole_0(B_242,B_242))) ),
    inference(superposition,[status(thm),theory(equality)],[c_7903,c_216])).

tff(c_8567,plain,(
    ! [B_249] : k4_xboole_0(B_249,k2_xboole_0(B_249,k5_xboole_0(B_249,B_249))) = k4_xboole_0(B_249,B_249) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5468,c_5639,c_26,c_5882,c_26,c_28,c_7933])).

tff(c_6,plain,(
    ! [D_8,B_4,A_3] :
      ( ~ r2_hidden(D_8,B_4)
      | ~ r2_hidden(D_8,k4_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_367,plain,(
    ! [D_8,C_54,A_52,B_53] :
      ( ~ r2_hidden(D_8,C_54)
      | ~ r2_hidden(D_8,k4_xboole_0(A_52,k2_xboole_0(B_53,C_54))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_348,c_6])).

tff(c_9202,plain,(
    ! [D_259,B_260] :
      ( ~ r2_hidden(D_259,k5_xboole_0(B_260,B_260))
      | ~ r2_hidden(D_259,k4_xboole_0(B_260,B_260)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8567,c_367])).

tff(c_9234,plain,(
    ! [D_36,B_242] : ~ r2_hidden(D_36,k4_xboole_0(B_242,B_242)) ),
    inference(resolution,[status(thm)],[c_8016,c_9202])).

tff(c_34488,plain,(
    ! [A_552,B_242] : k4_xboole_0(A_552,k4_xboole_0(B_242,B_242)) = A_552 ),
    inference(resolution,[status(thm)],[c_34172,c_9234])).

tff(c_20,plain,(
    ! [A_3,B_4,C_5] :
      ( r2_hidden('#skF_1'(A_3,B_4,C_5),A_3)
      | r2_hidden('#skF_2'(A_3,B_4,C_5),C_5)
      | k4_xboole_0(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_826,plain,(
    ! [A_88,B_89,C_90] :
      ( ~ r2_hidden('#skF_1'(A_88,B_89,C_90),B_89)
      | r2_hidden('#skF_2'(A_88,B_89,C_90),C_90)
      | k4_xboole_0(A_88,B_89) = C_90 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_833,plain,(
    ! [A_3,C_5] :
      ( r2_hidden('#skF_2'(A_3,A_3,C_5),C_5)
      | k4_xboole_0(A_3,A_3) = C_5 ) ),
    inference(resolution,[status(thm)],[c_20,c_826])).

tff(c_9242,plain,(
    ! [D_261,B_262] : ~ r2_hidden(D_261,k4_xboole_0(B_262,B_262)) ),
    inference(resolution,[status(thm)],[c_8016,c_9202])).

tff(c_9303,plain,(
    ! [B_263,A_264] : k4_xboole_0(B_263,B_263) = k4_xboole_0(A_264,A_264) ),
    inference(resolution,[status(thm)],[c_833,c_9242])).

tff(c_9570,plain,(
    ! [A_264,B_263] : k4_xboole_0(A_264,k4_xboole_0(B_263,B_263)) = k3_xboole_0(A_264,A_264) ),
    inference(superposition,[status(thm),theory(equality)],[c_9303,c_30])).

tff(c_35338,plain,(
    ! [A_264] : k3_xboole_0(A_264,A_264) = A_264 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34488,c_9570])).

tff(c_179,plain,(
    ! [A_41,B_42] : k2_xboole_0(k4_xboole_0(A_41,B_42),k4_xboole_0(B_42,A_41)) = k5_xboole_0(A_41,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_197,plain,(
    ! [A_16,B_17] : k2_xboole_0(k4_xboole_0(k3_xboole_0(A_16,B_17),A_16),k4_xboole_0(A_16,B_17)) = k5_xboole_0(k3_xboole_0(A_16,B_17),A_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_179])).

tff(c_35341,plain,(
    ! [A_557,B_558] : k4_xboole_0(A_557,k4_xboole_0(B_558,B_558)) = A_557 ),
    inference(resolution,[status(thm)],[c_34172,c_9234])).

tff(c_55019,plain,(
    ! [A_654,B_655,B_656] : k4_xboole_0(A_654,k2_xboole_0(B_655,k4_xboole_0(B_656,B_656))) = k4_xboole_0(A_654,B_655) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_35341])).

tff(c_55708,plain,(
    ! [A_654,B_17] : k4_xboole_0(A_654,k5_xboole_0(k3_xboole_0(B_17,B_17),B_17)) = k4_xboole_0(A_654,k4_xboole_0(k3_xboole_0(B_17,B_17),B_17)) ),
    inference(superposition,[status(thm),theory(equality)],[c_197,c_55019])).

tff(c_55893,plain,(
    ! [A_657,B_658] : k4_xboole_0(A_657,k5_xboole_0(B_658,B_658)) = A_657 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34488,c_35338,c_35338,c_55708])).

tff(c_5650,plain,(
    ! [B_212] : k3_xboole_0(B_212,k2_xboole_0(B_212,B_212)) = k3_xboole_0(B_212,B_212) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_5607])).

tff(c_24,plain,(
    ! [A_11,B_12] : k4_xboole_0(k2_xboole_0(A_11,B_12),k3_xboole_0(A_11,B_12)) = k5_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_5843,plain,(
    ! [B_214] : k4_xboole_0(k2_xboole_0(B_214,B_214),k3_xboole_0(B_214,B_214)) = k4_xboole_0(k2_xboole_0(B_214,B_214),B_214) ),
    inference(superposition,[status(thm),theory(equality)],[c_5727,c_114])).

tff(c_5883,plain,(
    ! [B_215] : k4_xboole_0(k2_xboole_0(B_215,B_215),B_215) = k5_xboole_0(B_215,B_215) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_5843])).

tff(c_5971,plain,(
    ! [B_215] : k4_xboole_0(k2_xboole_0(B_215,B_215),k5_xboole_0(B_215,B_215)) = k3_xboole_0(k2_xboole_0(B_215,B_215),B_215) ),
    inference(superposition,[status(thm),theory(equality)],[c_5883,c_30])).

tff(c_5999,plain,(
    ! [B_215] : k4_xboole_0(k2_xboole_0(B_215,B_215),k5_xboole_0(B_215,B_215)) = k3_xboole_0(B_215,B_215) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5650,c_2,c_5971])).

tff(c_35947,plain,(
    ! [B_215] : k4_xboole_0(k2_xboole_0(B_215,B_215),k5_xboole_0(B_215,B_215)) = B_215 ),
    inference(demodulation,[status(thm),theory(equality)],[c_35338,c_5999])).

tff(c_55950,plain,(
    ! [B_658] : k2_xboole_0(B_658,B_658) = B_658 ),
    inference(superposition,[status(thm),theory(equality)],[c_55893,c_35947])).

tff(c_9297,plain,(
    ! [B_262,A_3] : k4_xboole_0(B_262,B_262) = k4_xboole_0(A_3,A_3) ),
    inference(resolution,[status(thm)],[c_833,c_9242])).

tff(c_57611,plain,(
    ! [B_666,B_667] : k5_xboole_0(B_666,B_666) = k4_xboole_0(B_667,B_667) ),
    inference(superposition,[status(thm),theory(equality)],[c_55893,c_9297])).

tff(c_2694,plain,(
    ! [A_153,B_154] : k5_xboole_0(k3_xboole_0(A_153,B_154),k4_xboole_0(A_153,B_154)) = k2_xboole_0(k3_xboole_0(A_153,B_154),A_153) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_32])).

tff(c_2778,plain,(
    ! [A_1,B_2] : k5_xboole_0(k3_xboole_0(A_1,B_2),k4_xboole_0(B_2,A_1)) = k2_xboole_0(k3_xboole_0(B_2,A_1),B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2694])).

tff(c_57949,plain,(
    ! [B_667,B_666] : k5_xboole_0(k3_xboole_0(B_667,B_667),k5_xboole_0(B_666,B_666)) = k2_xboole_0(k3_xboole_0(B_667,B_667),B_667) ),
    inference(superposition,[status(thm),theory(equality)],[c_57611,c_2778])).

tff(c_58150,plain,(
    ! [B_667,B_666] : k5_xboole_0(B_667,k5_xboole_0(B_666,B_666)) = B_667 ),
    inference(demodulation,[status(thm),theory(equality)],[c_55950,c_35338,c_35338,c_57949])).

tff(c_59912,plain,(
    ! [A_683,B_684] : k4_xboole_0(A_683,A_683) = k3_xboole_0(A_683,k5_xboole_0(B_684,B_684)) ),
    inference(superposition,[status(thm),theory(equality)],[c_55893,c_30])).

tff(c_60551,plain,(
    ! [A_683,B_684] : k4_xboole_0(k2_xboole_0(A_683,k5_xboole_0(B_684,B_684)),k4_xboole_0(A_683,A_683)) = k5_xboole_0(A_683,k5_xboole_0(B_684,B_684)) ),
    inference(superposition,[status(thm),theory(equality)],[c_59912,c_24])).

tff(c_60796,plain,(
    ! [A_683,B_684] : k2_xboole_0(A_683,k5_xboole_0(B_684,B_684)) = A_683 ),
    inference(demodulation,[status(thm),theory(equality)],[c_58150,c_34488,c_60551])).

tff(c_9597,plain,(
    ! [A_43,B_44,A_264] : k4_xboole_0(k3_xboole_0(A_43,B_44),A_43) = k4_xboole_0(A_264,A_264) ),
    inference(superposition,[status(thm),theory(equality)],[c_216,c_9303])).

tff(c_73308,plain,(
    ! [B_751,A_752,B_753] : k5_xboole_0(B_751,B_751) = k4_xboole_0(k3_xboole_0(A_752,B_753),A_752) ),
    inference(superposition,[status(thm),theory(equality)],[c_9597,c_55893])).

tff(c_194,plain,(
    ! [A_16,B_17] : k2_xboole_0(k4_xboole_0(A_16,B_17),k4_xboole_0(k3_xboole_0(A_16,B_17),A_16)) = k5_xboole_0(A_16,k3_xboole_0(A_16,B_17)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_179])).

tff(c_73607,plain,(
    ! [A_752,B_753,B_751] : k5_xboole_0(A_752,k3_xboole_0(A_752,B_753)) = k2_xboole_0(k4_xboole_0(A_752,B_753),k5_xboole_0(B_751,B_751)) ),
    inference(superposition,[status(thm),theory(equality)],[c_73308,c_194])).

tff(c_95357,plain,(
    ! [A_849,B_850] : k5_xboole_0(A_849,k3_xboole_0(A_849,B_850)) = k4_xboole_0(A_849,B_850) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60796,c_73607])).

tff(c_95584,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_95357])).

tff(c_34,plain,(
    k5_xboole_0('#skF_3',k3_xboole_0('#skF_3','#skF_4')) != k4_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_35,plain,(
    k5_xboole_0('#skF_3',k3_xboole_0('#skF_4','#skF_3')) != k4_xboole_0('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_34])).

tff(c_102155,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_95584,c_35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:59:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 29.65/18.70  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 29.78/18.71  
% 29.78/18.71  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 29.78/18.71  %$ r2_hidden > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 29.78/18.71  
% 29.78/18.71  %Foreground sorts:
% 29.78/18.71  
% 29.78/18.71  
% 29.78/18.71  %Background operators:
% 29.78/18.71  
% 29.78/18.71  
% 29.78/18.71  %Foreground operators:
% 29.78/18.71  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 29.78/18.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 29.78/18.71  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 29.78/18.71  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 29.78/18.71  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 29.78/18.71  tff('#skF_3', type, '#skF_3': $i).
% 29.78/18.71  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 29.78/18.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 29.78/18.71  tff('#skF_4', type, '#skF_4': $i).
% 29.78/18.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 29.78/18.71  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 29.78/18.71  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 29.78/18.71  
% 29.78/18.74  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 29.78/18.74  tff(f_37, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 29.78/18.74  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 29.78/18.74  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 29.78/18.74  tff(f_39, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_xboole_0)).
% 29.78/18.74  tff(f_49, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 29.78/18.74  tff(f_43, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 29.78/18.74  tff(f_41, axiom, (![A, B]: (k5_xboole_0(A, B) = k4_xboole_0(k2_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l98_xboole_1)).
% 29.78/18.74  tff(f_52, negated_conjecture, ~(![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 29.78/18.74  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 29.78/18.74  tff(c_626, plain, (![A_78, B_79, C_80]: (r2_hidden('#skF_1'(A_78, B_79, C_80), A_78) | r2_hidden('#skF_2'(A_78, B_79, C_80), C_80) | k4_xboole_0(A_78, B_79)=C_80)), inference(cnfTransformation, [status(thm)], [f_37])).
% 29.78/18.74  tff(c_16, plain, (![A_3, B_4, C_5]: (~r2_hidden('#skF_1'(A_3, B_4, C_5), C_5) | r2_hidden('#skF_2'(A_3, B_4, C_5), C_5) | k4_xboole_0(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_37])).
% 29.78/18.74  tff(c_698, plain, (![A_78, B_79]: (r2_hidden('#skF_2'(A_78, B_79, A_78), A_78) | k4_xboole_0(A_78, B_79)=A_78)), inference(resolution, [status(thm)], [c_626, c_16])).
% 29.78/18.74  tff(c_14, plain, (![A_3, B_4, C_5]: (r2_hidden('#skF_1'(A_3, B_4, C_5), A_3) | r2_hidden('#skF_2'(A_3, B_4, C_5), B_4) | ~r2_hidden('#skF_2'(A_3, B_4, C_5), A_3) | k4_xboole_0(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_37])).
% 29.78/18.74  tff(c_1493, plain, (![A_110, B_111, C_112]: (~r2_hidden('#skF_1'(A_110, B_111, C_112), C_112) | r2_hidden('#skF_2'(A_110, B_111, C_112), B_111) | ~r2_hidden('#skF_2'(A_110, B_111, C_112), A_110) | k4_xboole_0(A_110, B_111)=C_112)), inference(cnfTransformation, [status(thm)], [f_37])).
% 29.78/18.74  tff(c_21458, plain, (![A_377, B_378]: (r2_hidden('#skF_2'(A_377, B_378, A_377), B_378) | ~r2_hidden('#skF_2'(A_377, B_378, A_377), A_377) | k4_xboole_0(A_377, B_378)=A_377)), inference(resolution, [status(thm)], [c_14, c_1493])).
% 29.78/18.74  tff(c_34172, plain, (![A_552, B_553]: (r2_hidden('#skF_2'(A_552, B_553, A_552), B_553) | k4_xboole_0(A_552, B_553)=A_552)), inference(resolution, [status(thm)], [c_698, c_21458])).
% 29.78/18.74  tff(c_28, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k3_xboole_0(A_16, B_17))=k4_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_45])).
% 29.78/18.74  tff(c_78, plain, (![A_26, B_27]: (k4_xboole_0(A_26, k4_xboole_0(A_26, B_27))=k3_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_47])).
% 29.78/18.74  tff(c_30, plain, (![A_18, B_19]: (k4_xboole_0(A_18, k4_xboole_0(A_18, B_19))=k3_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_47])).
% 29.78/18.74  tff(c_81, plain, (![A_26, B_27]: (k4_xboole_0(A_26, k3_xboole_0(A_26, B_27))=k3_xboole_0(A_26, k4_xboole_0(A_26, B_27)))), inference(superposition, [status(thm), theory('equality')], [c_78, c_30])).
% 29.78/18.74  tff(c_477, plain, (![A_26, B_27]: (k3_xboole_0(A_26, k4_xboole_0(A_26, B_27))=k4_xboole_0(A_26, B_27))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_81])).
% 29.78/18.74  tff(c_478, plain, (![A_64, B_65]: (k3_xboole_0(A_64, k4_xboole_0(A_64, B_65))=k4_xboole_0(A_64, B_65))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_81])).
% 29.78/18.74  tff(c_96, plain, (![A_28, B_29]: (k4_xboole_0(A_28, k3_xboole_0(A_28, B_29))=k4_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_45])).
% 29.78/18.74  tff(c_139, plain, (![B_39, A_40]: (k4_xboole_0(B_39, k3_xboole_0(A_40, B_39))=k4_xboole_0(B_39, A_40))), inference(superposition, [status(thm), theory('equality')], [c_2, c_96])).
% 29.78/18.74  tff(c_155, plain, (![B_39, A_40]: (k4_xboole_0(B_39, k4_xboole_0(B_39, A_40))=k3_xboole_0(B_39, k3_xboole_0(A_40, B_39)))), inference(superposition, [status(thm), theory('equality')], [c_139, c_30])).
% 29.78/18.74  tff(c_174, plain, (![B_39, A_40]: (k3_xboole_0(B_39, k3_xboole_0(A_40, B_39))=k3_xboole_0(B_39, A_40))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_155])).
% 29.78/18.74  tff(c_490, plain, (![A_64, B_65]: (k3_xboole_0(k4_xboole_0(A_64, B_65), k4_xboole_0(A_64, B_65))=k3_xboole_0(k4_xboole_0(A_64, B_65), A_64))), inference(superposition, [status(thm), theory('equality')], [c_478, c_174])).
% 29.78/18.74  tff(c_522, plain, (![A_64, B_65]: (k3_xboole_0(k4_xboole_0(A_64, B_65), k4_xboole_0(A_64, B_65))=k4_xboole_0(A_64, B_65))), inference(demodulation, [status(thm), theory('equality')], [c_477, c_2, c_490])).
% 29.78/18.74  tff(c_22, plain, (![A_9, B_10]: (k2_xboole_0(k4_xboole_0(A_9, B_10), k4_xboole_0(B_10, A_9))=k5_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 29.78/18.74  tff(c_32, plain, (![A_20, B_21]: (k5_xboole_0(A_20, k4_xboole_0(B_21, A_20))=k2_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_49])).
% 29.78/18.74  tff(c_348, plain, (![A_52, B_53, C_54]: (k4_xboole_0(k4_xboole_0(A_52, B_53), C_54)=k4_xboole_0(A_52, k2_xboole_0(B_53, C_54)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 29.78/18.74  tff(c_1971, plain, (![A_122, B_123, C_124]: (k4_xboole_0(A_122, k2_xboole_0(k4_xboole_0(A_122, B_123), C_124))=k4_xboole_0(k3_xboole_0(A_122, B_123), C_124))), inference(superposition, [status(thm), theory('equality')], [c_30, c_348])).
% 29.78/18.74  tff(c_5093, plain, (![A_208, B_209]: (k4_xboole_0(k3_xboole_0(A_208, B_209), k4_xboole_0(B_209, A_208))=k4_xboole_0(A_208, k5_xboole_0(A_208, B_209)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_1971])).
% 29.78/18.74  tff(c_5245, plain, (![A_26, B_27]: (k4_xboole_0(k4_xboole_0(A_26, B_27), k4_xboole_0(k4_xboole_0(A_26, B_27), A_26))=k4_xboole_0(A_26, k5_xboole_0(A_26, k4_xboole_0(A_26, B_27))))), inference(superposition, [status(thm), theory('equality')], [c_477, c_5093])).
% 29.78/18.74  tff(c_5307, plain, (![A_210, B_211]: (k4_xboole_0(A_210, k5_xboole_0(A_210, k4_xboole_0(A_210, B_211)))=k4_xboole_0(A_210, B_211))), inference(demodulation, [status(thm), theory('equality')], [c_477, c_2, c_30, c_5245])).
% 29.78/18.74  tff(c_5498, plain, (![B_212]: (k4_xboole_0(B_212, k2_xboole_0(B_212, B_212))=k4_xboole_0(B_212, B_212))), inference(superposition, [status(thm), theory('equality')], [c_32, c_5307])).
% 29.78/18.74  tff(c_5607, plain, (![B_212]: (k4_xboole_0(B_212, k4_xboole_0(B_212, B_212))=k3_xboole_0(B_212, k2_xboole_0(B_212, B_212)))), inference(superposition, [status(thm), theory('equality')], [c_5498, c_30])).
% 29.78/18.74  tff(c_5727, plain, (![B_214]: (k3_xboole_0(B_214, k2_xboole_0(B_214, B_214))=k3_xboole_0(B_214, B_214))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_5607])).
% 29.78/18.74  tff(c_5856, plain, (![B_10]: (k3_xboole_0(k4_xboole_0(B_10, B_10), k5_xboole_0(B_10, B_10))=k3_xboole_0(k4_xboole_0(B_10, B_10), k4_xboole_0(B_10, B_10)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_5727])).
% 29.78/18.74  tff(c_7903, plain, (![B_242]: (k3_xboole_0(k4_xboole_0(B_242, B_242), k5_xboole_0(B_242, B_242))=k4_xboole_0(B_242, B_242))), inference(demodulation, [status(thm), theory('equality')], [c_522, c_5856])).
% 29.78/18.74  tff(c_118, plain, (![D_30, A_31, B_32]: (r2_hidden(D_30, A_31) | ~r2_hidden(D_30, k4_xboole_0(A_31, B_32)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 29.78/18.74  tff(c_132, plain, (![D_36, A_37, B_38]: (r2_hidden(D_36, A_37) | ~r2_hidden(D_36, k3_xboole_0(A_37, B_38)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_118])).
% 29.78/18.74  tff(c_135, plain, (![D_36, A_1, B_2]: (r2_hidden(D_36, A_1) | ~r2_hidden(D_36, k3_xboole_0(B_2, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_132])).
% 29.78/18.74  tff(c_8016, plain, (![D_36, B_242]: (r2_hidden(D_36, k5_xboole_0(B_242, B_242)) | ~r2_hidden(D_36, k4_xboole_0(B_242, B_242)))), inference(superposition, [status(thm), theory('equality')], [c_7903, c_135])).
% 29.78/18.74  tff(c_5468, plain, (![B_21]: (k4_xboole_0(B_21, k2_xboole_0(B_21, B_21))=k4_xboole_0(B_21, B_21))), inference(superposition, [status(thm), theory('equality')], [c_32, c_5307])).
% 29.78/18.74  tff(c_384, plain, (![C_54, A_52, B_53]: (k5_xboole_0(C_54, k4_xboole_0(A_52, k2_xboole_0(B_53, C_54)))=k2_xboole_0(C_54, k4_xboole_0(A_52, B_53)))), inference(superposition, [status(thm), theory('equality')], [c_348, c_32])).
% 29.78/18.74  tff(c_5538, plain, (![B_212]: (k5_xboole_0(B_212, k4_xboole_0(B_212, B_212))=k2_xboole_0(B_212, k4_xboole_0(B_212, B_212)))), inference(superposition, [status(thm), theory('equality')], [c_5498, c_384])).
% 29.78/18.74  tff(c_5639, plain, (![B_212]: (k2_xboole_0(B_212, k4_xboole_0(B_212, B_212))=k2_xboole_0(B_212, B_212))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_5538])).
% 29.78/18.74  tff(c_26, plain, (![A_13, B_14, C_15]: (k4_xboole_0(k4_xboole_0(A_13, B_14), C_15)=k4_xboole_0(A_13, k2_xboole_0(B_14, C_15)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 29.78/18.74  tff(c_5882, plain, (![B_10]: (k3_xboole_0(k4_xboole_0(B_10, B_10), k5_xboole_0(B_10, B_10))=k4_xboole_0(B_10, B_10))), inference(demodulation, [status(thm), theory('equality')], [c_522, c_5856])).
% 29.78/18.74  tff(c_102, plain, (![A_28, B_29]: (k4_xboole_0(A_28, k4_xboole_0(A_28, B_29))=k3_xboole_0(A_28, k3_xboole_0(A_28, B_29)))), inference(superposition, [status(thm), theory('equality')], [c_96, c_30])).
% 29.78/18.74  tff(c_207, plain, (![A_43, B_44]: (k3_xboole_0(A_43, k3_xboole_0(A_43, B_44))=k3_xboole_0(A_43, B_44))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_102])).
% 29.78/18.74  tff(c_114, plain, (![B_2, A_1]: (k4_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_96])).
% 29.78/18.74  tff(c_216, plain, (![A_43, B_44]: (k4_xboole_0(k3_xboole_0(A_43, B_44), k3_xboole_0(A_43, B_44))=k4_xboole_0(k3_xboole_0(A_43, B_44), A_43))), inference(superposition, [status(thm), theory('equality')], [c_207, c_114])).
% 29.78/18.74  tff(c_7933, plain, (![B_242]: (k4_xboole_0(k3_xboole_0(k4_xboole_0(B_242, B_242), k5_xboole_0(B_242, B_242)), k4_xboole_0(B_242, B_242))=k4_xboole_0(k4_xboole_0(B_242, B_242), k3_xboole_0(k4_xboole_0(B_242, B_242), k5_xboole_0(B_242, B_242))))), inference(superposition, [status(thm), theory('equality')], [c_7903, c_216])).
% 29.78/18.74  tff(c_8567, plain, (![B_249]: (k4_xboole_0(B_249, k2_xboole_0(B_249, k5_xboole_0(B_249, B_249)))=k4_xboole_0(B_249, B_249))), inference(demodulation, [status(thm), theory('equality')], [c_5468, c_5639, c_26, c_5882, c_26, c_28, c_7933])).
% 29.78/18.74  tff(c_6, plain, (![D_8, B_4, A_3]: (~r2_hidden(D_8, B_4) | ~r2_hidden(D_8, k4_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 29.78/18.74  tff(c_367, plain, (![D_8, C_54, A_52, B_53]: (~r2_hidden(D_8, C_54) | ~r2_hidden(D_8, k4_xboole_0(A_52, k2_xboole_0(B_53, C_54))))), inference(superposition, [status(thm), theory('equality')], [c_348, c_6])).
% 29.78/18.74  tff(c_9202, plain, (![D_259, B_260]: (~r2_hidden(D_259, k5_xboole_0(B_260, B_260)) | ~r2_hidden(D_259, k4_xboole_0(B_260, B_260)))), inference(superposition, [status(thm), theory('equality')], [c_8567, c_367])).
% 29.78/18.74  tff(c_9234, plain, (![D_36, B_242]: (~r2_hidden(D_36, k4_xboole_0(B_242, B_242)))), inference(resolution, [status(thm)], [c_8016, c_9202])).
% 29.78/18.74  tff(c_34488, plain, (![A_552, B_242]: (k4_xboole_0(A_552, k4_xboole_0(B_242, B_242))=A_552)), inference(resolution, [status(thm)], [c_34172, c_9234])).
% 29.78/18.74  tff(c_20, plain, (![A_3, B_4, C_5]: (r2_hidden('#skF_1'(A_3, B_4, C_5), A_3) | r2_hidden('#skF_2'(A_3, B_4, C_5), C_5) | k4_xboole_0(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_37])).
% 29.78/18.74  tff(c_826, plain, (![A_88, B_89, C_90]: (~r2_hidden('#skF_1'(A_88, B_89, C_90), B_89) | r2_hidden('#skF_2'(A_88, B_89, C_90), C_90) | k4_xboole_0(A_88, B_89)=C_90)), inference(cnfTransformation, [status(thm)], [f_37])).
% 29.78/18.74  tff(c_833, plain, (![A_3, C_5]: (r2_hidden('#skF_2'(A_3, A_3, C_5), C_5) | k4_xboole_0(A_3, A_3)=C_5)), inference(resolution, [status(thm)], [c_20, c_826])).
% 29.78/18.74  tff(c_9242, plain, (![D_261, B_262]: (~r2_hidden(D_261, k4_xboole_0(B_262, B_262)))), inference(resolution, [status(thm)], [c_8016, c_9202])).
% 29.78/18.74  tff(c_9303, plain, (![B_263, A_264]: (k4_xboole_0(B_263, B_263)=k4_xboole_0(A_264, A_264))), inference(resolution, [status(thm)], [c_833, c_9242])).
% 29.78/18.74  tff(c_9570, plain, (![A_264, B_263]: (k4_xboole_0(A_264, k4_xboole_0(B_263, B_263))=k3_xboole_0(A_264, A_264))), inference(superposition, [status(thm), theory('equality')], [c_9303, c_30])).
% 29.78/18.74  tff(c_35338, plain, (![A_264]: (k3_xboole_0(A_264, A_264)=A_264)), inference(demodulation, [status(thm), theory('equality')], [c_34488, c_9570])).
% 29.78/18.74  tff(c_179, plain, (![A_41, B_42]: (k2_xboole_0(k4_xboole_0(A_41, B_42), k4_xboole_0(B_42, A_41))=k5_xboole_0(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_39])).
% 29.78/18.74  tff(c_197, plain, (![A_16, B_17]: (k2_xboole_0(k4_xboole_0(k3_xboole_0(A_16, B_17), A_16), k4_xboole_0(A_16, B_17))=k5_xboole_0(k3_xboole_0(A_16, B_17), A_16))), inference(superposition, [status(thm), theory('equality')], [c_28, c_179])).
% 29.78/18.74  tff(c_35341, plain, (![A_557, B_558]: (k4_xboole_0(A_557, k4_xboole_0(B_558, B_558))=A_557)), inference(resolution, [status(thm)], [c_34172, c_9234])).
% 29.78/18.74  tff(c_55019, plain, (![A_654, B_655, B_656]: (k4_xboole_0(A_654, k2_xboole_0(B_655, k4_xboole_0(B_656, B_656)))=k4_xboole_0(A_654, B_655))), inference(superposition, [status(thm), theory('equality')], [c_26, c_35341])).
% 29.78/18.74  tff(c_55708, plain, (![A_654, B_17]: (k4_xboole_0(A_654, k5_xboole_0(k3_xboole_0(B_17, B_17), B_17))=k4_xboole_0(A_654, k4_xboole_0(k3_xboole_0(B_17, B_17), B_17)))), inference(superposition, [status(thm), theory('equality')], [c_197, c_55019])).
% 29.78/18.74  tff(c_55893, plain, (![A_657, B_658]: (k4_xboole_0(A_657, k5_xboole_0(B_658, B_658))=A_657)), inference(demodulation, [status(thm), theory('equality')], [c_34488, c_35338, c_35338, c_55708])).
% 29.78/18.74  tff(c_5650, plain, (![B_212]: (k3_xboole_0(B_212, k2_xboole_0(B_212, B_212))=k3_xboole_0(B_212, B_212))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_5607])).
% 29.78/18.74  tff(c_24, plain, (![A_11, B_12]: (k4_xboole_0(k2_xboole_0(A_11, B_12), k3_xboole_0(A_11, B_12))=k5_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 29.78/18.74  tff(c_5843, plain, (![B_214]: (k4_xboole_0(k2_xboole_0(B_214, B_214), k3_xboole_0(B_214, B_214))=k4_xboole_0(k2_xboole_0(B_214, B_214), B_214))), inference(superposition, [status(thm), theory('equality')], [c_5727, c_114])).
% 29.78/18.74  tff(c_5883, plain, (![B_215]: (k4_xboole_0(k2_xboole_0(B_215, B_215), B_215)=k5_xboole_0(B_215, B_215))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_5843])).
% 29.78/18.74  tff(c_5971, plain, (![B_215]: (k4_xboole_0(k2_xboole_0(B_215, B_215), k5_xboole_0(B_215, B_215))=k3_xboole_0(k2_xboole_0(B_215, B_215), B_215))), inference(superposition, [status(thm), theory('equality')], [c_5883, c_30])).
% 29.78/18.74  tff(c_5999, plain, (![B_215]: (k4_xboole_0(k2_xboole_0(B_215, B_215), k5_xboole_0(B_215, B_215))=k3_xboole_0(B_215, B_215))), inference(demodulation, [status(thm), theory('equality')], [c_5650, c_2, c_5971])).
% 29.78/18.74  tff(c_35947, plain, (![B_215]: (k4_xboole_0(k2_xboole_0(B_215, B_215), k5_xboole_0(B_215, B_215))=B_215)), inference(demodulation, [status(thm), theory('equality')], [c_35338, c_5999])).
% 29.78/18.74  tff(c_55950, plain, (![B_658]: (k2_xboole_0(B_658, B_658)=B_658)), inference(superposition, [status(thm), theory('equality')], [c_55893, c_35947])).
% 29.78/18.74  tff(c_9297, plain, (![B_262, A_3]: (k4_xboole_0(B_262, B_262)=k4_xboole_0(A_3, A_3))), inference(resolution, [status(thm)], [c_833, c_9242])).
% 29.78/18.74  tff(c_57611, plain, (![B_666, B_667]: (k5_xboole_0(B_666, B_666)=k4_xboole_0(B_667, B_667))), inference(superposition, [status(thm), theory('equality')], [c_55893, c_9297])).
% 29.78/18.74  tff(c_2694, plain, (![A_153, B_154]: (k5_xboole_0(k3_xboole_0(A_153, B_154), k4_xboole_0(A_153, B_154))=k2_xboole_0(k3_xboole_0(A_153, B_154), A_153))), inference(superposition, [status(thm), theory('equality')], [c_96, c_32])).
% 29.78/18.74  tff(c_2778, plain, (![A_1, B_2]: (k5_xboole_0(k3_xboole_0(A_1, B_2), k4_xboole_0(B_2, A_1))=k2_xboole_0(k3_xboole_0(B_2, A_1), B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_2694])).
% 29.78/18.74  tff(c_57949, plain, (![B_667, B_666]: (k5_xboole_0(k3_xboole_0(B_667, B_667), k5_xboole_0(B_666, B_666))=k2_xboole_0(k3_xboole_0(B_667, B_667), B_667))), inference(superposition, [status(thm), theory('equality')], [c_57611, c_2778])).
% 29.78/18.74  tff(c_58150, plain, (![B_667, B_666]: (k5_xboole_0(B_667, k5_xboole_0(B_666, B_666))=B_667)), inference(demodulation, [status(thm), theory('equality')], [c_55950, c_35338, c_35338, c_57949])).
% 29.78/18.74  tff(c_59912, plain, (![A_683, B_684]: (k4_xboole_0(A_683, A_683)=k3_xboole_0(A_683, k5_xboole_0(B_684, B_684)))), inference(superposition, [status(thm), theory('equality')], [c_55893, c_30])).
% 29.78/18.74  tff(c_60551, plain, (![A_683, B_684]: (k4_xboole_0(k2_xboole_0(A_683, k5_xboole_0(B_684, B_684)), k4_xboole_0(A_683, A_683))=k5_xboole_0(A_683, k5_xboole_0(B_684, B_684)))), inference(superposition, [status(thm), theory('equality')], [c_59912, c_24])).
% 29.78/18.74  tff(c_60796, plain, (![A_683, B_684]: (k2_xboole_0(A_683, k5_xboole_0(B_684, B_684))=A_683)), inference(demodulation, [status(thm), theory('equality')], [c_58150, c_34488, c_60551])).
% 29.78/18.74  tff(c_9597, plain, (![A_43, B_44, A_264]: (k4_xboole_0(k3_xboole_0(A_43, B_44), A_43)=k4_xboole_0(A_264, A_264))), inference(superposition, [status(thm), theory('equality')], [c_216, c_9303])).
% 29.78/18.74  tff(c_73308, plain, (![B_751, A_752, B_753]: (k5_xboole_0(B_751, B_751)=k4_xboole_0(k3_xboole_0(A_752, B_753), A_752))), inference(superposition, [status(thm), theory('equality')], [c_9597, c_55893])).
% 29.78/18.74  tff(c_194, plain, (![A_16, B_17]: (k2_xboole_0(k4_xboole_0(A_16, B_17), k4_xboole_0(k3_xboole_0(A_16, B_17), A_16))=k5_xboole_0(A_16, k3_xboole_0(A_16, B_17)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_179])).
% 29.78/18.74  tff(c_73607, plain, (![A_752, B_753, B_751]: (k5_xboole_0(A_752, k3_xboole_0(A_752, B_753))=k2_xboole_0(k4_xboole_0(A_752, B_753), k5_xboole_0(B_751, B_751)))), inference(superposition, [status(thm), theory('equality')], [c_73308, c_194])).
% 29.78/18.74  tff(c_95357, plain, (![A_849, B_850]: (k5_xboole_0(A_849, k3_xboole_0(A_849, B_850))=k4_xboole_0(A_849, B_850))), inference(demodulation, [status(thm), theory('equality')], [c_60796, c_73607])).
% 29.78/18.74  tff(c_95584, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_95357])).
% 29.78/18.74  tff(c_34, plain, (k5_xboole_0('#skF_3', k3_xboole_0('#skF_3', '#skF_4'))!=k4_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_52])).
% 29.78/18.74  tff(c_35, plain, (k5_xboole_0('#skF_3', k3_xboole_0('#skF_4', '#skF_3'))!=k4_xboole_0('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_34])).
% 29.78/18.74  tff(c_102155, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_95584, c_35])).
% 29.78/18.74  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 29.78/18.74  
% 29.78/18.74  Inference rules
% 29.78/18.74  ----------------------
% 29.78/18.74  #Ref     : 0
% 29.78/18.74  #Sup     : 27241
% 29.78/18.74  #Fact    : 0
% 29.78/18.74  #Define  : 0
% 29.78/18.74  #Split   : 0
% 29.78/18.74  #Chain   : 0
% 29.78/18.74  #Close   : 0
% 29.78/18.74  
% 29.78/18.74  Ordering : KBO
% 29.78/18.74  
% 29.78/18.74  Simplification rules
% 29.78/18.74  ----------------------
% 29.78/18.74  #Subsume      : 7821
% 29.78/18.74  #Demod        : 21573
% 29.78/18.74  #Tautology    : 5040
% 29.78/18.74  #SimpNegUnit  : 609
% 29.78/18.74  #BackRed      : 38
% 29.78/18.74  
% 29.78/18.74  #Partial instantiations: 0
% 29.78/18.74  #Strategies tried      : 1
% 29.78/18.74  
% 29.78/18.74  Timing (in seconds)
% 29.78/18.74  ----------------------
% 29.78/18.74  Preprocessing        : 0.27
% 29.78/18.74  Parsing              : 0.15
% 29.78/18.74  CNF conversion       : 0.02
% 29.78/18.74  Main loop            : 17.68
% 29.78/18.74  Inferencing          : 2.15
% 29.78/18.74  Reduction            : 10.91
% 29.78/18.74  Demodulation         : 9.75
% 29.78/18.74  BG Simplification    : 0.36
% 29.78/18.74  Subsumption          : 3.47
% 29.78/18.74  Abstraction          : 0.61
% 29.78/18.74  MUC search           : 0.00
% 29.78/18.74  Cooper               : 0.00
% 29.78/18.74  Total                : 18.01
% 29.78/18.74  Index Insertion      : 0.00
% 29.78/18.74  Index Deletion       : 0.00
% 29.78/18.74  Index Matching       : 0.00
% 29.78/18.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
