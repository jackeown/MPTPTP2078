%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:37 EST 2020

% Result     : Theorem 30.04s
% Output     : CNFRefutation 30.08s
% Verified   : 
% Statistics : Number of formulae       :  157 (5843 expanded)
%              Number of leaves         :   39 (2032 expanded)
%              Depth                    :   24
%              Number of atoms          :  200 (8739 expanded)
%              Number of equality atoms :   85 (4297 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_4 > #skF_7 > #skF_6 > #skF_5 > #skF_2 > #skF_3 > #skF_1

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

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_98,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k4_xboole_0(B,k1_tarski(A)),k1_tarski(A)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_zfmisc_1)).

tff(f_67,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_61,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_53,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_65,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_71,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_69,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_73,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(c_86,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_56,plain,(
    ! [A_26] : k5_xboole_0(A_26,k1_xboole_0) = A_26 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_52,plain,(
    ! [A_22,B_23] : k5_xboole_0(A_22,k3_xboole_0(A_22,B_23)) = k4_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_44,plain,(
    ! [A_18] : k3_xboole_0(A_18,A_18) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_161,plain,(
    ! [A_77,B_78] : k5_xboole_0(A_77,k3_xboole_0(A_77,B_78)) = k4_xboole_0(A_77,B_78) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_173,plain,(
    ! [A_79] : k5_xboole_0(A_79,A_79) = k4_xboole_0(A_79,A_79) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_161])).

tff(c_180,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_173,c_56])).

tff(c_285,plain,(
    ! [D_110,B_111,A_112] :
      ( ~ r2_hidden(D_110,B_111)
      | ~ r2_hidden(D_110,k4_xboole_0(A_112,B_111)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_334,plain,(
    ! [D_117] :
      ( ~ r2_hidden(D_117,k1_xboole_0)
      | ~ r2_hidden(D_117,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_180,c_285])).

tff(c_373,plain,(
    ! [B_131] :
      ( ~ r2_hidden('#skF_1'(k1_xboole_0,B_131),k1_xboole_0)
      | r1_tarski(k1_xboole_0,B_131) ) ),
    inference(resolution,[status(thm)],[c_6,c_334])).

tff(c_380,plain,(
    ! [B_132] : r1_tarski(k1_xboole_0,B_132) ),
    inference(resolution,[status(thm)],[c_6,c_373])).

tff(c_54,plain,(
    ! [A_24,B_25] :
      ( k2_xboole_0(A_24,B_25) = B_25
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_390,plain,(
    ! [B_132] : k2_xboole_0(k1_xboole_0,B_132) = B_132 ),
    inference(resolution,[status(thm)],[c_380,c_54])).

tff(c_60,plain,(
    ! [A_30,B_31] : k5_xboole_0(A_30,k4_xboole_0(B_31,A_30)) = k2_xboole_0(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_423,plain,(
    ! [A_135,B_136,C_137] : k5_xboole_0(k5_xboole_0(A_135,B_136),C_137) = k5_xboole_0(A_135,k5_xboole_0(B_136,C_137)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_495,plain,(
    ! [A_142,C_143] : k5_xboole_0(A_142,k5_xboole_0(k1_xboole_0,C_143)) = k5_xboole_0(A_142,C_143) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_423])).

tff(c_528,plain,(
    ! [A_142,B_31] : k5_xboole_0(A_142,k4_xboole_0(B_31,k1_xboole_0)) = k5_xboole_0(A_142,k2_xboole_0(k1_xboole_0,B_31)) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_495])).

tff(c_557,plain,(
    ! [A_144,B_145] : k5_xboole_0(A_144,k4_xboole_0(B_145,k1_xboole_0)) = k5_xboole_0(A_144,B_145) ),
    inference(demodulation,[status(thm),theory(equality)],[c_390,c_528])).

tff(c_575,plain,(
    ! [B_145] : k5_xboole_0(k1_xboole_0,B_145) = k2_xboole_0(k1_xboole_0,B_145) ),
    inference(superposition,[status(thm),theory(equality)],[c_557,c_60])).

tff(c_602,plain,(
    ! [B_145] : k5_xboole_0(k1_xboole_0,B_145) = B_145 ),
    inference(demodulation,[status(thm),theory(equality)],[c_390,c_575])).

tff(c_170,plain,(
    ! [A_18] : k5_xboole_0(A_18,A_18) = k4_xboole_0(A_18,A_18) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_161])).

tff(c_50,plain,(
    ! [B_21] : r1_tarski(B_21,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_116,plain,(
    ! [A_69,B_70] :
      ( k2_xboole_0(A_69,B_70) = B_70
      | ~ r1_tarski(A_69,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_120,plain,(
    ! [B_21] : k2_xboole_0(B_21,B_21) = B_21 ),
    inference(resolution,[status(thm)],[c_50,c_116])).

tff(c_936,plain,(
    ! [A_168,C_169] : k5_xboole_0(k4_xboole_0(A_168,A_168),C_169) = k5_xboole_0(A_168,k5_xboole_0(A_168,C_169)) ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_423])).

tff(c_954,plain,(
    ! [A_168] : k5_xboole_0(A_168,k5_xboole_0(A_168,k4_xboole_0(A_168,A_168))) = k4_xboole_0(k4_xboole_0(A_168,A_168),k4_xboole_0(A_168,A_168)) ),
    inference(superposition,[status(thm),theory(equality)],[c_936,c_170])).

tff(c_996,plain,(
    ! [A_168] : k4_xboole_0(k4_xboole_0(A_168,A_168),k4_xboole_0(A_168,A_168)) = k4_xboole_0(A_168,A_168) ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_120,c_60,c_954])).

tff(c_294,plain,(
    ! [C_113,B_114,A_115] :
      ( r2_hidden(C_113,B_114)
      | ~ r2_hidden(C_113,A_115)
      | ~ r1_tarski(A_115,B_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_306,plain,(
    ! [A_1,B_2,B_114] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_114)
      | ~ r1_tarski(A_1,B_114)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_294])).

tff(c_1610,plain,(
    ! [A_223,B_224,B_225] :
      ( ~ r2_hidden('#skF_1'(k4_xboole_0(A_223,B_224),B_225),B_224)
      | r1_tarski(k4_xboole_0(A_223,B_224),B_225) ) ),
    inference(resolution,[status(thm)],[c_6,c_285])).

tff(c_1651,plain,(
    ! [A_228,B_229,B_230] :
      ( ~ r1_tarski(k4_xboole_0(A_228,B_229),B_229)
      | r1_tarski(k4_xboole_0(A_228,B_229),B_230) ) ),
    inference(resolution,[status(thm)],[c_306,c_1610])).

tff(c_1653,plain,(
    ! [A_168,B_230] :
      ( ~ r1_tarski(k4_xboole_0(A_168,A_168),k4_xboole_0(A_168,A_168))
      | r1_tarski(k4_xboole_0(k4_xboole_0(A_168,A_168),k4_xboole_0(A_168,A_168)),B_230) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_996,c_1651])).

tff(c_1662,plain,(
    ! [A_231,B_232] : r1_tarski(k4_xboole_0(A_231,A_231),B_232) ),
    inference(demodulation,[status(thm),theory(equality)],[c_996,c_50,c_1653])).

tff(c_46,plain,(
    ! [B_21,A_20] :
      ( B_21 = A_20
      | ~ r1_tarski(B_21,A_20)
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_389,plain,(
    ! [B_132] :
      ( k1_xboole_0 = B_132
      | ~ r1_tarski(B_132,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_380,c_46])).

tff(c_1699,plain,(
    ! [A_231] : k4_xboole_0(A_231,A_231) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1662,c_389])).

tff(c_461,plain,(
    ! [A_18,C_137] : k5_xboole_0(k4_xboole_0(A_18,A_18),C_137) = k5_xboole_0(A_18,k5_xboole_0(A_18,C_137)) ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_423])).

tff(c_1711,plain,(
    ! [A_18,C_137] : k5_xboole_0(A_18,k5_xboole_0(A_18,C_137)) = k5_xboole_0(k1_xboole_0,C_137) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1699,c_461])).

tff(c_1826,plain,(
    ! [A_238,C_239] : k5_xboole_0(A_238,k5_xboole_0(A_238,C_239)) = C_239 ),
    inference(demodulation,[status(thm),theory(equality)],[c_602,c_1711])).

tff(c_1875,plain,(
    ! [A_22,B_23] : k5_xboole_0(A_22,k4_xboole_0(A_22,B_23)) = k3_xboole_0(A_22,B_23) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_1826])).

tff(c_62,plain,(
    ! [A_32] : k2_tarski(A_32,A_32) = k1_tarski(A_32) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_723,plain,(
    ! [A_151,B_152,C_153] :
      ( r1_tarski(k2_tarski(A_151,B_152),C_153)
      | ~ r2_hidden(B_152,C_153)
      | ~ r2_hidden(A_151,C_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_893,plain,(
    ! [A_164,C_165] :
      ( r1_tarski(k1_tarski(A_164),C_165)
      | ~ r2_hidden(A_164,C_165)
      | ~ r2_hidden(A_164,C_165) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_723])).

tff(c_912,plain,(
    ! [A_164,C_165] :
      ( k2_xboole_0(k1_tarski(A_164),C_165) = C_165
      | ~ r2_hidden(A_164,C_165) ) ),
    inference(resolution,[status(thm)],[c_893,c_54])).

tff(c_2611,plain,(
    ! [A_261,B_262] : k5_xboole_0(A_261,k2_xboole_0(A_261,B_262)) = k4_xboole_0(B_262,A_261) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_1826])).

tff(c_58,plain,(
    ! [A_27,B_28,C_29] : k5_xboole_0(k5_xboole_0(A_27,B_28),C_29) = k5_xboole_0(A_27,k5_xboole_0(B_28,C_29)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1770,plain,(
    ! [A_234] : k5_xboole_0(A_234,A_234) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1699,c_170])).

tff(c_1896,plain,(
    ! [A_242,B_243] : k5_xboole_0(A_242,k5_xboole_0(B_243,k5_xboole_0(A_242,B_243))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_1770])).

tff(c_1715,plain,(
    ! [A_18,C_137] : k5_xboole_0(A_18,k5_xboole_0(A_18,C_137)) = C_137 ),
    inference(demodulation,[status(thm),theory(equality)],[c_602,c_1711])).

tff(c_1904,plain,(
    ! [B_243,A_242] : k5_xboole_0(B_243,k5_xboole_0(A_242,B_243)) = k5_xboole_0(A_242,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1896,c_1715])).

tff(c_1975,plain,(
    ! [B_243,A_242] : k5_xboole_0(B_243,k5_xboole_0(A_242,B_243)) = A_242 ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1904])).

tff(c_2932,plain,(
    ! [A_279,B_280] : k5_xboole_0(k2_xboole_0(A_279,B_280),k4_xboole_0(B_280,A_279)) = A_279 ),
    inference(superposition,[status(thm),theory(equality)],[c_2611,c_1975])).

tff(c_2962,plain,(
    ! [C_165,A_164] :
      ( k5_xboole_0(C_165,k4_xboole_0(C_165,k1_tarski(A_164))) = k1_tarski(A_164)
      | ~ r2_hidden(A_164,C_165) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_912,c_2932])).

tff(c_5642,plain,(
    ! [C_368,A_369] :
      ( k3_xboole_0(C_368,k1_tarski(A_369)) = k1_tarski(A_369)
      | ~ r2_hidden(A_369,C_368) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1875,c_2962])).

tff(c_2496,plain,(
    ! [A_258,B_259] : k5_xboole_0(A_258,k4_xboole_0(A_258,B_259)) = k3_xboole_0(A_258,B_259) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_1826])).

tff(c_3125,plain,(
    ! [A_283,B_284] : k5_xboole_0(k4_xboole_0(A_283,B_284),k3_xboole_0(A_283,B_284)) = A_283 ),
    inference(superposition,[status(thm),theory(equality)],[c_2496,c_1975])).

tff(c_3146,plain,(
    ! [A_283,B_284] : k5_xboole_0(k4_xboole_0(A_283,B_284),A_283) = k3_xboole_0(A_283,B_284) ),
    inference(superposition,[status(thm),theory(equality)],[c_3125,c_1715])).

tff(c_249,plain,(
    ! [A_103,B_104] :
      ( r2_hidden('#skF_1'(A_103,B_104),A_103)
      | r1_tarski(A_103,B_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_30,plain,(
    ! [D_17,A_12,B_13] :
      ( r2_hidden(D_17,A_12)
      | ~ r2_hidden(D_17,k4_xboole_0(A_12,B_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_4110,plain,(
    ! [A_321,B_322,B_323] :
      ( r2_hidden('#skF_1'(k4_xboole_0(A_321,B_322),B_323),A_321)
      | r1_tarski(k4_xboole_0(A_321,B_322),B_323) ) ),
    inference(resolution,[status(thm)],[c_249,c_30])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4189,plain,(
    ! [A_324,B_325] : r1_tarski(k4_xboole_0(A_324,B_325),A_324) ),
    inference(resolution,[status(thm)],[c_4110,c_4])).

tff(c_4584,plain,(
    ! [A_333,B_334] : k2_xboole_0(k4_xboole_0(A_333,B_334),A_333) = A_333 ),
    inference(resolution,[status(thm)],[c_4189,c_54])).

tff(c_1872,plain,(
    ! [A_30,B_31] : k5_xboole_0(A_30,k2_xboole_0(A_30,B_31)) = k4_xboole_0(B_31,A_30) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_1826])).

tff(c_4603,plain,(
    ! [A_333,B_334] : k5_xboole_0(k4_xboole_0(A_333,B_334),A_333) = k4_xboole_0(A_333,k4_xboole_0(A_333,B_334)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4584,c_1872])).

tff(c_4804,plain,(
    ! [A_340,B_341] : k4_xboole_0(A_340,k4_xboole_0(A_340,B_341)) = k3_xboole_0(A_340,B_341) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3146,c_4603])).

tff(c_4182,plain,(
    ! [A_321,B_322] : r1_tarski(k4_xboole_0(A_321,B_322),A_321) ),
    inference(resolution,[status(thm)],[c_4110,c_4])).

tff(c_4826,plain,(
    ! [A_340,B_341] : r1_tarski(k3_xboole_0(A_340,B_341),A_340) ),
    inference(superposition,[status(thm),theory(equality)],[c_4804,c_4182])).

tff(c_5672,plain,(
    ! [A_369,C_368] :
      ( r1_tarski(k1_tarski(A_369),C_368)
      | ~ r2_hidden(A_369,C_368) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5642,c_4826])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_82811,plain,(
    ! [A_1228,B_1229,B_1230,B_1231] :
      ( r2_hidden('#skF_1'(k4_xboole_0(A_1228,B_1229),B_1230),B_1231)
      | ~ r1_tarski(A_1228,B_1231)
      | r1_tarski(k4_xboole_0(A_1228,B_1229),B_1230) ) ),
    inference(resolution,[status(thm)],[c_4110,c_2])).

tff(c_293,plain,(
    ! [A_112,B_111,B_2] :
      ( ~ r2_hidden('#skF_1'(k4_xboole_0(A_112,B_111),B_2),B_111)
      | r1_tarski(k4_xboole_0(A_112,B_111),B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_285])).

tff(c_83282,plain,(
    ! [A_1240,B_1241,B_1242] :
      ( ~ r1_tarski(A_1240,B_1241)
      | r1_tarski(k4_xboole_0(A_1240,B_1241),B_1242) ) ),
    inference(resolution,[status(thm)],[c_82811,c_293])).

tff(c_83452,plain,(
    ! [A_1243,B_1244] :
      ( k4_xboole_0(A_1243,B_1244) = k1_xboole_0
      | ~ r1_tarski(A_1243,B_1244) ) ),
    inference(resolution,[status(thm)],[c_83282,c_389])).

tff(c_87184,plain,(
    ! [A_1272,C_1273] :
      ( k4_xboole_0(k1_tarski(A_1272),C_1273) = k1_xboole_0
      | ~ r2_hidden(A_1272,C_1273) ) ),
    inference(resolution,[status(thm)],[c_5672,c_83452])).

tff(c_87571,plain,(
    ! [C_1273,A_1272] :
      ( k2_xboole_0(C_1273,k1_tarski(A_1272)) = k5_xboole_0(C_1273,k1_xboole_0)
      | ~ r2_hidden(A_1272,C_1273) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_87184,c_60])).

tff(c_87666,plain,(
    ! [C_1273,A_1272] :
      ( k2_xboole_0(C_1273,k1_tarski(A_1272)) = C_1273
      | ~ r2_hidden(A_1272,C_1273) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_87571])).

tff(c_3143,plain,(
    ! [A_283,B_284] : k5_xboole_0(k3_xboole_0(A_283,B_284),A_283) = k4_xboole_0(A_283,B_284) ),
    inference(superposition,[status(thm),theory(equality)],[c_3125,c_1975])).

tff(c_4228,plain,(
    ! [A_324,B_325] : k2_xboole_0(k4_xboole_0(A_324,B_325),A_324) = A_324 ),
    inference(resolution,[status(thm)],[c_4189,c_54])).

tff(c_4950,plain,(
    ! [A_344,B_345] : k2_xboole_0(k3_xboole_0(A_344,B_345),A_344) = A_344 ),
    inference(superposition,[status(thm),theory(equality)],[c_4804,c_4228])).

tff(c_4969,plain,(
    ! [A_344,B_345] : k5_xboole_0(k3_xboole_0(A_344,B_345),A_344) = k4_xboole_0(A_344,k3_xboole_0(A_344,B_345)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4950,c_1872])).

tff(c_4989,plain,(
    ! [A_344,B_345] : k4_xboole_0(A_344,k3_xboole_0(A_344,B_345)) = k4_xboole_0(A_344,B_345) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3143,c_4969])).

tff(c_10,plain,(
    ! [D_11,B_7,A_6] :
      ( r2_hidden(D_11,B_7)
      | ~ r2_hidden(D_11,k3_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_268,plain,(
    ! [A_6,B_7,B_104] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_6,B_7),B_104),B_7)
      | r1_tarski(k3_xboole_0(A_6,B_7),B_104) ) ),
    inference(resolution,[status(thm)],[c_249,c_10])).

tff(c_12,plain,(
    ! [D_11,A_6,B_7] :
      ( r2_hidden(D_11,A_6)
      | ~ r2_hidden(D_11,k3_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_269,plain,(
    ! [A_6,B_7,B_104] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_6,B_7),B_104),A_6)
      | r1_tarski(k3_xboole_0(A_6,B_7),B_104) ) ),
    inference(resolution,[status(thm)],[c_249,c_12])).

tff(c_868,plain,(
    ! [D_161,A_162,B_163] :
      ( r2_hidden(D_161,k3_xboole_0(A_162,B_163))
      | ~ r2_hidden(D_161,B_163)
      | ~ r2_hidden(D_161,A_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_25584,plain,(
    ! [A_554,A_555,B_556] :
      ( r1_tarski(A_554,k3_xboole_0(A_555,B_556))
      | ~ r2_hidden('#skF_1'(A_554,k3_xboole_0(A_555,B_556)),B_556)
      | ~ r2_hidden('#skF_1'(A_554,k3_xboole_0(A_555,B_556)),A_555) ) ),
    inference(resolution,[status(thm)],[c_868,c_4])).

tff(c_103870,plain,(
    ! [A_1403,B_1404,A_1405] :
      ( ~ r2_hidden('#skF_1'(k3_xboole_0(A_1403,B_1404),k3_xboole_0(A_1405,A_1403)),A_1405)
      | r1_tarski(k3_xboole_0(A_1403,B_1404),k3_xboole_0(A_1405,A_1403)) ) ),
    inference(resolution,[status(thm)],[c_269,c_25584])).

tff(c_104052,plain,(
    ! [A_6,B_7] : r1_tarski(k3_xboole_0(A_6,B_7),k3_xboole_0(B_7,A_6)) ),
    inference(resolution,[status(thm)],[c_268,c_103870])).

tff(c_104070,plain,(
    ! [A_1406,B_1407] : r1_tarski(k3_xboole_0(A_1406,B_1407),k3_xboole_0(B_1407,A_1406)) ),
    inference(resolution,[status(thm)],[c_268,c_103870])).

tff(c_104094,plain,(
    ! [B_1407,A_1406] :
      ( k3_xboole_0(B_1407,A_1406) = k3_xboole_0(A_1406,B_1407)
      | ~ r1_tarski(k3_xboole_0(B_1407,A_1406),k3_xboole_0(A_1406,B_1407)) ) ),
    inference(resolution,[status(thm)],[c_104070,c_46])).

tff(c_104262,plain,(
    ! [B_1408,A_1409] : k3_xboole_0(B_1408,A_1409) = k3_xboole_0(A_1409,B_1408) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104052,c_104094])).

tff(c_1993,plain,(
    ! [B_244,A_245] : k5_xboole_0(B_244,k5_xboole_0(A_245,B_244)) = A_245 ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1904])).

tff(c_2002,plain,(
    ! [B_244,A_245] : k5_xboole_0(B_244,A_245) = k5_xboole_0(A_245,B_244) ),
    inference(superposition,[status(thm),theory(equality)],[c_1993,c_1715])).

tff(c_5389,plain,(
    ! [A_357,B_358,B_359] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_357,B_358),B_359),B_358)
      | r1_tarski(k3_xboole_0(A_357,B_358),B_359) ) ),
    inference(resolution,[status(thm)],[c_249,c_10])).

tff(c_5465,plain,(
    ! [A_360,B_361] : r1_tarski(k3_xboole_0(A_360,B_361),B_361) ),
    inference(resolution,[status(thm)],[c_5389,c_4])).

tff(c_5512,plain,(
    ! [A_362,B_363] : k2_xboole_0(k3_xboole_0(A_362,B_363),B_363) = B_363 ),
    inference(resolution,[status(thm)],[c_5465,c_54])).

tff(c_9322,plain,(
    ! [A_436,B_437] : k5_xboole_0(k3_xboole_0(A_436,B_437),B_437) = k4_xboole_0(B_437,k3_xboole_0(A_436,B_437)) ),
    inference(superposition,[status(thm),theory(equality)],[c_5512,c_1872])).

tff(c_468,plain,(
    ! [A_22,B_23,C_137] : k5_xboole_0(A_22,k5_xboole_0(k3_xboole_0(A_22,B_23),C_137)) = k5_xboole_0(k4_xboole_0(A_22,B_23),C_137) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_423])).

tff(c_9369,plain,(
    ! [A_436,B_437] : k5_xboole_0(A_436,k4_xboole_0(B_437,k3_xboole_0(A_436,B_437))) = k5_xboole_0(k4_xboole_0(A_436,B_437),B_437) ),
    inference(superposition,[status(thm),theory(equality)],[c_9322,c_468])).

tff(c_9451,plain,(
    ! [A_436,B_437] : k5_xboole_0(A_436,k4_xboole_0(B_437,k3_xboole_0(A_436,B_437))) = k2_xboole_0(B_437,A_436) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_2002,c_9369])).

tff(c_105302,plain,(
    ! [B_1408,A_1409] : k5_xboole_0(B_1408,k4_xboole_0(A_1409,k3_xboole_0(A_1409,B_1408))) = k2_xboole_0(A_1409,B_1408) ),
    inference(superposition,[status(thm),theory(equality)],[c_104262,c_9451])).

tff(c_105738,plain,(
    ! [B_1408,A_1409] : k2_xboole_0(B_1408,A_1409) = k2_xboole_0(A_1409,B_1408) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_4989,c_105302])).

tff(c_669,plain,(
    ! [D_147,A_148,B_149] :
      ( r2_hidden(D_147,k4_xboole_0(A_148,B_149))
      | r2_hidden(D_147,B_149)
      | ~ r2_hidden(D_147,A_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_17126,plain,(
    ! [A_513,A_514,B_515] :
      ( r1_tarski(A_513,k4_xboole_0(A_514,B_515))
      | r2_hidden('#skF_1'(A_513,k4_xboole_0(A_514,B_515)),B_515)
      | ~ r2_hidden('#skF_1'(A_513,k4_xboole_0(A_514,B_515)),A_514) ) ),
    inference(resolution,[status(thm)],[c_669,c_4])).

tff(c_61735,plain,(
    ! [A_989,B_990] :
      ( r2_hidden('#skF_1'(A_989,k4_xboole_0(A_989,B_990)),B_990)
      | r1_tarski(A_989,k4_xboole_0(A_989,B_990)) ) ),
    inference(resolution,[status(thm)],[c_6,c_17126])).

tff(c_61855,plain,(
    ! [A_991,B_992] : r1_tarski(k4_xboole_0(A_991,B_992),k4_xboole_0(k4_xboole_0(A_991,B_992),B_992)) ),
    inference(resolution,[status(thm)],[c_61735,c_293])).

tff(c_4227,plain,(
    ! [A_324,B_325] :
      ( k4_xboole_0(A_324,B_325) = A_324
      | ~ r1_tarski(A_324,k4_xboole_0(A_324,B_325)) ) ),
    inference(resolution,[status(thm)],[c_4189,c_46])).

tff(c_61975,plain,(
    ! [A_993,B_994] : k4_xboole_0(k4_xboole_0(A_993,B_994),B_994) = k4_xboole_0(A_993,B_994) ),
    inference(resolution,[status(thm)],[c_61855,c_4227])).

tff(c_62167,plain,(
    ! [B_994,A_993] : k5_xboole_0(B_994,k4_xboole_0(A_993,B_994)) = k2_xboole_0(B_994,k4_xboole_0(A_993,B_994)) ),
    inference(superposition,[status(thm),theory(equality)],[c_61975,c_60])).

tff(c_62273,plain,(
    ! [B_994,A_993] : k2_xboole_0(B_994,k4_xboole_0(A_993,B_994)) = k2_xboole_0(B_994,A_993) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_62167])).

tff(c_84,plain,(
    k2_xboole_0(k4_xboole_0('#skF_7',k1_tarski('#skF_6')),k1_tarski('#skF_6')) != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_107656,plain,(
    k2_xboole_0(k1_tarski('#skF_6'),k4_xboole_0('#skF_7',k1_tarski('#skF_6'))) != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_105738,c_84])).

tff(c_107657,plain,(
    k2_xboole_0('#skF_7',k1_tarski('#skF_6')) != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_105738,c_62273,c_107656])).

tff(c_108271,plain,(
    ~ r2_hidden('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_87666,c_107657])).

tff(c_108278,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_108271])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n007.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 09:58:21 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 30.04/21.63  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 30.08/21.65  
% 30.08/21.65  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 30.08/21.65  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_4 > #skF_7 > #skF_6 > #skF_5 > #skF_2 > #skF_3 > #skF_1
% 30.08/21.65  
% 30.08/21.65  %Foreground sorts:
% 30.08/21.65  
% 30.08/21.65  
% 30.08/21.65  %Background operators:
% 30.08/21.65  
% 30.08/21.65  
% 30.08/21.65  %Foreground operators:
% 30.08/21.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 30.08/21.65  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 30.08/21.65  tff(k1_tarski, type, k1_tarski: $i > $i).
% 30.08/21.65  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 30.08/21.65  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 30.08/21.65  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 30.08/21.65  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 30.08/21.65  tff('#skF_7', type, '#skF_7': $i).
% 30.08/21.65  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 30.08/21.65  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 30.08/21.65  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 30.08/21.65  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 30.08/21.65  tff('#skF_6', type, '#skF_6': $i).
% 30.08/21.65  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 30.08/21.65  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 30.08/21.65  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 30.08/21.65  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 30.08/21.65  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 30.08/21.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 30.08/21.65  tff(k3_tarski, type, k3_tarski: $i > $i).
% 30.08/21.65  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 30.08/21.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 30.08/21.65  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 30.08/21.65  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 30.08/21.65  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 30.08/21.65  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 30.08/21.65  
% 30.08/21.68  tff(f_98, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k4_xboole_0(B, k1_tarski(A)), k1_tarski(A)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t140_zfmisc_1)).
% 30.08/21.68  tff(f_67, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 30.08/21.68  tff(f_61, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 30.08/21.68  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 30.08/21.68  tff(f_53, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 30.08/21.68  tff(f_51, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 30.08/21.68  tff(f_65, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 30.08/21.68  tff(f_71, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 30.08/21.68  tff(f_69, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 30.08/21.68  tff(f_59, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 30.08/21.68  tff(f_73, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 30.08/21.68  tff(f_93, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 30.08/21.68  tff(f_41, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 30.08/21.68  tff(c_86, plain, (r2_hidden('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_98])).
% 30.08/21.68  tff(c_56, plain, (![A_26]: (k5_xboole_0(A_26, k1_xboole_0)=A_26)), inference(cnfTransformation, [status(thm)], [f_67])).
% 30.08/21.68  tff(c_52, plain, (![A_22, B_23]: (k5_xboole_0(A_22, k3_xboole_0(A_22, B_23))=k4_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_61])).
% 30.08/21.68  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 30.08/21.68  tff(c_44, plain, (![A_18]: (k3_xboole_0(A_18, A_18)=A_18)), inference(cnfTransformation, [status(thm)], [f_53])).
% 30.08/21.68  tff(c_161, plain, (![A_77, B_78]: (k5_xboole_0(A_77, k3_xboole_0(A_77, B_78))=k4_xboole_0(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_61])).
% 30.08/21.68  tff(c_173, plain, (![A_79]: (k5_xboole_0(A_79, A_79)=k4_xboole_0(A_79, A_79))), inference(superposition, [status(thm), theory('equality')], [c_44, c_161])).
% 30.08/21.68  tff(c_180, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_173, c_56])).
% 30.08/21.68  tff(c_285, plain, (![D_110, B_111, A_112]: (~r2_hidden(D_110, B_111) | ~r2_hidden(D_110, k4_xboole_0(A_112, B_111)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 30.08/21.68  tff(c_334, plain, (![D_117]: (~r2_hidden(D_117, k1_xboole_0) | ~r2_hidden(D_117, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_180, c_285])).
% 30.08/21.68  tff(c_373, plain, (![B_131]: (~r2_hidden('#skF_1'(k1_xboole_0, B_131), k1_xboole_0) | r1_tarski(k1_xboole_0, B_131))), inference(resolution, [status(thm)], [c_6, c_334])).
% 30.08/21.68  tff(c_380, plain, (![B_132]: (r1_tarski(k1_xboole_0, B_132))), inference(resolution, [status(thm)], [c_6, c_373])).
% 30.08/21.68  tff(c_54, plain, (![A_24, B_25]: (k2_xboole_0(A_24, B_25)=B_25 | ~r1_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_65])).
% 30.08/21.68  tff(c_390, plain, (![B_132]: (k2_xboole_0(k1_xboole_0, B_132)=B_132)), inference(resolution, [status(thm)], [c_380, c_54])).
% 30.08/21.68  tff(c_60, plain, (![A_30, B_31]: (k5_xboole_0(A_30, k4_xboole_0(B_31, A_30))=k2_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_71])).
% 30.08/21.68  tff(c_423, plain, (![A_135, B_136, C_137]: (k5_xboole_0(k5_xboole_0(A_135, B_136), C_137)=k5_xboole_0(A_135, k5_xboole_0(B_136, C_137)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 30.08/21.68  tff(c_495, plain, (![A_142, C_143]: (k5_xboole_0(A_142, k5_xboole_0(k1_xboole_0, C_143))=k5_xboole_0(A_142, C_143))), inference(superposition, [status(thm), theory('equality')], [c_56, c_423])).
% 30.08/21.68  tff(c_528, plain, (![A_142, B_31]: (k5_xboole_0(A_142, k4_xboole_0(B_31, k1_xboole_0))=k5_xboole_0(A_142, k2_xboole_0(k1_xboole_0, B_31)))), inference(superposition, [status(thm), theory('equality')], [c_60, c_495])).
% 30.08/21.68  tff(c_557, plain, (![A_144, B_145]: (k5_xboole_0(A_144, k4_xboole_0(B_145, k1_xboole_0))=k5_xboole_0(A_144, B_145))), inference(demodulation, [status(thm), theory('equality')], [c_390, c_528])).
% 30.08/21.68  tff(c_575, plain, (![B_145]: (k5_xboole_0(k1_xboole_0, B_145)=k2_xboole_0(k1_xboole_0, B_145))), inference(superposition, [status(thm), theory('equality')], [c_557, c_60])).
% 30.08/21.68  tff(c_602, plain, (![B_145]: (k5_xboole_0(k1_xboole_0, B_145)=B_145)), inference(demodulation, [status(thm), theory('equality')], [c_390, c_575])).
% 30.08/21.68  tff(c_170, plain, (![A_18]: (k5_xboole_0(A_18, A_18)=k4_xboole_0(A_18, A_18))), inference(superposition, [status(thm), theory('equality')], [c_44, c_161])).
% 30.08/21.68  tff(c_50, plain, (![B_21]: (r1_tarski(B_21, B_21))), inference(cnfTransformation, [status(thm)], [f_59])).
% 30.08/21.68  tff(c_116, plain, (![A_69, B_70]: (k2_xboole_0(A_69, B_70)=B_70 | ~r1_tarski(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_65])).
% 30.08/21.68  tff(c_120, plain, (![B_21]: (k2_xboole_0(B_21, B_21)=B_21)), inference(resolution, [status(thm)], [c_50, c_116])).
% 30.08/21.68  tff(c_936, plain, (![A_168, C_169]: (k5_xboole_0(k4_xboole_0(A_168, A_168), C_169)=k5_xboole_0(A_168, k5_xboole_0(A_168, C_169)))), inference(superposition, [status(thm), theory('equality')], [c_170, c_423])).
% 30.08/21.68  tff(c_954, plain, (![A_168]: (k5_xboole_0(A_168, k5_xboole_0(A_168, k4_xboole_0(A_168, A_168)))=k4_xboole_0(k4_xboole_0(A_168, A_168), k4_xboole_0(A_168, A_168)))), inference(superposition, [status(thm), theory('equality')], [c_936, c_170])).
% 30.08/21.68  tff(c_996, plain, (![A_168]: (k4_xboole_0(k4_xboole_0(A_168, A_168), k4_xboole_0(A_168, A_168))=k4_xboole_0(A_168, A_168))), inference(demodulation, [status(thm), theory('equality')], [c_170, c_120, c_60, c_954])).
% 30.08/21.68  tff(c_294, plain, (![C_113, B_114, A_115]: (r2_hidden(C_113, B_114) | ~r2_hidden(C_113, A_115) | ~r1_tarski(A_115, B_114))), inference(cnfTransformation, [status(thm)], [f_32])).
% 30.08/21.68  tff(c_306, plain, (![A_1, B_2, B_114]: (r2_hidden('#skF_1'(A_1, B_2), B_114) | ~r1_tarski(A_1, B_114) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_294])).
% 30.08/21.68  tff(c_1610, plain, (![A_223, B_224, B_225]: (~r2_hidden('#skF_1'(k4_xboole_0(A_223, B_224), B_225), B_224) | r1_tarski(k4_xboole_0(A_223, B_224), B_225))), inference(resolution, [status(thm)], [c_6, c_285])).
% 30.08/21.68  tff(c_1651, plain, (![A_228, B_229, B_230]: (~r1_tarski(k4_xboole_0(A_228, B_229), B_229) | r1_tarski(k4_xboole_0(A_228, B_229), B_230))), inference(resolution, [status(thm)], [c_306, c_1610])).
% 30.08/21.68  tff(c_1653, plain, (![A_168, B_230]: (~r1_tarski(k4_xboole_0(A_168, A_168), k4_xboole_0(A_168, A_168)) | r1_tarski(k4_xboole_0(k4_xboole_0(A_168, A_168), k4_xboole_0(A_168, A_168)), B_230))), inference(superposition, [status(thm), theory('equality')], [c_996, c_1651])).
% 30.08/21.68  tff(c_1662, plain, (![A_231, B_232]: (r1_tarski(k4_xboole_0(A_231, A_231), B_232))), inference(demodulation, [status(thm), theory('equality')], [c_996, c_50, c_1653])).
% 30.08/21.68  tff(c_46, plain, (![B_21, A_20]: (B_21=A_20 | ~r1_tarski(B_21, A_20) | ~r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_59])).
% 30.08/21.68  tff(c_389, plain, (![B_132]: (k1_xboole_0=B_132 | ~r1_tarski(B_132, k1_xboole_0))), inference(resolution, [status(thm)], [c_380, c_46])).
% 30.08/21.68  tff(c_1699, plain, (![A_231]: (k4_xboole_0(A_231, A_231)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1662, c_389])).
% 30.08/21.68  tff(c_461, plain, (![A_18, C_137]: (k5_xboole_0(k4_xboole_0(A_18, A_18), C_137)=k5_xboole_0(A_18, k5_xboole_0(A_18, C_137)))), inference(superposition, [status(thm), theory('equality')], [c_170, c_423])).
% 30.08/21.68  tff(c_1711, plain, (![A_18, C_137]: (k5_xboole_0(A_18, k5_xboole_0(A_18, C_137))=k5_xboole_0(k1_xboole_0, C_137))), inference(demodulation, [status(thm), theory('equality')], [c_1699, c_461])).
% 30.08/21.68  tff(c_1826, plain, (![A_238, C_239]: (k5_xboole_0(A_238, k5_xboole_0(A_238, C_239))=C_239)), inference(demodulation, [status(thm), theory('equality')], [c_602, c_1711])).
% 30.08/21.68  tff(c_1875, plain, (![A_22, B_23]: (k5_xboole_0(A_22, k4_xboole_0(A_22, B_23))=k3_xboole_0(A_22, B_23))), inference(superposition, [status(thm), theory('equality')], [c_52, c_1826])).
% 30.08/21.68  tff(c_62, plain, (![A_32]: (k2_tarski(A_32, A_32)=k1_tarski(A_32))), inference(cnfTransformation, [status(thm)], [f_73])).
% 30.08/21.68  tff(c_723, plain, (![A_151, B_152, C_153]: (r1_tarski(k2_tarski(A_151, B_152), C_153) | ~r2_hidden(B_152, C_153) | ~r2_hidden(A_151, C_153))), inference(cnfTransformation, [status(thm)], [f_93])).
% 30.08/21.68  tff(c_893, plain, (![A_164, C_165]: (r1_tarski(k1_tarski(A_164), C_165) | ~r2_hidden(A_164, C_165) | ~r2_hidden(A_164, C_165))), inference(superposition, [status(thm), theory('equality')], [c_62, c_723])).
% 30.08/21.68  tff(c_912, plain, (![A_164, C_165]: (k2_xboole_0(k1_tarski(A_164), C_165)=C_165 | ~r2_hidden(A_164, C_165))), inference(resolution, [status(thm)], [c_893, c_54])).
% 30.08/21.68  tff(c_2611, plain, (![A_261, B_262]: (k5_xboole_0(A_261, k2_xboole_0(A_261, B_262))=k4_xboole_0(B_262, A_261))), inference(superposition, [status(thm), theory('equality')], [c_60, c_1826])).
% 30.08/21.68  tff(c_58, plain, (![A_27, B_28, C_29]: (k5_xboole_0(k5_xboole_0(A_27, B_28), C_29)=k5_xboole_0(A_27, k5_xboole_0(B_28, C_29)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 30.08/21.68  tff(c_1770, plain, (![A_234]: (k5_xboole_0(A_234, A_234)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1699, c_170])).
% 30.08/21.68  tff(c_1896, plain, (![A_242, B_243]: (k5_xboole_0(A_242, k5_xboole_0(B_243, k5_xboole_0(A_242, B_243)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_58, c_1770])).
% 30.08/21.68  tff(c_1715, plain, (![A_18, C_137]: (k5_xboole_0(A_18, k5_xboole_0(A_18, C_137))=C_137)), inference(demodulation, [status(thm), theory('equality')], [c_602, c_1711])).
% 30.08/21.68  tff(c_1904, plain, (![B_243, A_242]: (k5_xboole_0(B_243, k5_xboole_0(A_242, B_243))=k5_xboole_0(A_242, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1896, c_1715])).
% 30.08/21.68  tff(c_1975, plain, (![B_243, A_242]: (k5_xboole_0(B_243, k5_xboole_0(A_242, B_243))=A_242)), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1904])).
% 30.08/21.68  tff(c_2932, plain, (![A_279, B_280]: (k5_xboole_0(k2_xboole_0(A_279, B_280), k4_xboole_0(B_280, A_279))=A_279)), inference(superposition, [status(thm), theory('equality')], [c_2611, c_1975])).
% 30.08/21.68  tff(c_2962, plain, (![C_165, A_164]: (k5_xboole_0(C_165, k4_xboole_0(C_165, k1_tarski(A_164)))=k1_tarski(A_164) | ~r2_hidden(A_164, C_165))), inference(superposition, [status(thm), theory('equality')], [c_912, c_2932])).
% 30.08/21.68  tff(c_5642, plain, (![C_368, A_369]: (k3_xboole_0(C_368, k1_tarski(A_369))=k1_tarski(A_369) | ~r2_hidden(A_369, C_368))), inference(demodulation, [status(thm), theory('equality')], [c_1875, c_2962])).
% 30.08/21.68  tff(c_2496, plain, (![A_258, B_259]: (k5_xboole_0(A_258, k4_xboole_0(A_258, B_259))=k3_xboole_0(A_258, B_259))), inference(superposition, [status(thm), theory('equality')], [c_52, c_1826])).
% 30.08/21.68  tff(c_3125, plain, (![A_283, B_284]: (k5_xboole_0(k4_xboole_0(A_283, B_284), k3_xboole_0(A_283, B_284))=A_283)), inference(superposition, [status(thm), theory('equality')], [c_2496, c_1975])).
% 30.08/21.68  tff(c_3146, plain, (![A_283, B_284]: (k5_xboole_0(k4_xboole_0(A_283, B_284), A_283)=k3_xboole_0(A_283, B_284))), inference(superposition, [status(thm), theory('equality')], [c_3125, c_1715])).
% 30.08/21.68  tff(c_249, plain, (![A_103, B_104]: (r2_hidden('#skF_1'(A_103, B_104), A_103) | r1_tarski(A_103, B_104))), inference(cnfTransformation, [status(thm)], [f_32])).
% 30.08/21.68  tff(c_30, plain, (![D_17, A_12, B_13]: (r2_hidden(D_17, A_12) | ~r2_hidden(D_17, k4_xboole_0(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 30.08/21.68  tff(c_4110, plain, (![A_321, B_322, B_323]: (r2_hidden('#skF_1'(k4_xboole_0(A_321, B_322), B_323), A_321) | r1_tarski(k4_xboole_0(A_321, B_322), B_323))), inference(resolution, [status(thm)], [c_249, c_30])).
% 30.08/21.68  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 30.08/21.68  tff(c_4189, plain, (![A_324, B_325]: (r1_tarski(k4_xboole_0(A_324, B_325), A_324))), inference(resolution, [status(thm)], [c_4110, c_4])).
% 30.08/21.68  tff(c_4584, plain, (![A_333, B_334]: (k2_xboole_0(k4_xboole_0(A_333, B_334), A_333)=A_333)), inference(resolution, [status(thm)], [c_4189, c_54])).
% 30.08/21.68  tff(c_1872, plain, (![A_30, B_31]: (k5_xboole_0(A_30, k2_xboole_0(A_30, B_31))=k4_xboole_0(B_31, A_30))), inference(superposition, [status(thm), theory('equality')], [c_60, c_1826])).
% 30.08/21.68  tff(c_4603, plain, (![A_333, B_334]: (k5_xboole_0(k4_xboole_0(A_333, B_334), A_333)=k4_xboole_0(A_333, k4_xboole_0(A_333, B_334)))), inference(superposition, [status(thm), theory('equality')], [c_4584, c_1872])).
% 30.08/21.68  tff(c_4804, plain, (![A_340, B_341]: (k4_xboole_0(A_340, k4_xboole_0(A_340, B_341))=k3_xboole_0(A_340, B_341))), inference(demodulation, [status(thm), theory('equality')], [c_3146, c_4603])).
% 30.08/21.68  tff(c_4182, plain, (![A_321, B_322]: (r1_tarski(k4_xboole_0(A_321, B_322), A_321))), inference(resolution, [status(thm)], [c_4110, c_4])).
% 30.08/21.68  tff(c_4826, plain, (![A_340, B_341]: (r1_tarski(k3_xboole_0(A_340, B_341), A_340))), inference(superposition, [status(thm), theory('equality')], [c_4804, c_4182])).
% 30.08/21.68  tff(c_5672, plain, (![A_369, C_368]: (r1_tarski(k1_tarski(A_369), C_368) | ~r2_hidden(A_369, C_368))), inference(superposition, [status(thm), theory('equality')], [c_5642, c_4826])).
% 30.08/21.68  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 30.08/21.68  tff(c_82811, plain, (![A_1228, B_1229, B_1230, B_1231]: (r2_hidden('#skF_1'(k4_xboole_0(A_1228, B_1229), B_1230), B_1231) | ~r1_tarski(A_1228, B_1231) | r1_tarski(k4_xboole_0(A_1228, B_1229), B_1230))), inference(resolution, [status(thm)], [c_4110, c_2])).
% 30.08/21.68  tff(c_293, plain, (![A_112, B_111, B_2]: (~r2_hidden('#skF_1'(k4_xboole_0(A_112, B_111), B_2), B_111) | r1_tarski(k4_xboole_0(A_112, B_111), B_2))), inference(resolution, [status(thm)], [c_6, c_285])).
% 30.08/21.68  tff(c_83282, plain, (![A_1240, B_1241, B_1242]: (~r1_tarski(A_1240, B_1241) | r1_tarski(k4_xboole_0(A_1240, B_1241), B_1242))), inference(resolution, [status(thm)], [c_82811, c_293])).
% 30.08/21.68  tff(c_83452, plain, (![A_1243, B_1244]: (k4_xboole_0(A_1243, B_1244)=k1_xboole_0 | ~r1_tarski(A_1243, B_1244))), inference(resolution, [status(thm)], [c_83282, c_389])).
% 30.08/21.68  tff(c_87184, plain, (![A_1272, C_1273]: (k4_xboole_0(k1_tarski(A_1272), C_1273)=k1_xboole_0 | ~r2_hidden(A_1272, C_1273))), inference(resolution, [status(thm)], [c_5672, c_83452])).
% 30.08/21.68  tff(c_87571, plain, (![C_1273, A_1272]: (k2_xboole_0(C_1273, k1_tarski(A_1272))=k5_xboole_0(C_1273, k1_xboole_0) | ~r2_hidden(A_1272, C_1273))), inference(superposition, [status(thm), theory('equality')], [c_87184, c_60])).
% 30.08/21.68  tff(c_87666, plain, (![C_1273, A_1272]: (k2_xboole_0(C_1273, k1_tarski(A_1272))=C_1273 | ~r2_hidden(A_1272, C_1273))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_87571])).
% 30.08/21.68  tff(c_3143, plain, (![A_283, B_284]: (k5_xboole_0(k3_xboole_0(A_283, B_284), A_283)=k4_xboole_0(A_283, B_284))), inference(superposition, [status(thm), theory('equality')], [c_3125, c_1975])).
% 30.08/21.68  tff(c_4228, plain, (![A_324, B_325]: (k2_xboole_0(k4_xboole_0(A_324, B_325), A_324)=A_324)), inference(resolution, [status(thm)], [c_4189, c_54])).
% 30.08/21.68  tff(c_4950, plain, (![A_344, B_345]: (k2_xboole_0(k3_xboole_0(A_344, B_345), A_344)=A_344)), inference(superposition, [status(thm), theory('equality')], [c_4804, c_4228])).
% 30.08/21.68  tff(c_4969, plain, (![A_344, B_345]: (k5_xboole_0(k3_xboole_0(A_344, B_345), A_344)=k4_xboole_0(A_344, k3_xboole_0(A_344, B_345)))), inference(superposition, [status(thm), theory('equality')], [c_4950, c_1872])).
% 30.08/21.68  tff(c_4989, plain, (![A_344, B_345]: (k4_xboole_0(A_344, k3_xboole_0(A_344, B_345))=k4_xboole_0(A_344, B_345))), inference(demodulation, [status(thm), theory('equality')], [c_3143, c_4969])).
% 30.08/21.68  tff(c_10, plain, (![D_11, B_7, A_6]: (r2_hidden(D_11, B_7) | ~r2_hidden(D_11, k3_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 30.08/21.68  tff(c_268, plain, (![A_6, B_7, B_104]: (r2_hidden('#skF_1'(k3_xboole_0(A_6, B_7), B_104), B_7) | r1_tarski(k3_xboole_0(A_6, B_7), B_104))), inference(resolution, [status(thm)], [c_249, c_10])).
% 30.08/21.68  tff(c_12, plain, (![D_11, A_6, B_7]: (r2_hidden(D_11, A_6) | ~r2_hidden(D_11, k3_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 30.08/21.68  tff(c_269, plain, (![A_6, B_7, B_104]: (r2_hidden('#skF_1'(k3_xboole_0(A_6, B_7), B_104), A_6) | r1_tarski(k3_xboole_0(A_6, B_7), B_104))), inference(resolution, [status(thm)], [c_249, c_12])).
% 30.08/21.68  tff(c_868, plain, (![D_161, A_162, B_163]: (r2_hidden(D_161, k3_xboole_0(A_162, B_163)) | ~r2_hidden(D_161, B_163) | ~r2_hidden(D_161, A_162))), inference(cnfTransformation, [status(thm)], [f_41])).
% 30.08/21.68  tff(c_25584, plain, (![A_554, A_555, B_556]: (r1_tarski(A_554, k3_xboole_0(A_555, B_556)) | ~r2_hidden('#skF_1'(A_554, k3_xboole_0(A_555, B_556)), B_556) | ~r2_hidden('#skF_1'(A_554, k3_xboole_0(A_555, B_556)), A_555))), inference(resolution, [status(thm)], [c_868, c_4])).
% 30.08/21.68  tff(c_103870, plain, (![A_1403, B_1404, A_1405]: (~r2_hidden('#skF_1'(k3_xboole_0(A_1403, B_1404), k3_xboole_0(A_1405, A_1403)), A_1405) | r1_tarski(k3_xboole_0(A_1403, B_1404), k3_xboole_0(A_1405, A_1403)))), inference(resolution, [status(thm)], [c_269, c_25584])).
% 30.08/21.68  tff(c_104052, plain, (![A_6, B_7]: (r1_tarski(k3_xboole_0(A_6, B_7), k3_xboole_0(B_7, A_6)))), inference(resolution, [status(thm)], [c_268, c_103870])).
% 30.08/21.68  tff(c_104070, plain, (![A_1406, B_1407]: (r1_tarski(k3_xboole_0(A_1406, B_1407), k3_xboole_0(B_1407, A_1406)))), inference(resolution, [status(thm)], [c_268, c_103870])).
% 30.08/21.68  tff(c_104094, plain, (![B_1407, A_1406]: (k3_xboole_0(B_1407, A_1406)=k3_xboole_0(A_1406, B_1407) | ~r1_tarski(k3_xboole_0(B_1407, A_1406), k3_xboole_0(A_1406, B_1407)))), inference(resolution, [status(thm)], [c_104070, c_46])).
% 30.08/21.68  tff(c_104262, plain, (![B_1408, A_1409]: (k3_xboole_0(B_1408, A_1409)=k3_xboole_0(A_1409, B_1408))), inference(demodulation, [status(thm), theory('equality')], [c_104052, c_104094])).
% 30.08/21.68  tff(c_1993, plain, (![B_244, A_245]: (k5_xboole_0(B_244, k5_xboole_0(A_245, B_244))=A_245)), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1904])).
% 30.08/21.68  tff(c_2002, plain, (![B_244, A_245]: (k5_xboole_0(B_244, A_245)=k5_xboole_0(A_245, B_244))), inference(superposition, [status(thm), theory('equality')], [c_1993, c_1715])).
% 30.08/21.68  tff(c_5389, plain, (![A_357, B_358, B_359]: (r2_hidden('#skF_1'(k3_xboole_0(A_357, B_358), B_359), B_358) | r1_tarski(k3_xboole_0(A_357, B_358), B_359))), inference(resolution, [status(thm)], [c_249, c_10])).
% 30.08/21.68  tff(c_5465, plain, (![A_360, B_361]: (r1_tarski(k3_xboole_0(A_360, B_361), B_361))), inference(resolution, [status(thm)], [c_5389, c_4])).
% 30.08/21.68  tff(c_5512, plain, (![A_362, B_363]: (k2_xboole_0(k3_xboole_0(A_362, B_363), B_363)=B_363)), inference(resolution, [status(thm)], [c_5465, c_54])).
% 30.08/21.68  tff(c_9322, plain, (![A_436, B_437]: (k5_xboole_0(k3_xboole_0(A_436, B_437), B_437)=k4_xboole_0(B_437, k3_xboole_0(A_436, B_437)))), inference(superposition, [status(thm), theory('equality')], [c_5512, c_1872])).
% 30.08/21.68  tff(c_468, plain, (![A_22, B_23, C_137]: (k5_xboole_0(A_22, k5_xboole_0(k3_xboole_0(A_22, B_23), C_137))=k5_xboole_0(k4_xboole_0(A_22, B_23), C_137))), inference(superposition, [status(thm), theory('equality')], [c_52, c_423])).
% 30.08/21.68  tff(c_9369, plain, (![A_436, B_437]: (k5_xboole_0(A_436, k4_xboole_0(B_437, k3_xboole_0(A_436, B_437)))=k5_xboole_0(k4_xboole_0(A_436, B_437), B_437))), inference(superposition, [status(thm), theory('equality')], [c_9322, c_468])).
% 30.08/21.68  tff(c_9451, plain, (![A_436, B_437]: (k5_xboole_0(A_436, k4_xboole_0(B_437, k3_xboole_0(A_436, B_437)))=k2_xboole_0(B_437, A_436))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_2002, c_9369])).
% 30.08/21.68  tff(c_105302, plain, (![B_1408, A_1409]: (k5_xboole_0(B_1408, k4_xboole_0(A_1409, k3_xboole_0(A_1409, B_1408)))=k2_xboole_0(A_1409, B_1408))), inference(superposition, [status(thm), theory('equality')], [c_104262, c_9451])).
% 30.08/21.68  tff(c_105738, plain, (![B_1408, A_1409]: (k2_xboole_0(B_1408, A_1409)=k2_xboole_0(A_1409, B_1408))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_4989, c_105302])).
% 30.08/21.68  tff(c_669, plain, (![D_147, A_148, B_149]: (r2_hidden(D_147, k4_xboole_0(A_148, B_149)) | r2_hidden(D_147, B_149) | ~r2_hidden(D_147, A_148))), inference(cnfTransformation, [status(thm)], [f_51])).
% 30.08/21.68  tff(c_17126, plain, (![A_513, A_514, B_515]: (r1_tarski(A_513, k4_xboole_0(A_514, B_515)) | r2_hidden('#skF_1'(A_513, k4_xboole_0(A_514, B_515)), B_515) | ~r2_hidden('#skF_1'(A_513, k4_xboole_0(A_514, B_515)), A_514))), inference(resolution, [status(thm)], [c_669, c_4])).
% 30.08/21.68  tff(c_61735, plain, (![A_989, B_990]: (r2_hidden('#skF_1'(A_989, k4_xboole_0(A_989, B_990)), B_990) | r1_tarski(A_989, k4_xboole_0(A_989, B_990)))), inference(resolution, [status(thm)], [c_6, c_17126])).
% 30.08/21.68  tff(c_61855, plain, (![A_991, B_992]: (r1_tarski(k4_xboole_0(A_991, B_992), k4_xboole_0(k4_xboole_0(A_991, B_992), B_992)))), inference(resolution, [status(thm)], [c_61735, c_293])).
% 30.08/21.68  tff(c_4227, plain, (![A_324, B_325]: (k4_xboole_0(A_324, B_325)=A_324 | ~r1_tarski(A_324, k4_xboole_0(A_324, B_325)))), inference(resolution, [status(thm)], [c_4189, c_46])).
% 30.08/21.68  tff(c_61975, plain, (![A_993, B_994]: (k4_xboole_0(k4_xboole_0(A_993, B_994), B_994)=k4_xboole_0(A_993, B_994))), inference(resolution, [status(thm)], [c_61855, c_4227])).
% 30.08/21.68  tff(c_62167, plain, (![B_994, A_993]: (k5_xboole_0(B_994, k4_xboole_0(A_993, B_994))=k2_xboole_0(B_994, k4_xboole_0(A_993, B_994)))), inference(superposition, [status(thm), theory('equality')], [c_61975, c_60])).
% 30.08/21.68  tff(c_62273, plain, (![B_994, A_993]: (k2_xboole_0(B_994, k4_xboole_0(A_993, B_994))=k2_xboole_0(B_994, A_993))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_62167])).
% 30.08/21.68  tff(c_84, plain, (k2_xboole_0(k4_xboole_0('#skF_7', k1_tarski('#skF_6')), k1_tarski('#skF_6'))!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_98])).
% 30.08/21.68  tff(c_107656, plain, (k2_xboole_0(k1_tarski('#skF_6'), k4_xboole_0('#skF_7', k1_tarski('#skF_6')))!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_105738, c_84])).
% 30.08/21.68  tff(c_107657, plain, (k2_xboole_0('#skF_7', k1_tarski('#skF_6'))!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_105738, c_62273, c_107656])).
% 30.08/21.68  tff(c_108271, plain, (~r2_hidden('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_87666, c_107657])).
% 30.08/21.68  tff(c_108278, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_108271])).
% 30.08/21.68  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 30.08/21.68  
% 30.08/21.68  Inference rules
% 30.08/21.68  ----------------------
% 30.08/21.68  #Ref     : 0
% 30.08/21.68  #Sup     : 27401
% 30.08/21.68  #Fact    : 0
% 30.08/21.68  #Define  : 0
% 30.08/21.68  #Split   : 10
% 30.08/21.68  #Chain   : 0
% 30.08/21.68  #Close   : 0
% 30.08/21.68  
% 30.08/21.68  Ordering : KBO
% 30.08/21.68  
% 30.08/21.68  Simplification rules
% 30.08/21.68  ----------------------
% 30.08/21.68  #Subsume      : 5944
% 30.08/21.68  #Demod        : 36403
% 30.08/21.68  #Tautology    : 8934
% 30.08/21.68  #SimpNegUnit  : 84
% 30.08/21.68  #BackRed      : 25
% 30.08/21.68  
% 30.08/21.68  #Partial instantiations: 0
% 30.08/21.68  #Strategies tried      : 1
% 30.08/21.68  
% 30.08/21.68  Timing (in seconds)
% 30.08/21.68  ----------------------
% 30.08/21.68  Preprocessing        : 0.37
% 30.08/21.68  Parsing              : 0.19
% 30.08/21.68  CNF conversion       : 0.03
% 30.08/21.68  Main loop            : 20.50
% 30.08/21.68  Inferencing          : 2.51
% 30.08/21.68  Reduction            : 12.18
% 30.08/21.68  Demodulation         : 11.23
% 30.08/21.68  BG Simplification    : 0.33
% 30.08/21.68  Subsumption          : 4.52
% 30.08/21.68  Abstraction          : 0.58
% 30.08/21.68  MUC search           : 0.00
% 30.08/21.68  Cooper               : 0.00
% 30.08/21.68  Total                : 20.92
% 30.08/21.68  Index Insertion      : 0.00
% 30.08/21.68  Index Deletion       : 0.00
% 30.08/21.68  Index Matching       : 0.00
% 30.08/21.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
