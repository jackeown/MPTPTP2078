%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:56 EST 2020

% Result     : Theorem 52.44s
% Output     : CNFRefutation 52.44s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 106 expanded)
%              Number of leaves         :   25 (  46 expanded)
%              Depth                    :   15
%              Number of atoms          :  188 ( 302 expanded)
%              Number of equality atoms :   12 (  19 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k5_relat_1 > k4_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_3 > #skF_2 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_92,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k10_relat_1(k5_relat_1(B,C),A) = k10_relat_1(B,k10_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t181_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_69,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k2_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_40,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_38,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_16,plain,(
    ! [A_11,B_12] :
      ( v1_relat_1(k5_relat_1(A_11,B_12))
      | ~ v1_relat_1(B_12)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_30,plain,(
    ! [B_23,C_25,A_22] :
      ( k10_relat_1(k5_relat_1(B_23,C_25),A_22) = k10_relat_1(B_23,k10_relat_1(C_25,A_22))
      | ~ v1_relat_1(C_25)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_28,plain,(
    ! [A_21] :
      ( k10_relat_1(A_21,k2_relat_1(A_21)) = k1_relat_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_154,plain,(
    ! [A_75,B_76,C_77] :
      ( r2_hidden(k4_tarski(A_75,'#skF_2'(A_75,B_76,C_77)),C_77)
      | ~ r2_hidden(A_75,k10_relat_1(C_77,B_76))
      | ~ v1_relat_1(C_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_293,plain,(
    ! [A_105,B_106,C_107,B_108] :
      ( r2_hidden(k4_tarski(A_105,'#skF_2'(A_105,B_106,C_107)),B_108)
      | ~ r1_tarski(C_107,B_108)
      | ~ r2_hidden(A_105,k10_relat_1(C_107,B_106))
      | ~ v1_relat_1(C_107) ) ),
    inference(resolution,[status(thm)],[c_154,c_2])).

tff(c_32,plain,(
    ! [B_27,C_28,A_26] :
      ( r2_hidden(B_27,k2_relat_1(C_28))
      | ~ r2_hidden(k4_tarski(A_26,B_27),C_28)
      | ~ v1_relat_1(C_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_310,plain,(
    ! [A_105,B_106,C_107,B_108] :
      ( r2_hidden('#skF_2'(A_105,B_106,C_107),k2_relat_1(B_108))
      | ~ v1_relat_1(B_108)
      | ~ r1_tarski(C_107,B_108)
      | ~ r2_hidden(A_105,k10_relat_1(C_107,B_106))
      | ~ v1_relat_1(C_107) ) ),
    inference(resolution,[status(thm)],[c_293,c_32])).

tff(c_22,plain,(
    ! [A_13,B_14,C_15] :
      ( r2_hidden(k4_tarski(A_13,'#skF_2'(A_13,B_14,C_15)),C_15)
      | ~ r2_hidden(A_13,k10_relat_1(C_15,B_14))
      | ~ v1_relat_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_24,plain,(
    ! [A_13,B_14,C_15] :
      ( r2_hidden('#skF_2'(A_13,B_14,C_15),k2_relat_1(C_15))
      | ~ r2_hidden(A_13,k10_relat_1(C_15,B_14))
      | ~ v1_relat_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_217,plain,(
    ! [A_88,C_89,B_90,D_91] :
      ( r2_hidden(A_88,k10_relat_1(C_89,B_90))
      | ~ r2_hidden(D_91,B_90)
      | ~ r2_hidden(k4_tarski(A_88,D_91),C_89)
      | ~ r2_hidden(D_91,k2_relat_1(C_89))
      | ~ v1_relat_1(C_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1360,plain,(
    ! [A_244,C_245,C_242,A_243,B_241] :
      ( r2_hidden(A_244,k10_relat_1(C_242,k2_relat_1(C_245)))
      | ~ r2_hidden(k4_tarski(A_244,'#skF_2'(A_243,B_241,C_245)),C_242)
      | ~ r2_hidden('#skF_2'(A_243,B_241,C_245),k2_relat_1(C_242))
      | ~ v1_relat_1(C_242)
      | ~ r2_hidden(A_243,k10_relat_1(C_245,B_241))
      | ~ v1_relat_1(C_245) ) ),
    inference(resolution,[status(thm)],[c_24,c_217])).

tff(c_1369,plain,(
    ! [A_246,C_247,B_248] :
      ( r2_hidden(A_246,k10_relat_1(C_247,k2_relat_1(C_247)))
      | ~ r2_hidden('#skF_2'(A_246,B_248,C_247),k2_relat_1(C_247))
      | ~ r2_hidden(A_246,k10_relat_1(C_247,B_248))
      | ~ v1_relat_1(C_247) ) ),
    inference(resolution,[status(thm)],[c_22,c_1360])).

tff(c_1373,plain,(
    ! [A_105,B_108,B_106] :
      ( r2_hidden(A_105,k10_relat_1(B_108,k2_relat_1(B_108)))
      | ~ r1_tarski(B_108,B_108)
      | ~ r2_hidden(A_105,k10_relat_1(B_108,B_106))
      | ~ v1_relat_1(B_108) ) ),
    inference(resolution,[status(thm)],[c_310,c_1369])).

tff(c_1398,plain,(
    ! [A_249,B_250,B_251] :
      ( r2_hidden(A_249,k10_relat_1(B_250,k2_relat_1(B_250)))
      | ~ r2_hidden(A_249,k10_relat_1(B_250,B_251))
      | ~ v1_relat_1(B_250) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1373])).

tff(c_1441,plain,(
    ! [A_252,A_253] :
      ( r2_hidden(A_252,k10_relat_1(A_253,k2_relat_1(A_253)))
      | ~ r2_hidden(A_252,k1_relat_1(A_253))
      | ~ v1_relat_1(A_253)
      | ~ v1_relat_1(A_253) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1398])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1936,plain,(
    ! [A_278,A_279] :
      ( r1_tarski(A_278,k10_relat_1(A_279,k2_relat_1(A_279)))
      | ~ r2_hidden('#skF_1'(A_278,k10_relat_1(A_279,k2_relat_1(A_279))),k1_relat_1(A_279))
      | ~ v1_relat_1(A_279) ) ),
    inference(resolution,[status(thm)],[c_1441,c_4])).

tff(c_1975,plain,(
    ! [A_280] :
      ( ~ v1_relat_1(A_280)
      | r1_tarski(k1_relat_1(A_280),k10_relat_1(A_280,k2_relat_1(A_280))) ) ),
    inference(resolution,[status(thm)],[c_6,c_1936])).

tff(c_2028,plain,(
    ! [B_23,C_25] :
      ( ~ v1_relat_1(k5_relat_1(B_23,C_25))
      | r1_tarski(k1_relat_1(k5_relat_1(B_23,C_25)),k10_relat_1(B_23,k10_relat_1(C_25,k2_relat_1(k5_relat_1(B_23,C_25)))))
      | ~ v1_relat_1(C_25)
      | ~ v1_relat_1(B_23) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_1975])).

tff(c_26,plain,(
    ! [B_20,A_19] :
      ( r1_tarski(k10_relat_1(B_20,A_19),k1_relat_1(B_20))
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_98,plain,(
    ! [A_57,B_58,C_59] :
      ( r2_hidden('#skF_2'(A_57,B_58,C_59),B_58)
      | ~ r2_hidden(A_57,k10_relat_1(C_59,B_58))
      | ~ v1_relat_1(C_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_101,plain,(
    ! [A_57,B_58,C_59,B_2] :
      ( r2_hidden('#skF_2'(A_57,B_58,C_59),B_2)
      | ~ r1_tarski(B_58,B_2)
      | ~ r2_hidden(A_57,k10_relat_1(C_59,B_58))
      | ~ v1_relat_1(C_59) ) ),
    inference(resolution,[status(thm)],[c_98,c_2])).

tff(c_7738,plain,(
    ! [B_552,B_549,C_554,C_550,A_551,A_553] :
      ( r2_hidden(A_551,k10_relat_1(C_550,B_552))
      | ~ r2_hidden(k4_tarski(A_551,'#skF_2'(A_553,B_549,C_554)),C_550)
      | ~ r2_hidden('#skF_2'(A_553,B_549,C_554),k2_relat_1(C_550))
      | ~ v1_relat_1(C_550)
      | ~ r1_tarski(B_549,B_552)
      | ~ r2_hidden(A_553,k10_relat_1(C_554,B_549))
      | ~ v1_relat_1(C_554) ) ),
    inference(resolution,[status(thm)],[c_101,c_217])).

tff(c_20148,plain,(
    ! [A_3729,C_3730,B_3731,B_3732] :
      ( r2_hidden(A_3729,k10_relat_1(C_3730,B_3731))
      | ~ r2_hidden('#skF_2'(A_3729,B_3732,C_3730),k2_relat_1(C_3730))
      | ~ r1_tarski(B_3732,B_3731)
      | ~ r2_hidden(A_3729,k10_relat_1(C_3730,B_3732))
      | ~ v1_relat_1(C_3730) ) ),
    inference(resolution,[status(thm)],[c_22,c_7738])).

tff(c_20166,plain,(
    ! [A_105,B_108,B_3731,B_106] :
      ( r2_hidden(A_105,k10_relat_1(B_108,B_3731))
      | ~ r1_tarski(B_106,B_3731)
      | ~ r1_tarski(B_108,B_108)
      | ~ r2_hidden(A_105,k10_relat_1(B_108,B_106))
      | ~ v1_relat_1(B_108) ) ),
    inference(resolution,[status(thm)],[c_310,c_20148])).

tff(c_20187,plain,(
    ! [A_3746,B_3747,B_3748,B_3749] :
      ( r2_hidden(A_3746,k10_relat_1(B_3747,B_3748))
      | ~ r1_tarski(B_3749,B_3748)
      | ~ r2_hidden(A_3746,k10_relat_1(B_3747,B_3749))
      | ~ v1_relat_1(B_3747) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_20166])).

tff(c_20344,plain,(
    ! [A_3779,B_3780,B_3781,A_3782] :
      ( r2_hidden(A_3779,k10_relat_1(B_3780,k1_relat_1(B_3781)))
      | ~ r2_hidden(A_3779,k10_relat_1(B_3780,k10_relat_1(B_3781,A_3782)))
      | ~ v1_relat_1(B_3780)
      | ~ v1_relat_1(B_3781) ) ),
    inference(resolution,[status(thm)],[c_26,c_20187])).

tff(c_80676,plain,(
    ! [B_8563,B_8564,A_8565,B_8566] :
      ( r2_hidden('#skF_1'(k10_relat_1(B_8563,k10_relat_1(B_8564,A_8565)),B_8566),k10_relat_1(B_8563,k1_relat_1(B_8564)))
      | ~ v1_relat_1(B_8563)
      | ~ v1_relat_1(B_8564)
      | r1_tarski(k10_relat_1(B_8563,k10_relat_1(B_8564,A_8565)),B_8566) ) ),
    inference(resolution,[status(thm)],[c_6,c_20344])).

tff(c_80919,plain,(
    ! [B_8580,B_8581,A_8582] :
      ( ~ v1_relat_1(B_8580)
      | ~ v1_relat_1(B_8581)
      | r1_tarski(k10_relat_1(B_8580,k10_relat_1(B_8581,A_8582)),k10_relat_1(B_8580,k1_relat_1(B_8581))) ) ),
    inference(resolution,[status(thm)],[c_80676,c_4])).

tff(c_14,plain,(
    ! [A_8,C_10,B_9] :
      ( r1_tarski(A_8,C_10)
      | ~ r1_tarski(B_9,C_10)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_81345,plain,(
    ! [A_8596,B_8597,B_8598,A_8599] :
      ( r1_tarski(A_8596,k10_relat_1(B_8597,k1_relat_1(B_8598)))
      | ~ r1_tarski(A_8596,k10_relat_1(B_8597,k10_relat_1(B_8598,A_8599)))
      | ~ v1_relat_1(B_8597)
      | ~ v1_relat_1(B_8598) ) ),
    inference(resolution,[status(thm)],[c_80919,c_14])).

tff(c_81687,plain,(
    ! [B_8630,C_8631] :
      ( r1_tarski(k1_relat_1(k5_relat_1(B_8630,C_8631)),k10_relat_1(B_8630,k1_relat_1(C_8631)))
      | ~ v1_relat_1(k5_relat_1(B_8630,C_8631))
      | ~ v1_relat_1(C_8631)
      | ~ v1_relat_1(B_8630) ) ),
    inference(resolution,[status(thm)],[c_2028,c_81345])).

tff(c_121,plain,(
    ! [B_68,C_69,A_70] :
      ( k10_relat_1(k5_relat_1(B_68,C_69),A_70) = k10_relat_1(B_68,k10_relat_1(C_69,A_70))
      | ~ v1_relat_1(C_69)
      | ~ v1_relat_1(B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_273,plain,(
    ! [B_102,C_103,A_104] :
      ( r1_tarski(k10_relat_1(B_102,k10_relat_1(C_103,A_104)),k1_relat_1(k5_relat_1(B_102,C_103)))
      | ~ v1_relat_1(k5_relat_1(B_102,C_103))
      | ~ v1_relat_1(C_103)
      | ~ v1_relat_1(B_102) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_26])).

tff(c_678,plain,(
    ! [B_159,A_160] :
      ( r1_tarski(k10_relat_1(B_159,k1_relat_1(A_160)),k1_relat_1(k5_relat_1(B_159,A_160)))
      | ~ v1_relat_1(k5_relat_1(B_159,A_160))
      | ~ v1_relat_1(A_160)
      | ~ v1_relat_1(B_159)
      | ~ v1_relat_1(A_160) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_273])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_704,plain,(
    ! [B_159,A_160] :
      ( k10_relat_1(B_159,k1_relat_1(A_160)) = k1_relat_1(k5_relat_1(B_159,A_160))
      | ~ r1_tarski(k1_relat_1(k5_relat_1(B_159,A_160)),k10_relat_1(B_159,k1_relat_1(A_160)))
      | ~ v1_relat_1(k5_relat_1(B_159,A_160))
      | ~ v1_relat_1(B_159)
      | ~ v1_relat_1(A_160) ) ),
    inference(resolution,[status(thm)],[c_678,c_8])).

tff(c_82143,plain,(
    ! [B_8645,C_8646] :
      ( k10_relat_1(B_8645,k1_relat_1(C_8646)) = k1_relat_1(k5_relat_1(B_8645,C_8646))
      | ~ v1_relat_1(k5_relat_1(B_8645,C_8646))
      | ~ v1_relat_1(C_8646)
      | ~ v1_relat_1(B_8645) ) ),
    inference(resolution,[status(thm)],[c_81687,c_704])).

tff(c_82160,plain,(
    ! [A_8660,B_8661] :
      ( k10_relat_1(A_8660,k1_relat_1(B_8661)) = k1_relat_1(k5_relat_1(A_8660,B_8661))
      | ~ v1_relat_1(B_8661)
      | ~ v1_relat_1(A_8660) ) ),
    inference(resolution,[status(thm)],[c_16,c_82143])).

tff(c_36,plain,(
    k10_relat_1('#skF_3',k1_relat_1('#skF_4')) != k1_relat_1(k5_relat_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_82782,plain,
    ( ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_82160,c_36])).

tff(c_82847,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_82782])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:03:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 52.44/40.81  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 52.44/40.82  
% 52.44/40.82  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 52.44/40.82  %$ r2_hidden > r1_tarski > v1_relat_1 > k5_relat_1 > k4_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_3 > #skF_2 > #skF_4 > #skF_1
% 52.44/40.82  
% 52.44/40.82  %Foreground sorts:
% 52.44/40.82  
% 52.44/40.82  
% 52.44/40.82  %Background operators:
% 52.44/40.82  
% 52.44/40.82  
% 52.44/40.82  %Foreground operators:
% 52.44/40.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 52.44/40.82  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 52.44/40.82  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 52.44/40.82  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 52.44/40.82  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 52.44/40.82  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 52.44/40.82  tff('#skF_3', type, '#skF_3': $i).
% 52.44/40.82  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 52.44/40.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 52.44/40.82  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 52.44/40.82  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 52.44/40.82  tff('#skF_4', type, '#skF_4': $i).
% 52.44/40.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 52.44/40.82  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 52.44/40.82  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 52.44/40.82  
% 52.44/40.84  tff(f_92, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 52.44/40.84  tff(f_50, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 52.44/40.84  tff(f_76, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k10_relat_1(k5_relat_1(B, C), A) = k10_relat_1(B, k10_relat_1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t181_relat_1)).
% 52.44/40.84  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 52.44/40.84  tff(f_69, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 52.44/40.84  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 52.44/40.84  tff(f_61, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 52.44/40.84  tff(f_84, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k2_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_relat_1)).
% 52.44/40.84  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_relat_1)).
% 52.44/40.84  tff(f_44, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 52.44/40.84  tff(c_40, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_92])).
% 52.44/40.84  tff(c_38, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_92])).
% 52.44/40.84  tff(c_16, plain, (![A_11, B_12]: (v1_relat_1(k5_relat_1(A_11, B_12)) | ~v1_relat_1(B_12) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_50])).
% 52.44/40.84  tff(c_30, plain, (![B_23, C_25, A_22]: (k10_relat_1(k5_relat_1(B_23, C_25), A_22)=k10_relat_1(B_23, k10_relat_1(C_25, A_22)) | ~v1_relat_1(C_25) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_76])).
% 52.44/40.84  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 52.44/40.84  tff(c_28, plain, (![A_21]: (k10_relat_1(A_21, k2_relat_1(A_21))=k1_relat_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_69])).
% 52.44/40.84  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 52.44/40.84  tff(c_154, plain, (![A_75, B_76, C_77]: (r2_hidden(k4_tarski(A_75, '#skF_2'(A_75, B_76, C_77)), C_77) | ~r2_hidden(A_75, k10_relat_1(C_77, B_76)) | ~v1_relat_1(C_77))), inference(cnfTransformation, [status(thm)], [f_61])).
% 52.44/40.84  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 52.44/40.84  tff(c_293, plain, (![A_105, B_106, C_107, B_108]: (r2_hidden(k4_tarski(A_105, '#skF_2'(A_105, B_106, C_107)), B_108) | ~r1_tarski(C_107, B_108) | ~r2_hidden(A_105, k10_relat_1(C_107, B_106)) | ~v1_relat_1(C_107))), inference(resolution, [status(thm)], [c_154, c_2])).
% 52.44/40.84  tff(c_32, plain, (![B_27, C_28, A_26]: (r2_hidden(B_27, k2_relat_1(C_28)) | ~r2_hidden(k4_tarski(A_26, B_27), C_28) | ~v1_relat_1(C_28))), inference(cnfTransformation, [status(thm)], [f_84])).
% 52.44/40.84  tff(c_310, plain, (![A_105, B_106, C_107, B_108]: (r2_hidden('#skF_2'(A_105, B_106, C_107), k2_relat_1(B_108)) | ~v1_relat_1(B_108) | ~r1_tarski(C_107, B_108) | ~r2_hidden(A_105, k10_relat_1(C_107, B_106)) | ~v1_relat_1(C_107))), inference(resolution, [status(thm)], [c_293, c_32])).
% 52.44/40.84  tff(c_22, plain, (![A_13, B_14, C_15]: (r2_hidden(k4_tarski(A_13, '#skF_2'(A_13, B_14, C_15)), C_15) | ~r2_hidden(A_13, k10_relat_1(C_15, B_14)) | ~v1_relat_1(C_15))), inference(cnfTransformation, [status(thm)], [f_61])).
% 52.44/40.84  tff(c_24, plain, (![A_13, B_14, C_15]: (r2_hidden('#skF_2'(A_13, B_14, C_15), k2_relat_1(C_15)) | ~r2_hidden(A_13, k10_relat_1(C_15, B_14)) | ~v1_relat_1(C_15))), inference(cnfTransformation, [status(thm)], [f_61])).
% 52.44/40.84  tff(c_217, plain, (![A_88, C_89, B_90, D_91]: (r2_hidden(A_88, k10_relat_1(C_89, B_90)) | ~r2_hidden(D_91, B_90) | ~r2_hidden(k4_tarski(A_88, D_91), C_89) | ~r2_hidden(D_91, k2_relat_1(C_89)) | ~v1_relat_1(C_89))), inference(cnfTransformation, [status(thm)], [f_61])).
% 52.44/40.84  tff(c_1360, plain, (![A_244, C_245, C_242, A_243, B_241]: (r2_hidden(A_244, k10_relat_1(C_242, k2_relat_1(C_245))) | ~r2_hidden(k4_tarski(A_244, '#skF_2'(A_243, B_241, C_245)), C_242) | ~r2_hidden('#skF_2'(A_243, B_241, C_245), k2_relat_1(C_242)) | ~v1_relat_1(C_242) | ~r2_hidden(A_243, k10_relat_1(C_245, B_241)) | ~v1_relat_1(C_245))), inference(resolution, [status(thm)], [c_24, c_217])).
% 52.44/40.84  tff(c_1369, plain, (![A_246, C_247, B_248]: (r2_hidden(A_246, k10_relat_1(C_247, k2_relat_1(C_247))) | ~r2_hidden('#skF_2'(A_246, B_248, C_247), k2_relat_1(C_247)) | ~r2_hidden(A_246, k10_relat_1(C_247, B_248)) | ~v1_relat_1(C_247))), inference(resolution, [status(thm)], [c_22, c_1360])).
% 52.44/40.84  tff(c_1373, plain, (![A_105, B_108, B_106]: (r2_hidden(A_105, k10_relat_1(B_108, k2_relat_1(B_108))) | ~r1_tarski(B_108, B_108) | ~r2_hidden(A_105, k10_relat_1(B_108, B_106)) | ~v1_relat_1(B_108))), inference(resolution, [status(thm)], [c_310, c_1369])).
% 52.44/40.84  tff(c_1398, plain, (![A_249, B_250, B_251]: (r2_hidden(A_249, k10_relat_1(B_250, k2_relat_1(B_250))) | ~r2_hidden(A_249, k10_relat_1(B_250, B_251)) | ~v1_relat_1(B_250))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1373])).
% 52.44/40.84  tff(c_1441, plain, (![A_252, A_253]: (r2_hidden(A_252, k10_relat_1(A_253, k2_relat_1(A_253))) | ~r2_hidden(A_252, k1_relat_1(A_253)) | ~v1_relat_1(A_253) | ~v1_relat_1(A_253))), inference(superposition, [status(thm), theory('equality')], [c_28, c_1398])).
% 52.44/40.84  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 52.44/40.84  tff(c_1936, plain, (![A_278, A_279]: (r1_tarski(A_278, k10_relat_1(A_279, k2_relat_1(A_279))) | ~r2_hidden('#skF_1'(A_278, k10_relat_1(A_279, k2_relat_1(A_279))), k1_relat_1(A_279)) | ~v1_relat_1(A_279))), inference(resolution, [status(thm)], [c_1441, c_4])).
% 52.44/40.84  tff(c_1975, plain, (![A_280]: (~v1_relat_1(A_280) | r1_tarski(k1_relat_1(A_280), k10_relat_1(A_280, k2_relat_1(A_280))))), inference(resolution, [status(thm)], [c_6, c_1936])).
% 52.44/40.84  tff(c_2028, plain, (![B_23, C_25]: (~v1_relat_1(k5_relat_1(B_23, C_25)) | r1_tarski(k1_relat_1(k5_relat_1(B_23, C_25)), k10_relat_1(B_23, k10_relat_1(C_25, k2_relat_1(k5_relat_1(B_23, C_25))))) | ~v1_relat_1(C_25) | ~v1_relat_1(B_23))), inference(superposition, [status(thm), theory('equality')], [c_30, c_1975])).
% 52.44/40.84  tff(c_26, plain, (![B_20, A_19]: (r1_tarski(k10_relat_1(B_20, A_19), k1_relat_1(B_20)) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_65])).
% 52.44/40.84  tff(c_98, plain, (![A_57, B_58, C_59]: (r2_hidden('#skF_2'(A_57, B_58, C_59), B_58) | ~r2_hidden(A_57, k10_relat_1(C_59, B_58)) | ~v1_relat_1(C_59))), inference(cnfTransformation, [status(thm)], [f_61])).
% 52.44/40.84  tff(c_101, plain, (![A_57, B_58, C_59, B_2]: (r2_hidden('#skF_2'(A_57, B_58, C_59), B_2) | ~r1_tarski(B_58, B_2) | ~r2_hidden(A_57, k10_relat_1(C_59, B_58)) | ~v1_relat_1(C_59))), inference(resolution, [status(thm)], [c_98, c_2])).
% 52.44/40.84  tff(c_7738, plain, (![B_552, B_549, C_554, C_550, A_551, A_553]: (r2_hidden(A_551, k10_relat_1(C_550, B_552)) | ~r2_hidden(k4_tarski(A_551, '#skF_2'(A_553, B_549, C_554)), C_550) | ~r2_hidden('#skF_2'(A_553, B_549, C_554), k2_relat_1(C_550)) | ~v1_relat_1(C_550) | ~r1_tarski(B_549, B_552) | ~r2_hidden(A_553, k10_relat_1(C_554, B_549)) | ~v1_relat_1(C_554))), inference(resolution, [status(thm)], [c_101, c_217])).
% 52.44/40.84  tff(c_20148, plain, (![A_3729, C_3730, B_3731, B_3732]: (r2_hidden(A_3729, k10_relat_1(C_3730, B_3731)) | ~r2_hidden('#skF_2'(A_3729, B_3732, C_3730), k2_relat_1(C_3730)) | ~r1_tarski(B_3732, B_3731) | ~r2_hidden(A_3729, k10_relat_1(C_3730, B_3732)) | ~v1_relat_1(C_3730))), inference(resolution, [status(thm)], [c_22, c_7738])).
% 52.44/40.84  tff(c_20166, plain, (![A_105, B_108, B_3731, B_106]: (r2_hidden(A_105, k10_relat_1(B_108, B_3731)) | ~r1_tarski(B_106, B_3731) | ~r1_tarski(B_108, B_108) | ~r2_hidden(A_105, k10_relat_1(B_108, B_106)) | ~v1_relat_1(B_108))), inference(resolution, [status(thm)], [c_310, c_20148])).
% 52.44/40.84  tff(c_20187, plain, (![A_3746, B_3747, B_3748, B_3749]: (r2_hidden(A_3746, k10_relat_1(B_3747, B_3748)) | ~r1_tarski(B_3749, B_3748) | ~r2_hidden(A_3746, k10_relat_1(B_3747, B_3749)) | ~v1_relat_1(B_3747))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_20166])).
% 52.44/40.84  tff(c_20344, plain, (![A_3779, B_3780, B_3781, A_3782]: (r2_hidden(A_3779, k10_relat_1(B_3780, k1_relat_1(B_3781))) | ~r2_hidden(A_3779, k10_relat_1(B_3780, k10_relat_1(B_3781, A_3782))) | ~v1_relat_1(B_3780) | ~v1_relat_1(B_3781))), inference(resolution, [status(thm)], [c_26, c_20187])).
% 52.44/40.84  tff(c_80676, plain, (![B_8563, B_8564, A_8565, B_8566]: (r2_hidden('#skF_1'(k10_relat_1(B_8563, k10_relat_1(B_8564, A_8565)), B_8566), k10_relat_1(B_8563, k1_relat_1(B_8564))) | ~v1_relat_1(B_8563) | ~v1_relat_1(B_8564) | r1_tarski(k10_relat_1(B_8563, k10_relat_1(B_8564, A_8565)), B_8566))), inference(resolution, [status(thm)], [c_6, c_20344])).
% 52.44/40.84  tff(c_80919, plain, (![B_8580, B_8581, A_8582]: (~v1_relat_1(B_8580) | ~v1_relat_1(B_8581) | r1_tarski(k10_relat_1(B_8580, k10_relat_1(B_8581, A_8582)), k10_relat_1(B_8580, k1_relat_1(B_8581))))), inference(resolution, [status(thm)], [c_80676, c_4])).
% 52.44/40.84  tff(c_14, plain, (![A_8, C_10, B_9]: (r1_tarski(A_8, C_10) | ~r1_tarski(B_9, C_10) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 52.44/40.84  tff(c_81345, plain, (![A_8596, B_8597, B_8598, A_8599]: (r1_tarski(A_8596, k10_relat_1(B_8597, k1_relat_1(B_8598))) | ~r1_tarski(A_8596, k10_relat_1(B_8597, k10_relat_1(B_8598, A_8599))) | ~v1_relat_1(B_8597) | ~v1_relat_1(B_8598))), inference(resolution, [status(thm)], [c_80919, c_14])).
% 52.44/40.84  tff(c_81687, plain, (![B_8630, C_8631]: (r1_tarski(k1_relat_1(k5_relat_1(B_8630, C_8631)), k10_relat_1(B_8630, k1_relat_1(C_8631))) | ~v1_relat_1(k5_relat_1(B_8630, C_8631)) | ~v1_relat_1(C_8631) | ~v1_relat_1(B_8630))), inference(resolution, [status(thm)], [c_2028, c_81345])).
% 52.44/40.84  tff(c_121, plain, (![B_68, C_69, A_70]: (k10_relat_1(k5_relat_1(B_68, C_69), A_70)=k10_relat_1(B_68, k10_relat_1(C_69, A_70)) | ~v1_relat_1(C_69) | ~v1_relat_1(B_68))), inference(cnfTransformation, [status(thm)], [f_76])).
% 52.44/40.84  tff(c_273, plain, (![B_102, C_103, A_104]: (r1_tarski(k10_relat_1(B_102, k10_relat_1(C_103, A_104)), k1_relat_1(k5_relat_1(B_102, C_103))) | ~v1_relat_1(k5_relat_1(B_102, C_103)) | ~v1_relat_1(C_103) | ~v1_relat_1(B_102))), inference(superposition, [status(thm), theory('equality')], [c_121, c_26])).
% 52.44/40.84  tff(c_678, plain, (![B_159, A_160]: (r1_tarski(k10_relat_1(B_159, k1_relat_1(A_160)), k1_relat_1(k5_relat_1(B_159, A_160))) | ~v1_relat_1(k5_relat_1(B_159, A_160)) | ~v1_relat_1(A_160) | ~v1_relat_1(B_159) | ~v1_relat_1(A_160))), inference(superposition, [status(thm), theory('equality')], [c_28, c_273])).
% 52.44/40.84  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 52.44/40.84  tff(c_704, plain, (![B_159, A_160]: (k10_relat_1(B_159, k1_relat_1(A_160))=k1_relat_1(k5_relat_1(B_159, A_160)) | ~r1_tarski(k1_relat_1(k5_relat_1(B_159, A_160)), k10_relat_1(B_159, k1_relat_1(A_160))) | ~v1_relat_1(k5_relat_1(B_159, A_160)) | ~v1_relat_1(B_159) | ~v1_relat_1(A_160))), inference(resolution, [status(thm)], [c_678, c_8])).
% 52.44/40.84  tff(c_82143, plain, (![B_8645, C_8646]: (k10_relat_1(B_8645, k1_relat_1(C_8646))=k1_relat_1(k5_relat_1(B_8645, C_8646)) | ~v1_relat_1(k5_relat_1(B_8645, C_8646)) | ~v1_relat_1(C_8646) | ~v1_relat_1(B_8645))), inference(resolution, [status(thm)], [c_81687, c_704])).
% 52.44/40.84  tff(c_82160, plain, (![A_8660, B_8661]: (k10_relat_1(A_8660, k1_relat_1(B_8661))=k1_relat_1(k5_relat_1(A_8660, B_8661)) | ~v1_relat_1(B_8661) | ~v1_relat_1(A_8660))), inference(resolution, [status(thm)], [c_16, c_82143])).
% 52.44/40.84  tff(c_36, plain, (k10_relat_1('#skF_3', k1_relat_1('#skF_4'))!=k1_relat_1(k5_relat_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 52.44/40.84  tff(c_82782, plain, (~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_82160, c_36])).
% 52.44/40.84  tff(c_82847, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_82782])).
% 52.44/40.84  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 52.44/40.84  
% 52.44/40.84  Inference rules
% 52.44/40.84  ----------------------
% 52.44/40.84  #Ref     : 1
% 52.44/40.84  #Sup     : 22495
% 52.44/40.84  #Fact    : 22
% 52.44/40.84  #Define  : 0
% 52.44/40.84  #Split   : 0
% 52.44/40.84  #Chain   : 0
% 52.44/40.84  #Close   : 0
% 52.44/40.84  
% 52.44/40.84  Ordering : KBO
% 52.44/40.84  
% 52.44/40.84  Simplification rules
% 52.44/40.84  ----------------------
% 52.44/40.84  #Subsume      : 3396
% 52.44/40.84  #Demod        : 1291
% 52.44/40.84  #Tautology    : 282
% 52.44/40.84  #SimpNegUnit  : 0
% 52.44/40.84  #BackRed      : 0
% 52.44/40.84  
% 52.44/40.84  #Partial instantiations: 4698
% 52.44/40.84  #Strategies tried      : 1
% 52.44/40.84  
% 52.44/40.84  Timing (in seconds)
% 52.44/40.84  ----------------------
% 52.44/40.84  Preprocessing        : 0.29
% 52.44/40.84  Parsing              : 0.15
% 52.44/40.84  CNF conversion       : 0.02
% 52.44/40.84  Main loop            : 39.78
% 52.44/40.84  Inferencing          : 2.51
% 52.44/40.84  Reduction            : 2.43
% 52.44/40.84  Demodulation         : 1.58
% 52.44/40.84  BG Simplification    : 0.42
% 52.44/40.84  Subsumption          : 33.18
% 52.44/40.84  Abstraction          : 0.58
% 52.44/40.84  MUC search           : 0.00
% 52.44/40.84  Cooper               : 0.00
% 52.44/40.84  Total                : 40.10
% 52.44/40.84  Index Insertion      : 0.00
% 52.44/40.84  Index Deletion       : 0.00
% 52.44/40.84  Index Matching       : 0.00
% 52.44/40.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
