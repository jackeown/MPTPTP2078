%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:04 EST 2020

% Result     : Theorem 7.93s
% Output     : CNFRefutation 7.93s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 501 expanded)
%              Number of leaves         :   40 ( 185 expanded)
%              Depth                    :   21
%              Number of atoms          :  102 ( 711 expanded)
%              Number of equality atoms :   63 ( 298 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

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

tff(f_83,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_69,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_71,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

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

tff(f_59,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_65,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_61,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_81,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_99,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_102,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_zfmisc_1)).

tff(c_36,plain,(
    ! [A_31,B_32] : k5_xboole_0(A_31,k4_xboole_0(B_32,A_31)) = k2_xboole_0(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_116,plain,(
    ! [B_75,A_76] : k5_xboole_0(B_75,A_76) = k5_xboole_0(A_76,B_75) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_28,plain,(
    ! [A_24] : k5_xboole_0(A_24,k1_xboole_0) = A_24 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_132,plain,(
    ! [A_76] : k5_xboole_0(k1_xboole_0,A_76) = A_76 ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_28])).

tff(c_30,plain,(
    ! [A_25] : r1_xboole_0(A_25,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_208,plain,(
    ! [B_79,A_80] :
      ( r1_xboole_0(B_79,A_80)
      | ~ r1_xboole_0(A_80,B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_211,plain,(
    ! [A_25] : r1_xboole_0(k1_xboole_0,A_25) ),
    inference(resolution,[status(thm)],[c_30,c_208])).

tff(c_8,plain,(
    ! [A_5] :
      ( v1_xboole_0(A_5)
      | r2_hidden('#skF_1'(A_5),A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_235,plain,(
    ! [A_86,B_87,C_88] :
      ( ~ r1_xboole_0(A_86,B_87)
      | ~ r2_hidden(C_88,k3_xboole_0(A_86,B_87)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_324,plain,(
    ! [A_99,B_100] :
      ( ~ r1_xboole_0(A_99,B_100)
      | v1_xboole_0(k3_xboole_0(A_99,B_100)) ) ),
    inference(resolution,[status(thm)],[c_8,c_235])).

tff(c_20,plain,(
    ! [B_17] : r1_tarski(B_17,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_226,plain,(
    ! [A_84,B_85] :
      ( k3_xboole_0(A_84,B_85) = A_84
      | ~ r1_tarski(A_84,B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_247,plain,(
    ! [B_89] : k3_xboole_0(B_89,B_89) = B_89 ),
    inference(resolution,[status(thm)],[c_20,c_226])).

tff(c_14,plain,(
    ! [A_11,B_12,C_15] :
      ( ~ r1_xboole_0(A_11,B_12)
      | ~ r2_hidden(C_15,k3_xboole_0(A_11,B_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_259,plain,(
    ! [B_90,C_91] :
      ( ~ r1_xboole_0(B_90,B_90)
      | ~ r2_hidden(C_91,B_90) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_247,c_14])).

tff(c_268,plain,(
    ! [C_92] : ~ r2_hidden(C_92,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_211,c_259])).

tff(c_273,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_268])).

tff(c_32,plain,(
    ! [B_27,A_26] :
      ( ~ v1_xboole_0(B_27)
      | B_27 = A_26
      | ~ v1_xboole_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_276,plain,(
    ! [A_26] :
      ( k1_xboole_0 = A_26
      | ~ v1_xboole_0(A_26) ) ),
    inference(resolution,[status(thm)],[c_273,c_32])).

tff(c_371,plain,(
    ! [A_104,B_105] :
      ( k3_xboole_0(A_104,B_105) = k1_xboole_0
      | ~ r1_xboole_0(A_104,B_105) ) ),
    inference(resolution,[status(thm)],[c_324,c_276])).

tff(c_378,plain,(
    ! [A_25] : k3_xboole_0(k1_xboole_0,A_25) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_211,c_371])).

tff(c_508,plain,(
    ! [A_110,B_111] : k5_xboole_0(A_110,k3_xboole_0(A_110,B_111)) = k4_xboole_0(A_110,B_111) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_515,plain,(
    ! [B_111] : k4_xboole_0(k1_xboole_0,B_111) = k3_xboole_0(k1_xboole_0,B_111) ),
    inference(superposition,[status(thm),theory(equality)],[c_508,c_132])).

tff(c_539,plain,(
    ! [B_111] : k4_xboole_0(k1_xboole_0,B_111) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_378,c_515])).

tff(c_277,plain,(
    ! [A_93,B_94] : k5_xboole_0(A_93,k4_xboole_0(B_94,A_93)) = k2_xboole_0(A_93,B_94) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_284,plain,(
    ! [B_94] : k4_xboole_0(B_94,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_94) ),
    inference(superposition,[status(thm),theory(equality)],[c_277,c_132])).

tff(c_379,plain,(
    ! [A_25] : k3_xboole_0(A_25,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_371])).

tff(c_521,plain,(
    ! [A_25] : k5_xboole_0(A_25,k1_xboole_0) = k4_xboole_0(A_25,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_379,c_508])).

tff(c_577,plain,(
    ! [A_116] : k2_xboole_0(k1_xboole_0,A_116) = A_116 ),
    inference(demodulation,[status(thm),theory(equality)],[c_284,c_28,c_521])).

tff(c_26,plain,(
    ! [A_22,B_23] : k4_xboole_0(k2_xboole_0(A_22,B_23),B_23) = k4_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_583,plain,(
    ! [A_116] : k4_xboole_0(k1_xboole_0,A_116) = k4_xboole_0(A_116,A_116) ),
    inference(superposition,[status(thm),theory(equality)],[c_577,c_26])).

tff(c_588,plain,(
    ! [A_116] : k4_xboole_0(A_116,A_116) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_539,c_583])).

tff(c_234,plain,(
    ! [B_17] : k3_xboole_0(B_17,B_17) = B_17 ),
    inference(resolution,[status(thm)],[c_20,c_226])).

tff(c_527,plain,(
    ! [B_17] : k5_xboole_0(B_17,B_17) = k4_xboole_0(B_17,B_17) ),
    inference(superposition,[status(thm),theory(equality)],[c_234,c_508])).

tff(c_817,plain,(
    ! [B_126] : k5_xboole_0(B_126,B_126) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_588,c_527])).

tff(c_34,plain,(
    ! [A_28,B_29,C_30] : k5_xboole_0(k5_xboole_0(A_28,B_29),C_30) = k5_xboole_0(A_28,k5_xboole_0(B_29,C_30)) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_822,plain,(
    ! [B_126,C_30] : k5_xboole_0(B_126,k5_xboole_0(B_126,C_30)) = k5_xboole_0(k1_xboole_0,C_30) ),
    inference(superposition,[status(thm),theory(equality)],[c_817,c_34])).

tff(c_856,plain,(
    ! [B_127,C_128] : k5_xboole_0(B_127,k5_xboole_0(B_127,C_128)) = C_128 ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_822])).

tff(c_1760,plain,(
    ! [A_182,B_183] : k5_xboole_0(A_182,k2_xboole_0(A_182,B_183)) = k4_xboole_0(B_183,A_182) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_856])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_905,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k5_xboole_0(B_4,A_3)) = B_4 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_856])).

tff(c_924,plain,(
    ! [A_129,B_130] : k5_xboole_0(A_129,k5_xboole_0(B_130,A_129)) = B_130 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_856])).

tff(c_951,plain,(
    ! [B_4,A_3] : k5_xboole_0(k5_xboole_0(B_4,A_3),B_4) = A_3 ),
    inference(superposition,[status(thm),theory(equality)],[c_905,c_924])).

tff(c_1766,plain,(
    ! [B_183,A_182] : k5_xboole_0(k4_xboole_0(B_183,A_182),A_182) = k2_xboole_0(A_182,B_183) ),
    inference(superposition,[status(thm),theory(equality)],[c_1760,c_951])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_537,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_508])).

tff(c_739,plain,(
    ! [A_123,B_124,C_125] : k5_xboole_0(k5_xboole_0(A_123,B_124),C_125) = k5_xboole_0(A_123,k5_xboole_0(B_124,C_125)) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2748,plain,(
    ! [B_205,A_206,B_207] : k5_xboole_0(B_205,k5_xboole_0(A_206,B_207)) = k5_xboole_0(A_206,k5_xboole_0(B_207,B_205)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_739])).

tff(c_3220,plain,(
    ! [A_208,B_209] : k5_xboole_0(k1_xboole_0,k5_xboole_0(A_208,B_209)) = k5_xboole_0(B_209,A_208) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_2748])).

tff(c_3326,plain,(
    ! [A_1,B_2] : k5_xboole_0(k3_xboole_0(A_1,B_2),B_2) = k5_xboole_0(k1_xboole_0,k4_xboole_0(B_2,A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_537,c_3220])).

tff(c_3402,plain,(
    ! [A_1,B_2] : k5_xboole_0(k3_xboole_0(A_1,B_2),B_2) = k4_xboole_0(B_2,A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_3326])).

tff(c_22,plain,(
    ! [A_18,B_19] : k5_xboole_0(A_18,k3_xboole_0(A_18,B_19)) = k4_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_5016,plain,(
    ! [A_246,B_247,C_248] : k5_xboole_0(A_246,k5_xboole_0(k3_xboole_0(A_246,B_247),C_248)) = k5_xboole_0(k4_xboole_0(A_246,B_247),C_248) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_739])).

tff(c_5101,plain,(
    ! [A_1,B_2] : k5_xboole_0(k4_xboole_0(A_1,B_2),B_2) = k5_xboole_0(A_1,k4_xboole_0(B_2,A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3402,c_5016])).

tff(c_5238,plain,(
    ! [B_249,A_250] : k2_xboole_0(B_249,A_250) = k2_xboole_0(A_250,B_249) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1766,c_36,c_5101])).

tff(c_816,plain,(
    ! [B_17] : k5_xboole_0(B_17,B_17) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_588,c_527])).

tff(c_52,plain,(
    ! [A_61,B_62] : r1_tarski(k1_tarski(A_61),k2_tarski(A_61,B_62)) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1492,plain,(
    ! [A_171,B_172] : k3_xboole_0(k1_tarski(A_171),k2_tarski(A_171,B_172)) = k1_tarski(A_171) ),
    inference(resolution,[status(thm)],[c_52,c_226])).

tff(c_1513,plain,(
    ! [A_171,B_172] : k5_xboole_0(k1_tarski(A_171),k1_tarski(A_171)) = k4_xboole_0(k1_tarski(A_171),k2_tarski(A_171,B_172)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1492,c_22])).

tff(c_1533,plain,(
    ! [A_173,B_174] : k4_xboole_0(k1_tarski(A_173),k2_tarski(A_173,B_174)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_816,c_1513])).

tff(c_1538,plain,(
    ! [A_173,B_174] : k2_xboole_0(k2_tarski(A_173,B_174),k1_tarski(A_173)) = k5_xboole_0(k2_tarski(A_173,B_174),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1533,c_36])).

tff(c_1545,plain,(
    ! [A_173,B_174] : k2_xboole_0(k2_tarski(A_173,B_174),k1_tarski(A_173)) = k2_tarski(A_173,B_174) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1538])).

tff(c_5253,plain,(
    ! [A_173,B_174] : k2_xboole_0(k1_tarski(A_173),k2_tarski(A_173,B_174)) = k2_tarski(A_173,B_174) ),
    inference(superposition,[status(thm),theory(equality)],[c_5238,c_1545])).

tff(c_54,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),k2_tarski('#skF_3','#skF_4')) != k2_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_12970,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5253,c_54])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:31:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.93/3.08  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.93/3.09  
% 7.93/3.09  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.93/3.09  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 7.93/3.09  
% 7.93/3.09  %Foreground sorts:
% 7.93/3.09  
% 7.93/3.09  
% 7.93/3.09  %Background operators:
% 7.93/3.09  
% 7.93/3.09  
% 7.93/3.09  %Foreground operators:
% 7.93/3.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.93/3.09  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.93/3.09  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.93/3.09  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.93/3.09  tff('#skF_1', type, '#skF_1': $i > $i).
% 7.93/3.09  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.93/3.09  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 7.93/3.09  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.93/3.09  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.93/3.09  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.93/3.09  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.93/3.09  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.93/3.09  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.93/3.09  tff('#skF_3', type, '#skF_3': $i).
% 7.93/3.09  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.93/3.09  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 7.93/3.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.93/3.09  tff('#skF_4', type, '#skF_4': $i).
% 7.93/3.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.93/3.09  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.93/3.09  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.93/3.09  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.93/3.09  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 7.93/3.09  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.93/3.09  
% 7.93/3.11  tff(f_83, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 7.93/3.11  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 7.93/3.11  tff(f_69, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 7.93/3.11  tff(f_71, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 7.93/3.11  tff(f_39, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 7.93/3.11  tff(f_35, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 7.93/3.11  tff(f_53, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 7.93/3.11  tff(f_59, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.93/3.11  tff(f_65, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 7.93/3.11  tff(f_79, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 7.93/3.11  tff(f_61, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 7.93/3.11  tff(f_67, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 7.93/3.11  tff(f_81, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 7.93/3.11  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 7.93/3.11  tff(f_99, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 7.93/3.11  tff(f_102, negated_conjecture, ~(![A, B]: (k2_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_zfmisc_1)).
% 7.93/3.11  tff(c_36, plain, (![A_31, B_32]: (k5_xboole_0(A_31, k4_xboole_0(B_32, A_31))=k2_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_83])).
% 7.93/3.11  tff(c_116, plain, (![B_75, A_76]: (k5_xboole_0(B_75, A_76)=k5_xboole_0(A_76, B_75))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.93/3.11  tff(c_28, plain, (![A_24]: (k5_xboole_0(A_24, k1_xboole_0)=A_24)), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.93/3.11  tff(c_132, plain, (![A_76]: (k5_xboole_0(k1_xboole_0, A_76)=A_76)), inference(superposition, [status(thm), theory('equality')], [c_116, c_28])).
% 7.93/3.11  tff(c_30, plain, (![A_25]: (r1_xboole_0(A_25, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.93/3.11  tff(c_208, plain, (![B_79, A_80]: (r1_xboole_0(B_79, A_80) | ~r1_xboole_0(A_80, B_79))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.93/3.11  tff(c_211, plain, (![A_25]: (r1_xboole_0(k1_xboole_0, A_25))), inference(resolution, [status(thm)], [c_30, c_208])).
% 7.93/3.11  tff(c_8, plain, (![A_5]: (v1_xboole_0(A_5) | r2_hidden('#skF_1'(A_5), A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.93/3.11  tff(c_235, plain, (![A_86, B_87, C_88]: (~r1_xboole_0(A_86, B_87) | ~r2_hidden(C_88, k3_xboole_0(A_86, B_87)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.93/3.11  tff(c_324, plain, (![A_99, B_100]: (~r1_xboole_0(A_99, B_100) | v1_xboole_0(k3_xboole_0(A_99, B_100)))), inference(resolution, [status(thm)], [c_8, c_235])).
% 7.93/3.11  tff(c_20, plain, (![B_17]: (r1_tarski(B_17, B_17))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.93/3.11  tff(c_226, plain, (![A_84, B_85]: (k3_xboole_0(A_84, B_85)=A_84 | ~r1_tarski(A_84, B_85))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.93/3.11  tff(c_247, plain, (![B_89]: (k3_xboole_0(B_89, B_89)=B_89)), inference(resolution, [status(thm)], [c_20, c_226])).
% 7.93/3.11  tff(c_14, plain, (![A_11, B_12, C_15]: (~r1_xboole_0(A_11, B_12) | ~r2_hidden(C_15, k3_xboole_0(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.93/3.11  tff(c_259, plain, (![B_90, C_91]: (~r1_xboole_0(B_90, B_90) | ~r2_hidden(C_91, B_90))), inference(superposition, [status(thm), theory('equality')], [c_247, c_14])).
% 7.93/3.11  tff(c_268, plain, (![C_92]: (~r2_hidden(C_92, k1_xboole_0))), inference(resolution, [status(thm)], [c_211, c_259])).
% 7.93/3.11  tff(c_273, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_268])).
% 7.93/3.11  tff(c_32, plain, (![B_27, A_26]: (~v1_xboole_0(B_27) | B_27=A_26 | ~v1_xboole_0(A_26))), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.93/3.11  tff(c_276, plain, (![A_26]: (k1_xboole_0=A_26 | ~v1_xboole_0(A_26))), inference(resolution, [status(thm)], [c_273, c_32])).
% 7.93/3.11  tff(c_371, plain, (![A_104, B_105]: (k3_xboole_0(A_104, B_105)=k1_xboole_0 | ~r1_xboole_0(A_104, B_105))), inference(resolution, [status(thm)], [c_324, c_276])).
% 7.93/3.11  tff(c_378, plain, (![A_25]: (k3_xboole_0(k1_xboole_0, A_25)=k1_xboole_0)), inference(resolution, [status(thm)], [c_211, c_371])).
% 7.93/3.11  tff(c_508, plain, (![A_110, B_111]: (k5_xboole_0(A_110, k3_xboole_0(A_110, B_111))=k4_xboole_0(A_110, B_111))), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.93/3.11  tff(c_515, plain, (![B_111]: (k4_xboole_0(k1_xboole_0, B_111)=k3_xboole_0(k1_xboole_0, B_111))), inference(superposition, [status(thm), theory('equality')], [c_508, c_132])).
% 7.93/3.11  tff(c_539, plain, (![B_111]: (k4_xboole_0(k1_xboole_0, B_111)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_378, c_515])).
% 7.93/3.11  tff(c_277, plain, (![A_93, B_94]: (k5_xboole_0(A_93, k4_xboole_0(B_94, A_93))=k2_xboole_0(A_93, B_94))), inference(cnfTransformation, [status(thm)], [f_83])).
% 7.93/3.11  tff(c_284, plain, (![B_94]: (k4_xboole_0(B_94, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_94))), inference(superposition, [status(thm), theory('equality')], [c_277, c_132])).
% 7.93/3.11  tff(c_379, plain, (![A_25]: (k3_xboole_0(A_25, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_371])).
% 7.93/3.11  tff(c_521, plain, (![A_25]: (k5_xboole_0(A_25, k1_xboole_0)=k4_xboole_0(A_25, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_379, c_508])).
% 7.93/3.11  tff(c_577, plain, (![A_116]: (k2_xboole_0(k1_xboole_0, A_116)=A_116)), inference(demodulation, [status(thm), theory('equality')], [c_284, c_28, c_521])).
% 7.93/3.11  tff(c_26, plain, (![A_22, B_23]: (k4_xboole_0(k2_xboole_0(A_22, B_23), B_23)=k4_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.93/3.11  tff(c_583, plain, (![A_116]: (k4_xboole_0(k1_xboole_0, A_116)=k4_xboole_0(A_116, A_116))), inference(superposition, [status(thm), theory('equality')], [c_577, c_26])).
% 7.93/3.11  tff(c_588, plain, (![A_116]: (k4_xboole_0(A_116, A_116)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_539, c_583])).
% 7.93/3.11  tff(c_234, plain, (![B_17]: (k3_xboole_0(B_17, B_17)=B_17)), inference(resolution, [status(thm)], [c_20, c_226])).
% 7.93/3.11  tff(c_527, plain, (![B_17]: (k5_xboole_0(B_17, B_17)=k4_xboole_0(B_17, B_17))), inference(superposition, [status(thm), theory('equality')], [c_234, c_508])).
% 7.93/3.11  tff(c_817, plain, (![B_126]: (k5_xboole_0(B_126, B_126)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_588, c_527])).
% 7.93/3.11  tff(c_34, plain, (![A_28, B_29, C_30]: (k5_xboole_0(k5_xboole_0(A_28, B_29), C_30)=k5_xboole_0(A_28, k5_xboole_0(B_29, C_30)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 7.93/3.11  tff(c_822, plain, (![B_126, C_30]: (k5_xboole_0(B_126, k5_xboole_0(B_126, C_30))=k5_xboole_0(k1_xboole_0, C_30))), inference(superposition, [status(thm), theory('equality')], [c_817, c_34])).
% 7.93/3.11  tff(c_856, plain, (![B_127, C_128]: (k5_xboole_0(B_127, k5_xboole_0(B_127, C_128))=C_128)), inference(demodulation, [status(thm), theory('equality')], [c_132, c_822])).
% 7.93/3.11  tff(c_1760, plain, (![A_182, B_183]: (k5_xboole_0(A_182, k2_xboole_0(A_182, B_183))=k4_xboole_0(B_183, A_182))), inference(superposition, [status(thm), theory('equality')], [c_36, c_856])).
% 7.93/3.11  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.93/3.11  tff(c_905, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k5_xboole_0(B_4, A_3))=B_4)), inference(superposition, [status(thm), theory('equality')], [c_4, c_856])).
% 7.93/3.11  tff(c_924, plain, (![A_129, B_130]: (k5_xboole_0(A_129, k5_xboole_0(B_130, A_129))=B_130)), inference(superposition, [status(thm), theory('equality')], [c_4, c_856])).
% 7.93/3.11  tff(c_951, plain, (![B_4, A_3]: (k5_xboole_0(k5_xboole_0(B_4, A_3), B_4)=A_3)), inference(superposition, [status(thm), theory('equality')], [c_905, c_924])).
% 7.93/3.11  tff(c_1766, plain, (![B_183, A_182]: (k5_xboole_0(k4_xboole_0(B_183, A_182), A_182)=k2_xboole_0(A_182, B_183))), inference(superposition, [status(thm), theory('equality')], [c_1760, c_951])).
% 7.93/3.11  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.93/3.11  tff(c_537, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_508])).
% 7.93/3.11  tff(c_739, plain, (![A_123, B_124, C_125]: (k5_xboole_0(k5_xboole_0(A_123, B_124), C_125)=k5_xboole_0(A_123, k5_xboole_0(B_124, C_125)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 7.93/3.11  tff(c_2748, plain, (![B_205, A_206, B_207]: (k5_xboole_0(B_205, k5_xboole_0(A_206, B_207))=k5_xboole_0(A_206, k5_xboole_0(B_207, B_205)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_739])).
% 7.93/3.11  tff(c_3220, plain, (![A_208, B_209]: (k5_xboole_0(k1_xboole_0, k5_xboole_0(A_208, B_209))=k5_xboole_0(B_209, A_208))), inference(superposition, [status(thm), theory('equality')], [c_132, c_2748])).
% 7.93/3.11  tff(c_3326, plain, (![A_1, B_2]: (k5_xboole_0(k3_xboole_0(A_1, B_2), B_2)=k5_xboole_0(k1_xboole_0, k4_xboole_0(B_2, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_537, c_3220])).
% 7.93/3.11  tff(c_3402, plain, (![A_1, B_2]: (k5_xboole_0(k3_xboole_0(A_1, B_2), B_2)=k4_xboole_0(B_2, A_1))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_3326])).
% 7.93/3.11  tff(c_22, plain, (![A_18, B_19]: (k5_xboole_0(A_18, k3_xboole_0(A_18, B_19))=k4_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.93/3.11  tff(c_5016, plain, (![A_246, B_247, C_248]: (k5_xboole_0(A_246, k5_xboole_0(k3_xboole_0(A_246, B_247), C_248))=k5_xboole_0(k4_xboole_0(A_246, B_247), C_248))), inference(superposition, [status(thm), theory('equality')], [c_22, c_739])).
% 7.93/3.11  tff(c_5101, plain, (![A_1, B_2]: (k5_xboole_0(k4_xboole_0(A_1, B_2), B_2)=k5_xboole_0(A_1, k4_xboole_0(B_2, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_3402, c_5016])).
% 7.93/3.11  tff(c_5238, plain, (![B_249, A_250]: (k2_xboole_0(B_249, A_250)=k2_xboole_0(A_250, B_249))), inference(demodulation, [status(thm), theory('equality')], [c_1766, c_36, c_5101])).
% 7.93/3.11  tff(c_816, plain, (![B_17]: (k5_xboole_0(B_17, B_17)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_588, c_527])).
% 7.93/3.11  tff(c_52, plain, (![A_61, B_62]: (r1_tarski(k1_tarski(A_61), k2_tarski(A_61, B_62)))), inference(cnfTransformation, [status(thm)], [f_99])).
% 7.93/3.11  tff(c_1492, plain, (![A_171, B_172]: (k3_xboole_0(k1_tarski(A_171), k2_tarski(A_171, B_172))=k1_tarski(A_171))), inference(resolution, [status(thm)], [c_52, c_226])).
% 7.93/3.11  tff(c_1513, plain, (![A_171, B_172]: (k5_xboole_0(k1_tarski(A_171), k1_tarski(A_171))=k4_xboole_0(k1_tarski(A_171), k2_tarski(A_171, B_172)))), inference(superposition, [status(thm), theory('equality')], [c_1492, c_22])).
% 7.93/3.11  tff(c_1533, plain, (![A_173, B_174]: (k4_xboole_0(k1_tarski(A_173), k2_tarski(A_173, B_174))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_816, c_1513])).
% 7.93/3.11  tff(c_1538, plain, (![A_173, B_174]: (k2_xboole_0(k2_tarski(A_173, B_174), k1_tarski(A_173))=k5_xboole_0(k2_tarski(A_173, B_174), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1533, c_36])).
% 7.93/3.11  tff(c_1545, plain, (![A_173, B_174]: (k2_xboole_0(k2_tarski(A_173, B_174), k1_tarski(A_173))=k2_tarski(A_173, B_174))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1538])).
% 7.93/3.11  tff(c_5253, plain, (![A_173, B_174]: (k2_xboole_0(k1_tarski(A_173), k2_tarski(A_173, B_174))=k2_tarski(A_173, B_174))), inference(superposition, [status(thm), theory('equality')], [c_5238, c_1545])).
% 7.93/3.11  tff(c_54, plain, (k2_xboole_0(k1_tarski('#skF_3'), k2_tarski('#skF_3', '#skF_4'))!=k2_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_102])).
% 7.93/3.11  tff(c_12970, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5253, c_54])).
% 7.93/3.11  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.93/3.11  
% 7.93/3.11  Inference rules
% 7.93/3.11  ----------------------
% 7.93/3.11  #Ref     : 0
% 7.93/3.11  #Sup     : 3280
% 7.93/3.11  #Fact    : 0
% 7.93/3.11  #Define  : 0
% 7.93/3.11  #Split   : 0
% 7.93/3.11  #Chain   : 0
% 7.93/3.11  #Close   : 0
% 7.93/3.11  
% 7.93/3.11  Ordering : KBO
% 7.93/3.11  
% 7.93/3.11  Simplification rules
% 7.93/3.11  ----------------------
% 7.93/3.11  #Subsume      : 410
% 7.93/3.11  #Demod        : 3342
% 7.93/3.11  #Tautology    : 1671
% 7.93/3.11  #SimpNegUnit  : 4
% 7.93/3.11  #BackRed      : 2
% 7.93/3.11  
% 7.93/3.11  #Partial instantiations: 0
% 7.93/3.11  #Strategies tried      : 1
% 7.93/3.11  
% 7.93/3.11  Timing (in seconds)
% 7.93/3.11  ----------------------
% 7.93/3.11  Preprocessing        : 0.34
% 7.93/3.11  Parsing              : 0.18
% 7.93/3.11  CNF conversion       : 0.02
% 7.93/3.11  Main loop            : 2.01
% 7.93/3.11  Inferencing          : 0.48
% 7.93/3.11  Reduction            : 1.13
% 7.93/3.11  Demodulation         : 1.00
% 7.93/3.11  BG Simplification    : 0.06
% 7.93/3.11  Subsumption          : 0.25
% 7.93/3.11  Abstraction          : 0.10
% 7.93/3.11  MUC search           : 0.00
% 7.93/3.11  Cooper               : 0.00
% 7.93/3.11  Total                : 2.38
% 7.93/3.11  Index Insertion      : 0.00
% 7.93/3.11  Index Deletion       : 0.00
% 7.93/3.11  Index Matching       : 0.00
% 7.93/3.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
