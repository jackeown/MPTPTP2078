%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:34 EST 2020

% Result     : Theorem 7.07s
% Output     : CNFRefutation 7.07s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 395 expanded)
%              Number of leaves         :   41 ( 150 expanded)
%              Depth                    :   18
%              Number of atoms          :  100 ( 429 expanded)
%              Number of equality atoms :   81 ( 367 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_93,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k1_tarski(A),k1_tarski(B))
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(f_78,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_80,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_66,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,D,C,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_enumset1)).

tff(f_70,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_72,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_76,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_68,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(C,D,A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_enumset1)).

tff(f_45,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_47,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_64,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_70,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_58,plain,(
    ! [A_45,B_46] : k1_enumset1(A_45,A_45,B_46) = k2_tarski(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_60,plain,(
    ! [A_47,B_48,C_49] : k2_enumset1(A_47,A_47,B_48,C_49) = k1_enumset1(A_47,B_48,C_49) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_927,plain,(
    ! [B_143,D_144,C_145,A_146] : k2_enumset1(B_143,D_144,C_145,A_146) = k2_enumset1(A_146,B_143,C_145,D_144) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1900,plain,(
    ! [C_201,A_202,B_203] : k2_enumset1(C_201,A_202,B_203,A_202) = k1_enumset1(A_202,B_203,C_201) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_927])).

tff(c_50,plain,(
    ! [A_33,B_34,C_35] : k2_xboole_0(k1_tarski(A_33),k2_tarski(B_34,C_35)) = k1_enumset1(A_33,B_34,C_35) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1328,plain,(
    ! [A_161,B_162,C_163,D_164] : k2_xboole_0(k1_tarski(A_161),k1_enumset1(B_162,C_163,D_164)) = k2_enumset1(A_161,B_162,C_163,D_164) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1337,plain,(
    ! [A_161,A_45,B_46] : k2_xboole_0(k1_tarski(A_161),k2_tarski(A_45,B_46)) = k2_enumset1(A_161,A_45,A_45,B_46) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_1328])).

tff(c_1340,plain,(
    ! [A_161,A_45,B_46] : k2_enumset1(A_161,A_45,A_45,B_46) = k1_enumset1(A_161,A_45,B_46) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1337])).

tff(c_1907,plain,(
    ! [C_201,B_203] : k1_enumset1(C_201,B_203,B_203) = k1_enumset1(B_203,B_203,C_201) ),
    inference(superposition,[status(thm),theory(equality)],[c_1900,c_1340])).

tff(c_1968,plain,(
    ! [C_201,B_203] : k1_enumset1(C_201,B_203,B_203) = k2_tarski(B_203,C_201) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1907])).

tff(c_56,plain,(
    ! [A_44] : k2_tarski(A_44,A_44) = k1_tarski(A_44) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_603,plain,(
    ! [A_129,B_130,C_131] : k2_xboole_0(k1_tarski(A_129),k2_tarski(B_130,C_131)) = k1_enumset1(A_129,B_130,C_131) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_612,plain,(
    ! [A_129,A_44] : k2_xboole_0(k1_tarski(A_129),k1_tarski(A_44)) = k1_enumset1(A_129,A_44,A_44) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_603])).

tff(c_3128,plain,(
    ! [A_129,A_44] : k2_xboole_0(k1_tarski(A_129),k1_tarski(A_44)) = k2_tarski(A_44,A_129) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1968,c_612])).

tff(c_714,plain,(
    ! [C_134,D_135,A_136,B_137] : k2_enumset1(C_134,D_135,A_136,B_137) = k2_enumset1(A_136,B_137,C_134,D_135) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_749,plain,(
    ! [B_48,C_49,A_47] : k2_enumset1(B_48,C_49,A_47,A_47) = k1_enumset1(A_47,B_48,C_49) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_714])).

tff(c_1984,plain,(
    ! [C_204,B_205] : k1_enumset1(C_204,B_205,B_205) = k2_tarski(B_205,C_204) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1907])).

tff(c_52,plain,(
    ! [A_36,B_37,C_38,D_39] : k2_xboole_0(k1_tarski(A_36),k1_enumset1(B_37,C_38,D_39)) = k2_enumset1(A_36,B_37,C_38,D_39) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1996,plain,(
    ! [A_36,B_205,C_204] : k2_xboole_0(k1_tarski(A_36),k2_tarski(B_205,C_204)) = k2_enumset1(A_36,C_204,B_205,B_205) ),
    inference(superposition,[status(thm),theory(equality)],[c_1984,c_52])).

tff(c_2019,plain,(
    ! [B_205,A_36,C_204] : k1_enumset1(B_205,A_36,C_204) = k1_enumset1(A_36,B_205,C_204) ),
    inference(demodulation,[status(thm),theory(equality)],[c_749,c_50,c_1996])).

tff(c_986,plain,(
    ! [C_49,A_47,B_48] : k2_enumset1(C_49,A_47,B_48,A_47) = k1_enumset1(A_47,B_48,C_49) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_927])).

tff(c_1536,plain,(
    ! [A_177,A_178,B_179] : k2_enumset1(A_177,A_178,A_178,B_179) = k1_enumset1(A_177,A_178,B_179) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1337])).

tff(c_1543,plain,(
    ! [B_179,A_177] : k1_enumset1(B_179,A_177,B_179) = k1_enumset1(A_177,B_179,B_179) ),
    inference(superposition,[status(thm),theory(equality)],[c_1536,c_749])).

tff(c_2091,plain,(
    ! [B_215,A_216] : k1_enumset1(B_215,A_216,B_215) = k2_tarski(B_215,A_216) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1968,c_1543])).

tff(c_2107,plain,(
    ! [A_36,B_215,A_216] : k2_xboole_0(k1_tarski(A_36),k2_tarski(B_215,A_216)) = k2_enumset1(A_36,B_215,A_216,B_215) ),
    inference(superposition,[status(thm),theory(equality)],[c_2091,c_52])).

tff(c_2673,plain,(
    ! [B_245,A_246,A_247] : k1_enumset1(B_245,A_246,A_247) = k1_enumset1(A_247,B_245,A_246) ),
    inference(demodulation,[status(thm),theory(equality)],[c_986,c_50,c_2107])).

tff(c_2841,plain,(
    ! [A_36,C_204,B_205] : k1_enumset1(A_36,C_204,B_205) = k1_enumset1(A_36,B_205,C_204) ),
    inference(superposition,[status(thm),theory(equality)],[c_2019,c_2673])).

tff(c_3129,plain,(
    ! [A_267,A_268] : k2_xboole_0(k1_tarski(A_267),k1_tarski(A_268)) = k2_tarski(A_268,A_267) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1968,c_612])).

tff(c_16,plain,(
    ! [A_13] : k5_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_18,plain,(
    ! [A_14,B_15] : r1_xboole_0(k4_xboole_0(A_14,B_15),B_15) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_104,plain,(
    ! [B_86,A_87] :
      ( r1_xboole_0(B_86,A_87)
      | ~ r1_xboole_0(A_87,B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_107,plain,(
    ! [B_15,A_14] : r1_xboole_0(B_15,k4_xboole_0(A_14,B_15)) ),
    inference(resolution,[status(thm)],[c_18,c_104])).

tff(c_113,plain,(
    ! [A_90,B_91] :
      ( k3_xboole_0(A_90,B_91) = k1_xboole_0
      | ~ r1_xboole_0(A_90,B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_120,plain,(
    ! [B_15,A_14] : k3_xboole_0(B_15,k4_xboole_0(A_14,B_15)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_107,c_113])).

tff(c_190,plain,(
    ! [A_109,B_110] : k5_xboole_0(A_109,k3_xboole_0(A_109,B_110)) = k4_xboole_0(A_109,B_110) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_202,plain,(
    ! [B_15,A_14] : k4_xboole_0(B_15,k4_xboole_0(A_14,B_15)) = k5_xboole_0(B_15,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_190])).

tff(c_211,plain,(
    ! [B_15,A_14] : k4_xboole_0(B_15,k4_xboole_0(A_14,B_15)) = B_15 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_202])).

tff(c_324,plain,(
    ! [A_116,B_117] : k4_xboole_0(A_116,k4_xboole_0(A_116,B_117)) = k3_xboole_0(A_116,B_117) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_361,plain,(
    ! [B_15,A_14] : k3_xboole_0(B_15,k4_xboole_0(A_14,B_15)) = k4_xboole_0(B_15,B_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_211,c_324])).

tff(c_372,plain,(
    ! [B_15] : k4_xboole_0(B_15,B_15) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_361])).

tff(c_72,plain,(
    r1_tarski(k1_tarski('#skF_3'),k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_168,plain,(
    ! [A_103,B_104] :
      ( k3_xboole_0(A_103,B_104) = A_103
      | ~ r1_tarski(A_103,B_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_172,plain,(
    k3_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_tarski('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_168])).

tff(c_199,plain,(
    k5_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_3')) = k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_190])).

tff(c_6,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_208,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k4_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_190])).

tff(c_274,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_3')) = k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_199,c_208])).

tff(c_435,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_372,c_274])).

tff(c_20,plain,(
    ! [A_16,B_17] : k5_xboole_0(A_16,k4_xboole_0(B_17,A_16)) = k2_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_446,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_3')) = k5_xboole_0(k1_tarski('#skF_4'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_435,c_20])).

tff(c_462,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_3')) = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_446])).

tff(c_3135,plain,(
    k2_tarski('#skF_3','#skF_4') = k1_tarski('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3129,c_462])).

tff(c_3163,plain,(
    ! [A_33] : k2_xboole_0(k1_tarski(A_33),k1_tarski('#skF_4')) = k1_enumset1(A_33,'#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3135,c_50])).

tff(c_3202,plain,(
    ! [A_269] : k1_enumset1(A_269,'#skF_4','#skF_3') = k2_tarski('#skF_4',A_269) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3128,c_2841,c_3163])).

tff(c_24,plain,(
    ! [E_24,A_18,B_19] : r2_hidden(E_24,k1_enumset1(A_18,B_19,E_24)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_3254,plain,(
    ! [A_269] : r2_hidden('#skF_3',k2_tarski('#skF_4',A_269)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3202,c_24])).

tff(c_1599,plain,(
    ! [E_180,C_181,B_182,A_183] :
      ( E_180 = C_181
      | E_180 = B_182
      | E_180 = A_183
      | ~ r2_hidden(E_180,k1_enumset1(A_183,B_182,C_181)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_9106,plain,(
    ! [E_366,B_367,A_368] :
      ( E_366 = B_367
      | E_366 = A_368
      | E_366 = A_368
      | ~ r2_hidden(E_366,k2_tarski(A_368,B_367)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_1599])).

tff(c_9112,plain,(
    ! [A_269] :
      ( A_269 = '#skF_3'
      | '#skF_3' = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_3254,c_9106])).

tff(c_9155,plain,(
    '#skF_3' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_70,c_9112])).

tff(c_9147,plain,(
    ! [A_269] : A_269 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_70,c_9112])).

tff(c_9560,plain,(
    ! [A_6729] : A_6729 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_9155,c_9147])).

tff(c_9947,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_9560,c_70])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:46:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.07/2.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.07/2.56  
% 7.07/2.56  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.07/2.56  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 7.07/2.56  
% 7.07/2.56  %Foreground sorts:
% 7.07/2.56  
% 7.07/2.56  
% 7.07/2.56  %Background operators:
% 7.07/2.56  
% 7.07/2.56  
% 7.07/2.56  %Foreground operators:
% 7.07/2.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.07/2.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.07/2.56  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.07/2.56  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.07/2.56  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.07/2.56  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 7.07/2.56  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.07/2.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.07/2.56  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.07/2.56  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.07/2.56  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 7.07/2.56  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.07/2.56  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.07/2.56  tff('#skF_3', type, '#skF_3': $i).
% 7.07/2.56  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.07/2.56  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 7.07/2.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.07/2.56  tff('#skF_4', type, '#skF_4': $i).
% 7.07/2.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.07/2.56  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.07/2.56  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.07/2.56  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 7.07/2.56  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 7.07/2.56  
% 7.07/2.58  tff(f_93, negated_conjecture, ~(![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 7.07/2.58  tff(f_78, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 7.07/2.58  tff(f_80, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 7.07/2.58  tff(f_66, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, D, C, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_enumset1)).
% 7.07/2.58  tff(f_70, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_enumset1)).
% 7.07/2.58  tff(f_72, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_enumset1)).
% 7.07/2.58  tff(f_76, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 7.07/2.58  tff(f_68, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(C, D, A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t118_enumset1)).
% 7.07/2.58  tff(f_45, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 7.07/2.58  tff(f_47, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 7.07/2.58  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 7.07/2.58  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 7.07/2.58  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 7.07/2.58  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 7.07/2.58  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 7.07/2.58  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 7.07/2.58  tff(f_49, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 7.07/2.58  tff(f_64, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 7.07/2.58  tff(c_70, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_93])).
% 7.07/2.58  tff(c_58, plain, (![A_45, B_46]: (k1_enumset1(A_45, A_45, B_46)=k2_tarski(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.07/2.58  tff(c_60, plain, (![A_47, B_48, C_49]: (k2_enumset1(A_47, A_47, B_48, C_49)=k1_enumset1(A_47, B_48, C_49))), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.07/2.58  tff(c_927, plain, (![B_143, D_144, C_145, A_146]: (k2_enumset1(B_143, D_144, C_145, A_146)=k2_enumset1(A_146, B_143, C_145, D_144))), inference(cnfTransformation, [status(thm)], [f_66])).
% 7.07/2.58  tff(c_1900, plain, (![C_201, A_202, B_203]: (k2_enumset1(C_201, A_202, B_203, A_202)=k1_enumset1(A_202, B_203, C_201))), inference(superposition, [status(thm), theory('equality')], [c_60, c_927])).
% 7.07/2.58  tff(c_50, plain, (![A_33, B_34, C_35]: (k2_xboole_0(k1_tarski(A_33), k2_tarski(B_34, C_35))=k1_enumset1(A_33, B_34, C_35))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.07/2.58  tff(c_1328, plain, (![A_161, B_162, C_163, D_164]: (k2_xboole_0(k1_tarski(A_161), k1_enumset1(B_162, C_163, D_164))=k2_enumset1(A_161, B_162, C_163, D_164))), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.07/2.58  tff(c_1337, plain, (![A_161, A_45, B_46]: (k2_xboole_0(k1_tarski(A_161), k2_tarski(A_45, B_46))=k2_enumset1(A_161, A_45, A_45, B_46))), inference(superposition, [status(thm), theory('equality')], [c_58, c_1328])).
% 7.07/2.58  tff(c_1340, plain, (![A_161, A_45, B_46]: (k2_enumset1(A_161, A_45, A_45, B_46)=k1_enumset1(A_161, A_45, B_46))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1337])).
% 7.07/2.58  tff(c_1907, plain, (![C_201, B_203]: (k1_enumset1(C_201, B_203, B_203)=k1_enumset1(B_203, B_203, C_201))), inference(superposition, [status(thm), theory('equality')], [c_1900, c_1340])).
% 7.07/2.58  tff(c_1968, plain, (![C_201, B_203]: (k1_enumset1(C_201, B_203, B_203)=k2_tarski(B_203, C_201))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1907])).
% 7.07/2.58  tff(c_56, plain, (![A_44]: (k2_tarski(A_44, A_44)=k1_tarski(A_44))), inference(cnfTransformation, [status(thm)], [f_76])).
% 7.07/2.58  tff(c_603, plain, (![A_129, B_130, C_131]: (k2_xboole_0(k1_tarski(A_129), k2_tarski(B_130, C_131))=k1_enumset1(A_129, B_130, C_131))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.07/2.58  tff(c_612, plain, (![A_129, A_44]: (k2_xboole_0(k1_tarski(A_129), k1_tarski(A_44))=k1_enumset1(A_129, A_44, A_44))), inference(superposition, [status(thm), theory('equality')], [c_56, c_603])).
% 7.07/2.58  tff(c_3128, plain, (![A_129, A_44]: (k2_xboole_0(k1_tarski(A_129), k1_tarski(A_44))=k2_tarski(A_44, A_129))), inference(demodulation, [status(thm), theory('equality')], [c_1968, c_612])).
% 7.07/2.58  tff(c_714, plain, (![C_134, D_135, A_136, B_137]: (k2_enumset1(C_134, D_135, A_136, B_137)=k2_enumset1(A_136, B_137, C_134, D_135))), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.07/2.58  tff(c_749, plain, (![B_48, C_49, A_47]: (k2_enumset1(B_48, C_49, A_47, A_47)=k1_enumset1(A_47, B_48, C_49))), inference(superposition, [status(thm), theory('equality')], [c_60, c_714])).
% 7.07/2.58  tff(c_1984, plain, (![C_204, B_205]: (k1_enumset1(C_204, B_205, B_205)=k2_tarski(B_205, C_204))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1907])).
% 7.07/2.58  tff(c_52, plain, (![A_36, B_37, C_38, D_39]: (k2_xboole_0(k1_tarski(A_36), k1_enumset1(B_37, C_38, D_39))=k2_enumset1(A_36, B_37, C_38, D_39))), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.07/2.58  tff(c_1996, plain, (![A_36, B_205, C_204]: (k2_xboole_0(k1_tarski(A_36), k2_tarski(B_205, C_204))=k2_enumset1(A_36, C_204, B_205, B_205))), inference(superposition, [status(thm), theory('equality')], [c_1984, c_52])).
% 7.07/2.58  tff(c_2019, plain, (![B_205, A_36, C_204]: (k1_enumset1(B_205, A_36, C_204)=k1_enumset1(A_36, B_205, C_204))), inference(demodulation, [status(thm), theory('equality')], [c_749, c_50, c_1996])).
% 7.07/2.58  tff(c_986, plain, (![C_49, A_47, B_48]: (k2_enumset1(C_49, A_47, B_48, A_47)=k1_enumset1(A_47, B_48, C_49))), inference(superposition, [status(thm), theory('equality')], [c_60, c_927])).
% 7.07/2.58  tff(c_1536, plain, (![A_177, A_178, B_179]: (k2_enumset1(A_177, A_178, A_178, B_179)=k1_enumset1(A_177, A_178, B_179))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1337])).
% 7.07/2.58  tff(c_1543, plain, (![B_179, A_177]: (k1_enumset1(B_179, A_177, B_179)=k1_enumset1(A_177, B_179, B_179))), inference(superposition, [status(thm), theory('equality')], [c_1536, c_749])).
% 7.07/2.58  tff(c_2091, plain, (![B_215, A_216]: (k1_enumset1(B_215, A_216, B_215)=k2_tarski(B_215, A_216))), inference(demodulation, [status(thm), theory('equality')], [c_1968, c_1543])).
% 7.07/2.58  tff(c_2107, plain, (![A_36, B_215, A_216]: (k2_xboole_0(k1_tarski(A_36), k2_tarski(B_215, A_216))=k2_enumset1(A_36, B_215, A_216, B_215))), inference(superposition, [status(thm), theory('equality')], [c_2091, c_52])).
% 7.07/2.58  tff(c_2673, plain, (![B_245, A_246, A_247]: (k1_enumset1(B_245, A_246, A_247)=k1_enumset1(A_247, B_245, A_246))), inference(demodulation, [status(thm), theory('equality')], [c_986, c_50, c_2107])).
% 7.07/2.58  tff(c_2841, plain, (![A_36, C_204, B_205]: (k1_enumset1(A_36, C_204, B_205)=k1_enumset1(A_36, B_205, C_204))), inference(superposition, [status(thm), theory('equality')], [c_2019, c_2673])).
% 7.07/2.58  tff(c_3129, plain, (![A_267, A_268]: (k2_xboole_0(k1_tarski(A_267), k1_tarski(A_268))=k2_tarski(A_268, A_267))), inference(demodulation, [status(thm), theory('equality')], [c_1968, c_612])).
% 7.07/2.58  tff(c_16, plain, (![A_13]: (k5_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.07/2.58  tff(c_18, plain, (![A_14, B_15]: (r1_xboole_0(k4_xboole_0(A_14, B_15), B_15))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.07/2.58  tff(c_104, plain, (![B_86, A_87]: (r1_xboole_0(B_86, A_87) | ~r1_xboole_0(A_87, B_86))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.07/2.58  tff(c_107, plain, (![B_15, A_14]: (r1_xboole_0(B_15, k4_xboole_0(A_14, B_15)))), inference(resolution, [status(thm)], [c_18, c_104])).
% 7.07/2.58  tff(c_113, plain, (![A_90, B_91]: (k3_xboole_0(A_90, B_91)=k1_xboole_0 | ~r1_xboole_0(A_90, B_91))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.07/2.58  tff(c_120, plain, (![B_15, A_14]: (k3_xboole_0(B_15, k4_xboole_0(A_14, B_15))=k1_xboole_0)), inference(resolution, [status(thm)], [c_107, c_113])).
% 7.07/2.58  tff(c_190, plain, (![A_109, B_110]: (k5_xboole_0(A_109, k3_xboole_0(A_109, B_110))=k4_xboole_0(A_109, B_110))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.07/2.58  tff(c_202, plain, (![B_15, A_14]: (k4_xboole_0(B_15, k4_xboole_0(A_14, B_15))=k5_xboole_0(B_15, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_120, c_190])).
% 7.07/2.58  tff(c_211, plain, (![B_15, A_14]: (k4_xboole_0(B_15, k4_xboole_0(A_14, B_15))=B_15)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_202])).
% 7.07/2.58  tff(c_324, plain, (![A_116, B_117]: (k4_xboole_0(A_116, k4_xboole_0(A_116, B_117))=k3_xboole_0(A_116, B_117))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.07/2.58  tff(c_361, plain, (![B_15, A_14]: (k3_xboole_0(B_15, k4_xboole_0(A_14, B_15))=k4_xboole_0(B_15, B_15))), inference(superposition, [status(thm), theory('equality')], [c_211, c_324])).
% 7.07/2.58  tff(c_372, plain, (![B_15]: (k4_xboole_0(B_15, B_15)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_120, c_361])).
% 7.07/2.58  tff(c_72, plain, (r1_tarski(k1_tarski('#skF_3'), k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 7.07/2.58  tff(c_168, plain, (![A_103, B_104]: (k3_xboole_0(A_103, B_104)=A_103 | ~r1_tarski(A_103, B_104))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.07/2.58  tff(c_172, plain, (k3_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_tarski('#skF_3')), inference(resolution, [status(thm)], [c_72, c_168])).
% 7.07/2.58  tff(c_199, plain, (k5_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_3'))=k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_172, c_190])).
% 7.07/2.58  tff(c_6, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.07/2.58  tff(c_208, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k4_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_6, c_190])).
% 7.07/2.58  tff(c_274, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_3'))=k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_199, c_208])).
% 7.07/2.58  tff(c_435, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_372, c_274])).
% 7.07/2.58  tff(c_20, plain, (![A_16, B_17]: (k5_xboole_0(A_16, k4_xboole_0(B_17, A_16))=k2_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.07/2.58  tff(c_446, plain, (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_3'))=k5_xboole_0(k1_tarski('#skF_4'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_435, c_20])).
% 7.07/2.58  tff(c_462, plain, (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_3'))=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_446])).
% 7.07/2.58  tff(c_3135, plain, (k2_tarski('#skF_3', '#skF_4')=k1_tarski('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3129, c_462])).
% 7.07/2.58  tff(c_3163, plain, (![A_33]: (k2_xboole_0(k1_tarski(A_33), k1_tarski('#skF_4'))=k1_enumset1(A_33, '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_3135, c_50])).
% 7.07/2.58  tff(c_3202, plain, (![A_269]: (k1_enumset1(A_269, '#skF_4', '#skF_3')=k2_tarski('#skF_4', A_269))), inference(demodulation, [status(thm), theory('equality')], [c_3128, c_2841, c_3163])).
% 7.07/2.58  tff(c_24, plain, (![E_24, A_18, B_19]: (r2_hidden(E_24, k1_enumset1(A_18, B_19, E_24)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.07/2.58  tff(c_3254, plain, (![A_269]: (r2_hidden('#skF_3', k2_tarski('#skF_4', A_269)))), inference(superposition, [status(thm), theory('equality')], [c_3202, c_24])).
% 7.07/2.58  tff(c_1599, plain, (![E_180, C_181, B_182, A_183]: (E_180=C_181 | E_180=B_182 | E_180=A_183 | ~r2_hidden(E_180, k1_enumset1(A_183, B_182, C_181)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.07/2.58  tff(c_9106, plain, (![E_366, B_367, A_368]: (E_366=B_367 | E_366=A_368 | E_366=A_368 | ~r2_hidden(E_366, k2_tarski(A_368, B_367)))), inference(superposition, [status(thm), theory('equality')], [c_58, c_1599])).
% 7.07/2.58  tff(c_9112, plain, (![A_269]: (A_269='#skF_3' | '#skF_3'='#skF_4')), inference(resolution, [status(thm)], [c_3254, c_9106])).
% 7.07/2.58  tff(c_9155, plain, ('#skF_3'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_70, c_70, c_9112])).
% 7.07/2.58  tff(c_9147, plain, (![A_269]: (A_269='#skF_3')), inference(negUnitSimplification, [status(thm)], [c_70, c_70, c_9112])).
% 7.07/2.58  tff(c_9560, plain, (![A_6729]: (A_6729='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_9155, c_9147])).
% 7.07/2.58  tff(c_9947, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_9560, c_70])).
% 7.07/2.58  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.07/2.58  
% 7.07/2.58  Inference rules
% 7.07/2.58  ----------------------
% 7.07/2.58  #Ref     : 0
% 7.07/2.58  #Sup     : 2499
% 7.07/2.58  #Fact    : 1
% 7.07/2.58  #Define  : 0
% 7.07/2.58  #Split   : 1
% 7.07/2.58  #Chain   : 0
% 7.07/2.58  #Close   : 0
% 7.07/2.58  
% 7.07/2.58  Ordering : KBO
% 7.07/2.58  
% 7.07/2.58  Simplification rules
% 7.07/2.58  ----------------------
% 7.07/2.58  #Subsume      : 491
% 7.07/2.58  #Demod        : 2030
% 7.07/2.58  #Tautology    : 1471
% 7.07/2.58  #SimpNegUnit  : 12
% 7.07/2.58  #BackRed      : 7
% 7.07/2.58  
% 7.07/2.58  #Partial instantiations: 122
% 7.07/2.58  #Strategies tried      : 1
% 7.07/2.58  
% 7.07/2.58  Timing (in seconds)
% 7.07/2.58  ----------------------
% 7.07/2.58  Preprocessing        : 0.36
% 7.07/2.58  Parsing              : 0.19
% 7.07/2.58  CNF conversion       : 0.03
% 7.07/2.58  Main loop            : 1.46
% 7.07/2.59  Inferencing          : 0.48
% 7.07/2.59  Reduction            : 0.65
% 7.07/2.59  Demodulation         : 0.55
% 7.07/2.59  BG Simplification    : 0.05
% 7.07/2.59  Subsumption          : 0.21
% 7.07/2.59  Abstraction          : 0.06
% 7.07/2.59  MUC search           : 0.00
% 7.07/2.59  Cooper               : 0.00
% 7.07/2.59  Total                : 1.86
% 7.39/2.59  Index Insertion      : 0.00
% 7.39/2.59  Index Deletion       : 0.00
% 7.39/2.59  Index Matching       : 0.00
% 7.39/2.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
