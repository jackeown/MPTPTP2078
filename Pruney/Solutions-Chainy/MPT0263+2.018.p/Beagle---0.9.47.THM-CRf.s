%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:16 EST 2020

% Result     : Theorem 8.59s
% Output     : CNFRefutation 8.59s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 466 expanded)
%              Number of leaves         :   27 ( 168 expanded)
%              Depth                    :   21
%              Number of atoms          :  161 ( 857 expanded)
%              Number of equality atoms :   66 ( 390 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_69,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_xboole_0(k1_tarski(A),B)
        | k3_xboole_0(k1_tarski(A),B) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_39,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_64,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l35_zfmisc_1)).

tff(f_56,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_124,plain,(
    ! [A_39,B_40] :
      ( r1_xboole_0(A_39,B_40)
      | k4_xboole_0(A_39,B_40) != A_39 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_60,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_5'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_132,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') != k1_tarski('#skF_5') ),
    inference(resolution,[status(thm)],[c_124,c_60])).

tff(c_1124,plain,(
    ! [A_125,B_126,C_127] :
      ( r2_hidden('#skF_1'(A_125,B_126,C_127),A_125)
      | r2_hidden('#skF_2'(A_125,B_126,C_127),C_127)
      | k4_xboole_0(A_125,B_126) = C_127 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_16,plain,(
    ! [A_3,B_4,C_5] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4,C_5),C_5)
      | r2_hidden('#skF_2'(A_3,B_4,C_5),C_5)
      | k4_xboole_0(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1230,plain,(
    ! [A_125,B_126] :
      ( r2_hidden('#skF_2'(A_125,B_126,A_125),A_125)
      | k4_xboole_0(A_125,B_126) = A_125 ) ),
    inference(resolution,[status(thm)],[c_1124,c_16])).

tff(c_14,plain,(
    ! [A_3,B_4,C_5] :
      ( r2_hidden('#skF_1'(A_3,B_4,C_5),A_3)
      | r2_hidden('#skF_2'(A_3,B_4,C_5),B_4)
      | ~ r2_hidden('#skF_2'(A_3,B_4,C_5),A_3)
      | k4_xboole_0(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1929,plain,(
    ! [A_151,B_152,C_153] :
      ( ~ r2_hidden('#skF_1'(A_151,B_152,C_153),C_153)
      | r2_hidden('#skF_2'(A_151,B_152,C_153),B_152)
      | ~ r2_hidden('#skF_2'(A_151,B_152,C_153),A_151)
      | k4_xboole_0(A_151,B_152) = C_153 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_3526,plain,(
    ! [A_213,B_214] :
      ( r2_hidden('#skF_2'(A_213,B_214,A_213),B_214)
      | ~ r2_hidden('#skF_2'(A_213,B_214,A_213),A_213)
      | k4_xboole_0(A_213,B_214) = A_213 ) ),
    inference(resolution,[status(thm)],[c_14,c_1929])).

tff(c_3559,plain,(
    ! [A_125,B_126] :
      ( r2_hidden('#skF_2'(A_125,B_126,A_125),B_126)
      | k4_xboole_0(A_125,B_126) = A_125 ) ),
    inference(resolution,[status(thm)],[c_1230,c_3526])).

tff(c_22,plain,(
    ! [A_9] : k4_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_163,plain,(
    ! [A_46,B_47] :
      ( r2_hidden(A_46,B_47)
      | k4_xboole_0(k1_tarski(A_46),B_47) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_170,plain,(
    ! [A_46] :
      ( r2_hidden(A_46,k1_xboole_0)
      | k1_tarski(A_46) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_163])).

tff(c_178,plain,(
    ! [D_49,B_50,A_51] :
      ( ~ r2_hidden(D_49,B_50)
      | ~ r2_hidden(D_49,k4_xboole_0(A_51,B_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_185,plain,(
    ! [D_52,A_53] :
      ( ~ r2_hidden(D_52,k1_xboole_0)
      | ~ r2_hidden(D_52,A_53) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_178])).

tff(c_189,plain,(
    ! [A_54,A_55] :
      ( ~ r2_hidden(A_54,A_55)
      | k1_tarski(A_54) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_170,c_185])).

tff(c_202,plain,(
    ! [A_46] : k1_tarski(A_46) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_170,c_189])).

tff(c_142,plain,(
    ! [A_43,B_44] :
      ( k4_xboole_0(k1_tarski(A_43),B_44) = k1_xboole_0
      | ~ r2_hidden(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_152,plain,(
    ! [A_43] :
      ( k1_tarski(A_43) = k1_xboole_0
      | ~ r2_hidden(A_43,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_22])).

tff(c_206,plain,(
    ! [A_43] : ~ r2_hidden(A_43,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_202,c_152])).

tff(c_1256,plain,(
    ! [A_128,B_129] :
      ( r2_hidden('#skF_2'(A_128,B_129,A_128),A_128)
      | k4_xboole_0(A_128,B_129) = A_128 ) ),
    inference(resolution,[status(thm)],[c_1124,c_16])).

tff(c_1317,plain,(
    ! [B_129] : k4_xboole_0(k1_xboole_0,B_129) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1256,c_206])).

tff(c_8,plain,(
    ! [D_8,A_3,B_4] :
      ( r2_hidden(D_8,A_3)
      | ~ r2_hidden(D_8,k4_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4084,plain,(
    ! [A_228,B_229,A_230,B_231] :
      ( r2_hidden('#skF_2'(A_228,B_229,k4_xboole_0(A_230,B_231)),A_230)
      | r2_hidden('#skF_1'(A_228,B_229,k4_xboole_0(A_230,B_231)),A_228)
      | k4_xboole_0(A_230,B_231) = k4_xboole_0(A_228,B_229) ) ),
    inference(resolution,[status(thm)],[c_1124,c_8])).

tff(c_4185,plain,(
    ! [B_229,A_230,B_231] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_229,k4_xboole_0(A_230,B_231)),A_230)
      | k4_xboole_0(k1_xboole_0,B_229) = k4_xboole_0(A_230,B_231) ) ),
    inference(resolution,[status(thm)],[c_4084,c_206])).

tff(c_4268,plain,(
    ! [B_229,A_230,B_231] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_229,k4_xboole_0(A_230,B_231)),A_230)
      | k4_xboole_0(A_230,B_231) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1317,c_4185])).

tff(c_1242,plain,(
    ! [B_126,C_127] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_126,C_127),C_127)
      | k4_xboole_0(k1_xboole_0,B_126) = C_127 ) ),
    inference(resolution,[status(thm)],[c_1124,c_206])).

tff(c_1942,plain,(
    ! [B_126,C_127] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_126,C_127),C_127)
      | k1_xboole_0 = C_127 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1317,c_1242])).

tff(c_48,plain,(
    ! [A_20] : k2_tarski(A_20,A_20) = k1_tarski(A_20) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_80,plain,(
    ! [D_30,B_31] : r2_hidden(D_30,k2_tarski(D_30,B_31)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_83,plain,(
    ! [A_20] : r2_hidden(A_20,k1_tarski(A_20)) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_80])).

tff(c_4,plain,(
    ! [D_8,A_3,B_4] :
      ( r2_hidden(D_8,k4_xboole_0(A_3,B_4))
      | r2_hidden(D_8,B_4)
      | ~ r2_hidden(D_8,A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_56,plain,(
    ! [A_26,B_27] :
      ( k4_xboole_0(k1_tarski(A_26),B_27) = k1_xboole_0
      | ~ r2_hidden(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_209,plain,(
    ! [A_58,B_59] : k4_xboole_0(A_58,k4_xboole_0(A_58,B_59)) = k3_xboole_0(A_58,B_59) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2058,plain,(
    ! [A_161,B_162] :
      ( k3_xboole_0(k1_tarski(A_161),B_162) = k1_xboole_0
      | ~ r2_hidden(A_161,k4_xboole_0(k1_tarski(A_161),B_162)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_209])).

tff(c_2074,plain,(
    ! [D_8,B_4] :
      ( k3_xboole_0(k1_tarski(D_8),B_4) = k1_xboole_0
      | r2_hidden(D_8,B_4)
      | ~ r2_hidden(D_8,k1_tarski(D_8)) ) ),
    inference(resolution,[status(thm)],[c_4,c_2058])).

tff(c_2090,plain,(
    ! [D_8,B_4] :
      ( k3_xboole_0(k1_tarski(D_8),B_4) = k1_xboole_0
      | r2_hidden(D_8,B_4) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_2074])).

tff(c_24,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k4_xboole_0(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_489,plain,(
    ! [D_84,A_85,B_86] :
      ( r2_hidden(D_84,k4_xboole_0(A_85,B_86))
      | r2_hidden(D_84,B_86)
      | ~ r2_hidden(D_84,A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2949,plain,(
    ! [D_189,A_190,B_191] :
      ( r2_hidden(D_189,k3_xboole_0(A_190,B_191))
      | r2_hidden(D_189,k4_xboole_0(A_190,B_191))
      | ~ r2_hidden(D_189,A_190) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_489])).

tff(c_6,plain,(
    ! [D_8,B_4,A_3] :
      ( ~ r2_hidden(D_8,B_4)
      | ~ r2_hidden(D_8,k4_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_3164,plain,(
    ! [D_196,B_197,A_198] :
      ( ~ r2_hidden(D_196,B_197)
      | r2_hidden(D_196,k3_xboole_0(A_198,B_197))
      | ~ r2_hidden(D_196,A_198) ) ),
    inference(resolution,[status(thm)],[c_2949,c_6])).

tff(c_3217,plain,(
    ! [D_196,B_4,D_8] :
      ( ~ r2_hidden(D_196,B_4)
      | r2_hidden(D_196,k1_xboole_0)
      | ~ r2_hidden(D_196,k1_tarski(D_8))
      | r2_hidden(D_8,B_4) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2090,c_3164])).

tff(c_3260,plain,(
    ! [D_199,B_200,D_201] :
      ( ~ r2_hidden(D_199,B_200)
      | ~ r2_hidden(D_199,k1_tarski(D_201))
      | r2_hidden(D_201,B_200) ) ),
    inference(negUnitSimplification,[status(thm)],[c_206,c_3217])).

tff(c_8449,plain,(
    ! [B_323,C_324,D_325] :
      ( ~ r2_hidden('#skF_2'(k1_xboole_0,B_323,C_324),k1_tarski(D_325))
      | r2_hidden(D_325,C_324)
      | k1_xboole_0 = C_324 ) ),
    inference(resolution,[status(thm)],[c_1942,c_3260])).

tff(c_8820,plain,(
    ! [D_332,B_333] :
      ( r2_hidden(D_332,k4_xboole_0(k1_tarski(D_332),B_333))
      | k4_xboole_0(k1_tarski(D_332),B_333) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4268,c_8449])).

tff(c_239,plain,(
    ! [A_26,B_59] :
      ( k3_xboole_0(k1_tarski(A_26),B_59) = k1_xboole_0
      | ~ r2_hidden(A_26,k4_xboole_0(k1_tarski(A_26),B_59)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_209])).

tff(c_8889,plain,(
    ! [D_334,B_335] :
      ( k3_xboole_0(k1_tarski(D_334),B_335) = k1_xboole_0
      | k4_xboole_0(k1_tarski(D_334),B_335) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8820,c_239])).

tff(c_9012,plain,(
    ! [D_334,B_335] :
      ( k4_xboole_0(k1_tarski(D_334),k1_xboole_0) = k3_xboole_0(k1_tarski(D_334),B_335)
      | k3_xboole_0(k1_tarski(D_334),B_335) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8889,c_24])).

tff(c_9559,plain,(
    ! [D_344,B_345] :
      ( k3_xboole_0(k1_tarski(D_344),B_345) = k1_tarski(D_344)
      | k3_xboole_0(k1_tarski(D_344),B_345) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_9012])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10004,plain,(
    ! [B_348,D_349] :
      ( k3_xboole_0(B_348,k1_tarski(D_349)) = k1_tarski(D_349)
      | k3_xboole_0(k1_tarski(D_349),B_348) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9559,c_2])).

tff(c_1943,plain,(
    ! [B_154,C_155] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_154,C_155),C_155)
      | k1_xboole_0 = C_155 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1317,c_1242])).

tff(c_286,plain,(
    ! [D_61,A_62,B_63] :
      ( r2_hidden(D_61,A_62)
      | ~ r2_hidden(D_61,k4_xboole_0(A_62,B_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_312,plain,(
    ! [D_65,A_66,B_67] :
      ( r2_hidden(D_65,A_66)
      | ~ r2_hidden(D_65,k3_xboole_0(A_66,B_67)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_286])).

tff(c_324,plain,(
    ! [D_65,B_2,A_1] :
      ( r2_hidden(D_65,B_2)
      | ~ r2_hidden(D_65,k3_xboole_0(A_1,B_2)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_312])).

tff(c_1987,plain,(
    ! [B_154,A_1,B_2] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_154,k3_xboole_0(A_1,B_2)),B_2)
      | k3_xboole_0(A_1,B_2) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1943,c_324])).

tff(c_8533,plain,(
    ! [D_326,A_327] :
      ( r2_hidden(D_326,k3_xboole_0(A_327,k1_tarski(D_326)))
      | k3_xboole_0(A_327,k1_tarski(D_326)) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1987,c_8449])).

tff(c_8585,plain,(
    ! [D_326,A_1] :
      ( r2_hidden(D_326,k3_xboole_0(k1_tarski(D_326),A_1))
      | k3_xboole_0(A_1,k1_tarski(D_326)) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_8533])).

tff(c_10181,plain,(
    ! [D_349,B_348] :
      ( r2_hidden(D_349,k1_xboole_0)
      | k3_xboole_0(B_348,k1_tarski(D_349)) = k1_xboole_0
      | k3_xboole_0(B_348,k1_tarski(D_349)) = k1_tarski(D_349) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10004,c_8585])).

tff(c_11102,plain,(
    ! [B_352,D_353] :
      ( k3_xboole_0(B_352,k1_tarski(D_353)) = k1_xboole_0
      | k3_xboole_0(B_352,k1_tarski(D_353)) = k1_tarski(D_353) ) ),
    inference(negUnitSimplification,[status(thm)],[c_206,c_10181])).

tff(c_58,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),'#skF_6') != k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_61,plain,(
    k3_xboole_0('#skF_6',k1_tarski('#skF_5')) != k1_tarski('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_58])).

tff(c_11361,plain,(
    k3_xboole_0('#skF_6',k1_tarski('#skF_5')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_11102,c_61])).

tff(c_3235,plain,(
    ! [D_196,B_2,A_1] :
      ( ~ r2_hidden(D_196,B_2)
      | r2_hidden(D_196,k3_xboole_0(B_2,A_1))
      | ~ r2_hidden(D_196,A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_3164])).

tff(c_11512,plain,(
    ! [D_196] :
      ( ~ r2_hidden(D_196,'#skF_6')
      | r2_hidden(D_196,k1_xboole_0)
      | ~ r2_hidden(D_196,k1_tarski('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11361,c_3235])).

tff(c_11634,plain,(
    ! [D_358] :
      ( ~ r2_hidden(D_358,'#skF_6')
      | ~ r2_hidden(D_358,k1_tarski('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_206,c_11512])).

tff(c_14034,plain,(
    ! [B_392] :
      ( ~ r2_hidden('#skF_2'(k1_tarski('#skF_5'),B_392,k1_tarski('#skF_5')),'#skF_6')
      | k4_xboole_0(k1_tarski('#skF_5'),B_392) = k1_tarski('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1230,c_11634])).

tff(c_14056,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') = k1_tarski('#skF_5') ),
    inference(resolution,[status(thm)],[c_3559,c_14034])).

tff(c_14066,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_132,c_132,c_14056])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:08:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.59/3.01  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.59/3.02  
% 8.59/3.02  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.59/3.02  %$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 8.59/3.02  
% 8.59/3.02  %Foreground sorts:
% 8.59/3.02  
% 8.59/3.02  
% 8.59/3.02  %Background operators:
% 8.59/3.02  
% 8.59/3.02  
% 8.59/3.02  %Foreground operators:
% 8.59/3.02  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 8.59/3.02  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.59/3.02  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.59/3.02  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.59/3.02  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.59/3.02  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.59/3.02  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 8.59/3.02  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.59/3.02  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.59/3.02  tff('#skF_5', type, '#skF_5': $i).
% 8.59/3.02  tff('#skF_6', type, '#skF_6': $i).
% 8.59/3.02  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.59/3.02  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.59/3.02  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 8.59/3.02  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.59/3.02  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 8.59/3.02  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.59/3.02  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.59/3.02  
% 8.59/3.04  tff(f_45, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 8.59/3.04  tff(f_69, negated_conjecture, ~(![A, B]: (r1_xboole_0(k1_tarski(A), B) | (k3_xboole_0(k1_tarski(A), B) = k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_zfmisc_1)).
% 8.59/3.04  tff(f_37, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 8.59/3.04  tff(f_39, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 8.59/3.04  tff(f_64, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l35_zfmisc_1)).
% 8.59/3.04  tff(f_56, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 8.59/3.04  tff(f_54, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 8.59/3.04  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 8.59/3.04  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 8.59/3.04  tff(c_124, plain, (![A_39, B_40]: (r1_xboole_0(A_39, B_40) | k4_xboole_0(A_39, B_40)!=A_39)), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.59/3.04  tff(c_60, plain, (~r1_xboole_0(k1_tarski('#skF_5'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_69])).
% 8.59/3.04  tff(c_132, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')!=k1_tarski('#skF_5')), inference(resolution, [status(thm)], [c_124, c_60])).
% 8.59/3.04  tff(c_1124, plain, (![A_125, B_126, C_127]: (r2_hidden('#skF_1'(A_125, B_126, C_127), A_125) | r2_hidden('#skF_2'(A_125, B_126, C_127), C_127) | k4_xboole_0(A_125, B_126)=C_127)), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.59/3.04  tff(c_16, plain, (![A_3, B_4, C_5]: (~r2_hidden('#skF_1'(A_3, B_4, C_5), C_5) | r2_hidden('#skF_2'(A_3, B_4, C_5), C_5) | k4_xboole_0(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.59/3.04  tff(c_1230, plain, (![A_125, B_126]: (r2_hidden('#skF_2'(A_125, B_126, A_125), A_125) | k4_xboole_0(A_125, B_126)=A_125)), inference(resolution, [status(thm)], [c_1124, c_16])).
% 8.59/3.04  tff(c_14, plain, (![A_3, B_4, C_5]: (r2_hidden('#skF_1'(A_3, B_4, C_5), A_3) | r2_hidden('#skF_2'(A_3, B_4, C_5), B_4) | ~r2_hidden('#skF_2'(A_3, B_4, C_5), A_3) | k4_xboole_0(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.59/3.04  tff(c_1929, plain, (![A_151, B_152, C_153]: (~r2_hidden('#skF_1'(A_151, B_152, C_153), C_153) | r2_hidden('#skF_2'(A_151, B_152, C_153), B_152) | ~r2_hidden('#skF_2'(A_151, B_152, C_153), A_151) | k4_xboole_0(A_151, B_152)=C_153)), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.59/3.04  tff(c_3526, plain, (![A_213, B_214]: (r2_hidden('#skF_2'(A_213, B_214, A_213), B_214) | ~r2_hidden('#skF_2'(A_213, B_214, A_213), A_213) | k4_xboole_0(A_213, B_214)=A_213)), inference(resolution, [status(thm)], [c_14, c_1929])).
% 8.59/3.04  tff(c_3559, plain, (![A_125, B_126]: (r2_hidden('#skF_2'(A_125, B_126, A_125), B_126) | k4_xboole_0(A_125, B_126)=A_125)), inference(resolution, [status(thm)], [c_1230, c_3526])).
% 8.59/3.04  tff(c_22, plain, (![A_9]: (k4_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.59/3.04  tff(c_163, plain, (![A_46, B_47]: (r2_hidden(A_46, B_47) | k4_xboole_0(k1_tarski(A_46), B_47)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.59/3.04  tff(c_170, plain, (![A_46]: (r2_hidden(A_46, k1_xboole_0) | k1_tarski(A_46)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_22, c_163])).
% 8.59/3.04  tff(c_178, plain, (![D_49, B_50, A_51]: (~r2_hidden(D_49, B_50) | ~r2_hidden(D_49, k4_xboole_0(A_51, B_50)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.59/3.04  tff(c_185, plain, (![D_52, A_53]: (~r2_hidden(D_52, k1_xboole_0) | ~r2_hidden(D_52, A_53))), inference(superposition, [status(thm), theory('equality')], [c_22, c_178])).
% 8.59/3.04  tff(c_189, plain, (![A_54, A_55]: (~r2_hidden(A_54, A_55) | k1_tarski(A_54)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_170, c_185])).
% 8.59/3.04  tff(c_202, plain, (![A_46]: (k1_tarski(A_46)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_170, c_189])).
% 8.59/3.04  tff(c_142, plain, (![A_43, B_44]: (k4_xboole_0(k1_tarski(A_43), B_44)=k1_xboole_0 | ~r2_hidden(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.59/3.04  tff(c_152, plain, (![A_43]: (k1_tarski(A_43)=k1_xboole_0 | ~r2_hidden(A_43, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_142, c_22])).
% 8.59/3.04  tff(c_206, plain, (![A_43]: (~r2_hidden(A_43, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_202, c_152])).
% 8.59/3.04  tff(c_1256, plain, (![A_128, B_129]: (r2_hidden('#skF_2'(A_128, B_129, A_128), A_128) | k4_xboole_0(A_128, B_129)=A_128)), inference(resolution, [status(thm)], [c_1124, c_16])).
% 8.59/3.04  tff(c_1317, plain, (![B_129]: (k4_xboole_0(k1_xboole_0, B_129)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1256, c_206])).
% 8.59/3.04  tff(c_8, plain, (![D_8, A_3, B_4]: (r2_hidden(D_8, A_3) | ~r2_hidden(D_8, k4_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.59/3.04  tff(c_4084, plain, (![A_228, B_229, A_230, B_231]: (r2_hidden('#skF_2'(A_228, B_229, k4_xboole_0(A_230, B_231)), A_230) | r2_hidden('#skF_1'(A_228, B_229, k4_xboole_0(A_230, B_231)), A_228) | k4_xboole_0(A_230, B_231)=k4_xboole_0(A_228, B_229))), inference(resolution, [status(thm)], [c_1124, c_8])).
% 8.59/3.04  tff(c_4185, plain, (![B_229, A_230, B_231]: (r2_hidden('#skF_2'(k1_xboole_0, B_229, k4_xboole_0(A_230, B_231)), A_230) | k4_xboole_0(k1_xboole_0, B_229)=k4_xboole_0(A_230, B_231))), inference(resolution, [status(thm)], [c_4084, c_206])).
% 8.59/3.04  tff(c_4268, plain, (![B_229, A_230, B_231]: (r2_hidden('#skF_2'(k1_xboole_0, B_229, k4_xboole_0(A_230, B_231)), A_230) | k4_xboole_0(A_230, B_231)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1317, c_4185])).
% 8.59/3.04  tff(c_1242, plain, (![B_126, C_127]: (r2_hidden('#skF_2'(k1_xboole_0, B_126, C_127), C_127) | k4_xboole_0(k1_xboole_0, B_126)=C_127)), inference(resolution, [status(thm)], [c_1124, c_206])).
% 8.59/3.04  tff(c_1942, plain, (![B_126, C_127]: (r2_hidden('#skF_2'(k1_xboole_0, B_126, C_127), C_127) | k1_xboole_0=C_127)), inference(demodulation, [status(thm), theory('equality')], [c_1317, c_1242])).
% 8.59/3.04  tff(c_48, plain, (![A_20]: (k2_tarski(A_20, A_20)=k1_tarski(A_20))), inference(cnfTransformation, [status(thm)], [f_56])).
% 8.59/3.04  tff(c_80, plain, (![D_30, B_31]: (r2_hidden(D_30, k2_tarski(D_30, B_31)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 8.59/3.04  tff(c_83, plain, (![A_20]: (r2_hidden(A_20, k1_tarski(A_20)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_80])).
% 8.59/3.04  tff(c_4, plain, (![D_8, A_3, B_4]: (r2_hidden(D_8, k4_xboole_0(A_3, B_4)) | r2_hidden(D_8, B_4) | ~r2_hidden(D_8, A_3))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.59/3.04  tff(c_56, plain, (![A_26, B_27]: (k4_xboole_0(k1_tarski(A_26), B_27)=k1_xboole_0 | ~r2_hidden(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.59/3.04  tff(c_209, plain, (![A_58, B_59]: (k4_xboole_0(A_58, k4_xboole_0(A_58, B_59))=k3_xboole_0(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.59/3.04  tff(c_2058, plain, (![A_161, B_162]: (k3_xboole_0(k1_tarski(A_161), B_162)=k1_xboole_0 | ~r2_hidden(A_161, k4_xboole_0(k1_tarski(A_161), B_162)))), inference(superposition, [status(thm), theory('equality')], [c_56, c_209])).
% 8.59/3.04  tff(c_2074, plain, (![D_8, B_4]: (k3_xboole_0(k1_tarski(D_8), B_4)=k1_xboole_0 | r2_hidden(D_8, B_4) | ~r2_hidden(D_8, k1_tarski(D_8)))), inference(resolution, [status(thm)], [c_4, c_2058])).
% 8.59/3.04  tff(c_2090, plain, (![D_8, B_4]: (k3_xboole_0(k1_tarski(D_8), B_4)=k1_xboole_0 | r2_hidden(D_8, B_4))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_2074])).
% 8.59/3.04  tff(c_24, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k4_xboole_0(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.59/3.04  tff(c_489, plain, (![D_84, A_85, B_86]: (r2_hidden(D_84, k4_xboole_0(A_85, B_86)) | r2_hidden(D_84, B_86) | ~r2_hidden(D_84, A_85))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.59/3.04  tff(c_2949, plain, (![D_189, A_190, B_191]: (r2_hidden(D_189, k3_xboole_0(A_190, B_191)) | r2_hidden(D_189, k4_xboole_0(A_190, B_191)) | ~r2_hidden(D_189, A_190))), inference(superposition, [status(thm), theory('equality')], [c_24, c_489])).
% 8.59/3.04  tff(c_6, plain, (![D_8, B_4, A_3]: (~r2_hidden(D_8, B_4) | ~r2_hidden(D_8, k4_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.59/3.04  tff(c_3164, plain, (![D_196, B_197, A_198]: (~r2_hidden(D_196, B_197) | r2_hidden(D_196, k3_xboole_0(A_198, B_197)) | ~r2_hidden(D_196, A_198))), inference(resolution, [status(thm)], [c_2949, c_6])).
% 8.59/3.04  tff(c_3217, plain, (![D_196, B_4, D_8]: (~r2_hidden(D_196, B_4) | r2_hidden(D_196, k1_xboole_0) | ~r2_hidden(D_196, k1_tarski(D_8)) | r2_hidden(D_8, B_4))), inference(superposition, [status(thm), theory('equality')], [c_2090, c_3164])).
% 8.59/3.04  tff(c_3260, plain, (![D_199, B_200, D_201]: (~r2_hidden(D_199, B_200) | ~r2_hidden(D_199, k1_tarski(D_201)) | r2_hidden(D_201, B_200))), inference(negUnitSimplification, [status(thm)], [c_206, c_3217])).
% 8.59/3.04  tff(c_8449, plain, (![B_323, C_324, D_325]: (~r2_hidden('#skF_2'(k1_xboole_0, B_323, C_324), k1_tarski(D_325)) | r2_hidden(D_325, C_324) | k1_xboole_0=C_324)), inference(resolution, [status(thm)], [c_1942, c_3260])).
% 8.59/3.04  tff(c_8820, plain, (![D_332, B_333]: (r2_hidden(D_332, k4_xboole_0(k1_tarski(D_332), B_333)) | k4_xboole_0(k1_tarski(D_332), B_333)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4268, c_8449])).
% 8.59/3.04  tff(c_239, plain, (![A_26, B_59]: (k3_xboole_0(k1_tarski(A_26), B_59)=k1_xboole_0 | ~r2_hidden(A_26, k4_xboole_0(k1_tarski(A_26), B_59)))), inference(superposition, [status(thm), theory('equality')], [c_56, c_209])).
% 8.59/3.04  tff(c_8889, plain, (![D_334, B_335]: (k3_xboole_0(k1_tarski(D_334), B_335)=k1_xboole_0 | k4_xboole_0(k1_tarski(D_334), B_335)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8820, c_239])).
% 8.59/3.04  tff(c_9012, plain, (![D_334, B_335]: (k4_xboole_0(k1_tarski(D_334), k1_xboole_0)=k3_xboole_0(k1_tarski(D_334), B_335) | k3_xboole_0(k1_tarski(D_334), B_335)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8889, c_24])).
% 8.59/3.04  tff(c_9559, plain, (![D_344, B_345]: (k3_xboole_0(k1_tarski(D_344), B_345)=k1_tarski(D_344) | k3_xboole_0(k1_tarski(D_344), B_345)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_9012])).
% 8.59/3.04  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.59/3.04  tff(c_10004, plain, (![B_348, D_349]: (k3_xboole_0(B_348, k1_tarski(D_349))=k1_tarski(D_349) | k3_xboole_0(k1_tarski(D_349), B_348)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_9559, c_2])).
% 8.59/3.04  tff(c_1943, plain, (![B_154, C_155]: (r2_hidden('#skF_2'(k1_xboole_0, B_154, C_155), C_155) | k1_xboole_0=C_155)), inference(demodulation, [status(thm), theory('equality')], [c_1317, c_1242])).
% 8.59/3.04  tff(c_286, plain, (![D_61, A_62, B_63]: (r2_hidden(D_61, A_62) | ~r2_hidden(D_61, k4_xboole_0(A_62, B_63)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.59/3.04  tff(c_312, plain, (![D_65, A_66, B_67]: (r2_hidden(D_65, A_66) | ~r2_hidden(D_65, k3_xboole_0(A_66, B_67)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_286])).
% 8.59/3.04  tff(c_324, plain, (![D_65, B_2, A_1]: (r2_hidden(D_65, B_2) | ~r2_hidden(D_65, k3_xboole_0(A_1, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_312])).
% 8.59/3.04  tff(c_1987, plain, (![B_154, A_1, B_2]: (r2_hidden('#skF_2'(k1_xboole_0, B_154, k3_xboole_0(A_1, B_2)), B_2) | k3_xboole_0(A_1, B_2)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1943, c_324])).
% 8.59/3.04  tff(c_8533, plain, (![D_326, A_327]: (r2_hidden(D_326, k3_xboole_0(A_327, k1_tarski(D_326))) | k3_xboole_0(A_327, k1_tarski(D_326))=k1_xboole_0)), inference(resolution, [status(thm)], [c_1987, c_8449])).
% 8.59/3.04  tff(c_8585, plain, (![D_326, A_1]: (r2_hidden(D_326, k3_xboole_0(k1_tarski(D_326), A_1)) | k3_xboole_0(A_1, k1_tarski(D_326))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_8533])).
% 8.59/3.04  tff(c_10181, plain, (![D_349, B_348]: (r2_hidden(D_349, k1_xboole_0) | k3_xboole_0(B_348, k1_tarski(D_349))=k1_xboole_0 | k3_xboole_0(B_348, k1_tarski(D_349))=k1_tarski(D_349))), inference(superposition, [status(thm), theory('equality')], [c_10004, c_8585])).
% 8.59/3.04  tff(c_11102, plain, (![B_352, D_353]: (k3_xboole_0(B_352, k1_tarski(D_353))=k1_xboole_0 | k3_xboole_0(B_352, k1_tarski(D_353))=k1_tarski(D_353))), inference(negUnitSimplification, [status(thm)], [c_206, c_10181])).
% 8.59/3.04  tff(c_58, plain, (k3_xboole_0(k1_tarski('#skF_5'), '#skF_6')!=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_69])).
% 8.59/3.04  tff(c_61, plain, (k3_xboole_0('#skF_6', k1_tarski('#skF_5'))!=k1_tarski('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_58])).
% 8.59/3.04  tff(c_11361, plain, (k3_xboole_0('#skF_6', k1_tarski('#skF_5'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_11102, c_61])).
% 8.59/3.04  tff(c_3235, plain, (![D_196, B_2, A_1]: (~r2_hidden(D_196, B_2) | r2_hidden(D_196, k3_xboole_0(B_2, A_1)) | ~r2_hidden(D_196, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_3164])).
% 8.59/3.04  tff(c_11512, plain, (![D_196]: (~r2_hidden(D_196, '#skF_6') | r2_hidden(D_196, k1_xboole_0) | ~r2_hidden(D_196, k1_tarski('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_11361, c_3235])).
% 8.59/3.04  tff(c_11634, plain, (![D_358]: (~r2_hidden(D_358, '#skF_6') | ~r2_hidden(D_358, k1_tarski('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_206, c_11512])).
% 8.59/3.04  tff(c_14034, plain, (![B_392]: (~r2_hidden('#skF_2'(k1_tarski('#skF_5'), B_392, k1_tarski('#skF_5')), '#skF_6') | k4_xboole_0(k1_tarski('#skF_5'), B_392)=k1_tarski('#skF_5'))), inference(resolution, [status(thm)], [c_1230, c_11634])).
% 8.59/3.04  tff(c_14056, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')=k1_tarski('#skF_5')), inference(resolution, [status(thm)], [c_3559, c_14034])).
% 8.59/3.04  tff(c_14066, plain, $false, inference(negUnitSimplification, [status(thm)], [c_132, c_132, c_14056])).
% 8.59/3.04  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.59/3.04  
% 8.59/3.04  Inference rules
% 8.59/3.04  ----------------------
% 8.59/3.04  #Ref     : 0
% 8.59/3.04  #Sup     : 3171
% 8.59/3.04  #Fact    : 4
% 8.59/3.04  #Define  : 0
% 8.59/3.04  #Split   : 2
% 8.59/3.04  #Chain   : 0
% 8.59/3.04  #Close   : 0
% 8.59/3.04  
% 8.59/3.04  Ordering : KBO
% 8.59/3.04  
% 8.59/3.04  Simplification rules
% 8.59/3.04  ----------------------
% 8.59/3.04  #Subsume      : 1080
% 8.59/3.04  #Demod        : 1975
% 8.59/3.04  #Tautology    : 893
% 8.59/3.04  #SimpNegUnit  : 541
% 8.59/3.04  #BackRed      : 13
% 8.59/3.04  
% 8.59/3.04  #Partial instantiations: 0
% 8.59/3.04  #Strategies tried      : 1
% 8.59/3.04  
% 8.59/3.04  Timing (in seconds)
% 8.59/3.04  ----------------------
% 8.59/3.04  Preprocessing        : 0.32
% 8.59/3.04  Parsing              : 0.16
% 8.59/3.04  CNF conversion       : 0.02
% 8.59/3.04  Main loop            : 1.95
% 8.59/3.04  Inferencing          : 0.58
% 8.59/3.04  Reduction            : 0.71
% 8.59/3.04  Demodulation         : 0.54
% 8.59/3.04  BG Simplification    : 0.07
% 8.59/3.04  Subsumption          : 0.48
% 8.59/3.04  Abstraction          : 0.10
% 8.59/3.04  MUC search           : 0.00
% 8.59/3.04  Cooper               : 0.00
% 8.59/3.04  Total                : 2.31
% 8.59/3.04  Index Insertion      : 0.00
% 8.59/3.04  Index Deletion       : 0.00
% 8.59/3.04  Index Matching       : 0.00
% 8.59/3.04  BG Taut test         : 0.00
%------------------------------------------------------------------------------
