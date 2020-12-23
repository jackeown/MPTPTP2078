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
% DateTime   : Thu Dec  3 09:46:08 EST 2020

% Result     : Theorem 25.87s
% Output     : CNFRefutation 25.87s
% Verified   : 
% Statistics : Number of formulae       :   97 (3715 expanded)
%              Number of leaves         :   19 (1298 expanded)
%              Depth                    :   20
%              Number of atoms          :  260 (6816 expanded)
%              Number of equality atoms :  232 (6228 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_44,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_48,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_46,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_42,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_51,negated_conjecture,(
    ~ ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(c_28,plain,(
    ! [A_10,B_11] : k2_xboole_0(k1_tarski(A_10),k1_tarski(B_11)) = k2_tarski(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_32,plain,(
    ! [A_15] : k2_tarski(A_15,A_15) = k1_tarski(A_15) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_65,plain,(
    ! [A_30,B_31,C_32] : k2_xboole_0(k1_tarski(A_30),k2_tarski(B_31,C_32)) = k1_enumset1(A_30,B_31,C_32) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_74,plain,(
    ! [A_30,A_15] : k2_xboole_0(k1_tarski(A_30),k1_tarski(A_15)) = k1_enumset1(A_30,A_15,A_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_65])).

tff(c_78,plain,(
    ! [A_33,A_34] : k1_enumset1(A_33,A_34,A_34) = k2_tarski(A_33,A_34) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_74])).

tff(c_6,plain,(
    ! [E_9,A_3,B_4] : r2_hidden(E_9,k1_enumset1(A_3,B_4,E_9)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_84,plain,(
    ! [A_34,A_33] : r2_hidden(A_34,k2_tarski(A_33,A_34)) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_6])).

tff(c_10,plain,(
    ! [E_9,B_4,C_5] : r2_hidden(E_9,k1_enumset1(E_9,B_4,C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_90,plain,(
    ! [A_33,A_34] : r2_hidden(A_33,k2_tarski(A_33,A_34)) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_10])).

tff(c_77,plain,(
    ! [A_30,A_15] : k1_enumset1(A_30,A_15,A_15) = k2_tarski(A_30,A_15) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_74])).

tff(c_169,plain,(
    ! [A_81,B_82,C_83,D_84] :
      ( '#skF_1'(A_81,B_82,C_83,D_84) = C_83
      | '#skF_1'(A_81,B_82,C_83,D_84) = B_82
      | '#skF_1'(A_81,B_82,C_83,D_84) = A_81
      | r2_hidden('#skF_2'(A_81,B_82,C_83,D_84),D_84)
      | k1_enumset1(A_81,B_82,C_83) = D_84 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_4,plain,(
    ! [E_9,C_5,B_4,A_3] :
      ( E_9 = C_5
      | E_9 = B_4
      | E_9 = A_3
      | ~ r2_hidden(E_9,k1_enumset1(A_3,B_4,C_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_184,plain,(
    ! [A_3,A_81,B_82,C_83,C_5,B_4] :
      ( '#skF_2'(A_81,B_82,C_83,k1_enumset1(A_3,B_4,C_5)) = C_5
      | '#skF_2'(A_81,B_82,C_83,k1_enumset1(A_3,B_4,C_5)) = B_4
      | '#skF_2'(A_81,B_82,C_83,k1_enumset1(A_3,B_4,C_5)) = A_3
      | '#skF_1'(A_81,B_82,C_83,k1_enumset1(A_3,B_4,C_5)) = C_83
      | '#skF_1'(A_81,B_82,C_83,k1_enumset1(A_3,B_4,C_5)) = B_82
      | '#skF_1'(A_81,B_82,C_83,k1_enumset1(A_3,B_4,C_5)) = A_81
      | k1_enumset1(A_81,B_82,C_83) = k1_enumset1(A_3,B_4,C_5) ) ),
    inference(resolution,[status(thm)],[c_169,c_4])).

tff(c_803,plain,(
    ! [A_3,A_81,B_82,C_83,C_5] :
      ( '#skF_2'(A_81,B_82,C_83,k1_enumset1(A_3,C_5,C_5)) = A_3
      | '#skF_1'(A_81,B_82,C_83,k1_enumset1(A_3,C_5,C_5)) = C_83
      | '#skF_1'(A_81,B_82,C_83,k1_enumset1(A_3,C_5,C_5)) = B_82
      | '#skF_1'(A_81,B_82,C_83,k1_enumset1(A_3,C_5,C_5)) = A_81
      | k1_enumset1(A_81,B_82,C_83) = k1_enumset1(A_3,C_5,C_5)
      | '#skF_2'(A_81,B_82,C_83,k1_enumset1(A_3,C_5,C_5)) = C_5 ) ),
    inference(factorization,[status(thm),theory(equality)],[c_184])).

tff(c_2639,plain,(
    ! [C_151,B_152,A_150,A_148,C_149] :
      ( '#skF_2'(A_148,B_152,C_149,k2_tarski(A_150,C_151)) = A_150
      | '#skF_1'(A_148,B_152,C_149,k2_tarski(A_150,C_151)) = C_149
      | '#skF_1'(A_148,B_152,C_149,k2_tarski(A_150,C_151)) = B_152
      | '#skF_1'(A_148,B_152,C_149,k2_tarski(A_150,C_151)) = A_148
      | k2_tarski(A_150,C_151) = k1_enumset1(A_148,B_152,C_149)
      | '#skF_2'(A_148,B_152,C_149,k2_tarski(A_150,C_151)) = C_151 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_77,c_77,c_77,c_77,c_77,c_803])).

tff(c_22,plain,(
    ! [A_3,B_4,C_5,D_6] :
      ( '#skF_1'(A_3,B_4,C_5,D_6) = C_5
      | '#skF_1'(A_3,B_4,C_5,D_6) = B_4
      | '#skF_1'(A_3,B_4,C_5,D_6) = A_3
      | '#skF_2'(A_3,B_4,C_5,D_6) != A_3
      | k1_enumset1(A_3,B_4,C_5) = D_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_9545,plain,(
    ! [C_444,B_445,C_446,A_447] :
      ( '#skF_2'(C_444,B_445,C_446,k2_tarski(A_447,C_444)) = A_447
      | '#skF_1'(C_444,B_445,C_446,k2_tarski(A_447,C_444)) = C_446
      | '#skF_1'(C_444,B_445,C_446,k2_tarski(A_447,C_444)) = B_445
      | '#skF_1'(C_444,B_445,C_446,k2_tarski(A_447,C_444)) = C_444
      | k2_tarski(A_447,C_444) = k1_enumset1(C_444,B_445,C_446) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2639,c_22])).

tff(c_14,plain,(
    ! [A_3,B_4,C_5,D_6] :
      ( '#skF_1'(A_3,B_4,C_5,D_6) = C_5
      | '#skF_1'(A_3,B_4,C_5,D_6) = B_4
      | '#skF_1'(A_3,B_4,C_5,D_6) = A_3
      | '#skF_2'(A_3,B_4,C_5,D_6) != C_5
      | k1_enumset1(A_3,B_4,C_5) = D_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_9590,plain,(
    ! [C_444,B_445,C_446] :
      ( '#skF_1'(C_444,B_445,C_446,k2_tarski(C_446,C_444)) = C_446
      | '#skF_1'(C_444,B_445,C_446,k2_tarski(C_446,C_444)) = B_445
      | '#skF_1'(C_444,B_445,C_446,k2_tarski(C_446,C_444)) = C_444
      | k1_enumset1(C_444,B_445,C_446) = k2_tarski(C_446,C_444) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9545,c_14])).

tff(c_10557,plain,(
    ! [C_470,C_471] :
      ( '#skF_1'(C_470,C_470,C_471,k2_tarski(C_471,C_470)) = C_471
      | k1_enumset1(C_470,C_470,C_471) = k2_tarski(C_471,C_470)
      | '#skF_1'(C_470,C_470,C_471,k2_tarski(C_471,C_470)) = C_470 ) ),
    inference(factorization,[status(thm),theory(equality)],[c_9590])).

tff(c_149,plain,(
    ! [A_61,B_62,C_63,D_64] :
      ( ~ r2_hidden('#skF_1'(A_61,B_62,C_63,D_64),D_64)
      | r2_hidden('#skF_2'(A_61,B_62,C_63,D_64),D_64)
      | k1_enumset1(A_61,B_62,C_63) = D_64 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_96,plain,(
    ! [E_35,C_36,B_37,A_38] :
      ( E_35 = C_36
      | E_35 = B_37
      | E_35 = A_38
      | ~ r2_hidden(E_35,k1_enumset1(A_38,B_37,C_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_99,plain,(
    ! [E_35,A_15,A_30] :
      ( E_35 = A_15
      | E_35 = A_15
      | E_35 = A_30
      | ~ r2_hidden(E_35,k2_tarski(A_30,A_15)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_96])).

tff(c_163,plain,(
    ! [A_15,A_61,B_62,C_63,A_30] :
      ( '#skF_2'(A_61,B_62,C_63,k2_tarski(A_30,A_15)) = A_15
      | '#skF_2'(A_61,B_62,C_63,k2_tarski(A_30,A_15)) = A_30
      | ~ r2_hidden('#skF_1'(A_61,B_62,C_63,k2_tarski(A_30,A_15)),k2_tarski(A_30,A_15))
      | k2_tarski(A_30,A_15) = k1_enumset1(A_61,B_62,C_63) ) ),
    inference(resolution,[status(thm)],[c_149,c_99])).

tff(c_10589,plain,(
    ! [C_470,C_471] :
      ( '#skF_2'(C_470,C_470,C_471,k2_tarski(C_471,C_470)) = C_470
      | '#skF_2'(C_470,C_470,C_471,k2_tarski(C_471,C_470)) = C_471
      | ~ r2_hidden(C_471,k2_tarski(C_471,C_470))
      | k1_enumset1(C_470,C_470,C_471) = k2_tarski(C_471,C_470)
      | k1_enumset1(C_470,C_470,C_471) = k2_tarski(C_471,C_470)
      | '#skF_1'(C_470,C_470,C_471,k2_tarski(C_471,C_470)) = C_470 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10557,c_163])).

tff(c_109308,plain,(
    ! [C_1316,C_1317] :
      ( '#skF_2'(C_1316,C_1316,C_1317,k2_tarski(C_1317,C_1316)) = C_1316
      | '#skF_2'(C_1316,C_1316,C_1317,k2_tarski(C_1317,C_1316)) = C_1317
      | k1_enumset1(C_1316,C_1316,C_1317) = k2_tarski(C_1317,C_1316)
      | '#skF_1'(C_1316,C_1316,C_1317,k2_tarski(C_1317,C_1316)) = C_1316 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_10589])).

tff(c_9948,plain,(
    ! [C_453,B_454,C_455] :
      ( '#skF_1'(C_453,B_454,C_455,k2_tarski(C_455,C_453)) = C_455
      | '#skF_1'(C_453,B_454,C_455,k2_tarski(C_455,C_453)) = B_454
      | '#skF_1'(C_453,B_454,C_455,k2_tarski(C_455,C_453)) = C_453
      | k1_enumset1(C_453,B_454,C_455) = k2_tarski(C_455,C_453) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9545,c_14])).

tff(c_16,plain,(
    ! [A_3,B_4,C_5,D_6] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4,C_5,D_6),D_6)
      | '#skF_2'(A_3,B_4,C_5,D_6) != B_4
      | k1_enumset1(A_3,B_4,C_5) = D_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_9976,plain,(
    ! [C_455,C_453,B_454] :
      ( ~ r2_hidden(C_455,k2_tarski(C_455,C_453))
      | '#skF_2'(C_453,B_454,C_455,k2_tarski(C_455,C_453)) != B_454
      | k1_enumset1(C_453,B_454,C_455) = k2_tarski(C_455,C_453)
      | '#skF_1'(C_453,B_454,C_455,k2_tarski(C_455,C_453)) = B_454
      | '#skF_1'(C_453,B_454,C_455,k2_tarski(C_455,C_453)) = C_453
      | k1_enumset1(C_453,B_454,C_455) = k2_tarski(C_455,C_453) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9948,c_16])).

tff(c_10143,plain,(
    ! [C_453,B_454,C_455] :
      ( '#skF_2'(C_453,B_454,C_455,k2_tarski(C_455,C_453)) != B_454
      | '#skF_1'(C_453,B_454,C_455,k2_tarski(C_455,C_453)) = B_454
      | '#skF_1'(C_453,B_454,C_455,k2_tarski(C_455,C_453)) = C_453
      | k1_enumset1(C_453,B_454,C_455) = k2_tarski(C_455,C_453) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_9976])).

tff(c_110058,plain,(
    ! [C_1318,C_1319] :
      ( '#skF_2'(C_1318,C_1318,C_1319,k2_tarski(C_1319,C_1318)) = C_1319
      | k1_enumset1(C_1318,C_1318,C_1319) = k2_tarski(C_1319,C_1318)
      | '#skF_1'(C_1318,C_1318,C_1319,k2_tarski(C_1319,C_1318)) = C_1318 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_109308,c_10143])).

tff(c_836,plain,(
    ! [B_115,A_112,A_110,B_114,C_111,C_113] :
      ( '#skF_2'(A_110,B_114,C_111,k1_enumset1(A_112,B_115,C_113)) = C_113
      | '#skF_2'(A_110,B_114,C_111,k1_enumset1(A_112,B_115,C_113)) = B_115
      | '#skF_2'(A_110,B_114,C_111,k1_enumset1(A_112,B_115,C_113)) = A_112
      | '#skF_1'(A_110,B_114,C_111,k1_enumset1(A_112,B_115,C_113)) = C_111
      | '#skF_1'(A_110,B_114,C_111,k1_enumset1(A_112,B_115,C_113)) = B_114
      | '#skF_1'(A_110,B_114,C_111,k1_enumset1(A_112,B_115,C_113)) = A_110
      | k1_enumset1(A_112,B_115,C_113) = k1_enumset1(A_110,B_114,C_111) ) ),
    inference(resolution,[status(thm)],[c_169,c_4])).

tff(c_18,plain,(
    ! [A_3,B_4,C_5,D_6] :
      ( '#skF_1'(A_3,B_4,C_5,D_6) = C_5
      | '#skF_1'(A_3,B_4,C_5,D_6) = B_4
      | '#skF_1'(A_3,B_4,C_5,D_6) = A_3
      | '#skF_2'(A_3,B_4,C_5,D_6) != B_4
      | k1_enumset1(A_3,B_4,C_5) = D_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_6530,plain,(
    ! [C_323,A_326,A_322,C_325,B_324] :
      ( '#skF_2'(A_322,B_324,C_325,k1_enumset1(A_326,B_324,C_323)) = C_323
      | '#skF_2'(A_322,B_324,C_325,k1_enumset1(A_326,B_324,C_323)) = A_326
      | '#skF_1'(A_322,B_324,C_325,k1_enumset1(A_326,B_324,C_323)) = C_325
      | '#skF_1'(A_322,B_324,C_325,k1_enumset1(A_326,B_324,C_323)) = B_324
      | '#skF_1'(A_322,B_324,C_325,k1_enumset1(A_326,B_324,C_323)) = A_322
      | k1_enumset1(A_326,B_324,C_323) = k1_enumset1(A_322,B_324,C_325) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_836,c_18])).

tff(c_6602,plain,(
    ! [A_322,C_323,C_325,A_326] :
      ( '#skF_2'(A_322,C_323,C_325,k1_enumset1(A_326,C_323,C_323)) = A_326
      | '#skF_1'(A_322,C_323,C_325,k1_enumset1(A_326,C_323,C_323)) = C_325
      | '#skF_1'(A_322,C_323,C_325,k1_enumset1(A_326,C_323,C_323)) = C_323
      | '#skF_1'(A_322,C_323,C_325,k1_enumset1(A_326,C_323,C_323)) = A_322
      | k1_enumset1(A_326,C_323,C_323) = k1_enumset1(A_322,C_323,C_325) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6530,c_18])).

tff(c_10288,plain,(
    ! [A_464,C_465,C_466,A_467] :
      ( '#skF_2'(A_464,C_465,C_466,k2_tarski(A_467,C_465)) = A_467
      | '#skF_1'(A_464,C_465,C_466,k2_tarski(A_467,C_465)) = C_466
      | '#skF_1'(A_464,C_465,C_466,k2_tarski(A_467,C_465)) = C_465
      | '#skF_1'(A_464,C_465,C_466,k2_tarski(A_467,C_465)) = A_464
      | k2_tarski(A_467,C_465) = k1_enumset1(A_464,C_465,C_466) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_77,c_77,c_77,c_77,c_6602])).

tff(c_11573,plain,(
    ! [A_489,C_490,C_491] :
      ( '#skF_1'(A_489,C_490,C_491,k2_tarski(C_491,C_490)) = C_491
      | '#skF_1'(A_489,C_490,C_491,k2_tarski(C_491,C_490)) = C_490
      | '#skF_1'(A_489,C_490,C_491,k2_tarski(C_491,C_490)) = A_489
      | k1_enumset1(A_489,C_490,C_491) = k2_tarski(C_491,C_490) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10288,c_14])).

tff(c_12,plain,(
    ! [A_3,B_4,C_5,D_6] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4,C_5,D_6),D_6)
      | '#skF_2'(A_3,B_4,C_5,D_6) != C_5
      | k1_enumset1(A_3,B_4,C_5) = D_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_11632,plain,(
    ! [C_491,C_490,A_489] :
      ( ~ r2_hidden(C_491,k2_tarski(C_491,C_490))
      | '#skF_2'(A_489,C_490,C_491,k2_tarski(C_491,C_490)) != C_491
      | k1_enumset1(A_489,C_490,C_491) = k2_tarski(C_491,C_490)
      | '#skF_1'(A_489,C_490,C_491,k2_tarski(C_491,C_490)) = C_490
      | '#skF_1'(A_489,C_490,C_491,k2_tarski(C_491,C_490)) = A_489
      | k1_enumset1(A_489,C_490,C_491) = k2_tarski(C_491,C_490) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11573,c_12])).

tff(c_11934,plain,(
    ! [A_489,C_490,C_491] :
      ( '#skF_2'(A_489,C_490,C_491,k2_tarski(C_491,C_490)) != C_491
      | '#skF_1'(A_489,C_490,C_491,k2_tarski(C_491,C_490)) = C_490
      | '#skF_1'(A_489,C_490,C_491,k2_tarski(C_491,C_490)) = A_489
      | k1_enumset1(A_489,C_490,C_491) = k2_tarski(C_491,C_490) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_11632])).

tff(c_110731,plain,(
    ! [C_1320,C_1321] :
      ( k1_enumset1(C_1320,C_1320,C_1321) = k2_tarski(C_1321,C_1320)
      | '#skF_1'(C_1320,C_1320,C_1321,k2_tarski(C_1321,C_1320)) = C_1320 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_110058,c_11934])).

tff(c_110910,plain,(
    ! [C_1320,C_1321] :
      ( '#skF_2'(C_1320,C_1320,C_1321,k2_tarski(C_1321,C_1320)) = C_1320
      | '#skF_2'(C_1320,C_1320,C_1321,k2_tarski(C_1321,C_1320)) = C_1321
      | ~ r2_hidden(C_1320,k2_tarski(C_1321,C_1320))
      | k1_enumset1(C_1320,C_1320,C_1321) = k2_tarski(C_1321,C_1320)
      | k1_enumset1(C_1320,C_1320,C_1321) = k2_tarski(C_1321,C_1320) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_110731,c_163])).

tff(c_111751,plain,(
    ! [C_1332,C_1333] :
      ( '#skF_2'(C_1332,C_1332,C_1333,k2_tarski(C_1333,C_1332)) = C_1332
      | '#skF_2'(C_1332,C_1332,C_1333,k2_tarski(C_1333,C_1332)) = C_1333
      | k1_enumset1(C_1332,C_1332,C_1333) = k2_tarski(C_1333,C_1332) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_110910])).

tff(c_20,plain,(
    ! [A_3,B_4,C_5,D_6] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4,C_5,D_6),D_6)
      | '#skF_2'(A_3,B_4,C_5,D_6) != A_3
      | k1_enumset1(A_3,B_4,C_5) = D_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_110919,plain,(
    ! [C_1320,C_1321] :
      ( ~ r2_hidden(C_1320,k2_tarski(C_1321,C_1320))
      | '#skF_2'(C_1320,C_1320,C_1321,k2_tarski(C_1321,C_1320)) != C_1320
      | k1_enumset1(C_1320,C_1320,C_1321) = k2_tarski(C_1321,C_1320)
      | k1_enumset1(C_1320,C_1320,C_1321) = k2_tarski(C_1321,C_1320) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_110731,c_20])).

tff(c_111116,plain,(
    ! [C_1320,C_1321] :
      ( '#skF_2'(C_1320,C_1320,C_1321,k2_tarski(C_1321,C_1320)) != C_1320
      | k1_enumset1(C_1320,C_1320,C_1321) = k2_tarski(C_1321,C_1320) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_110919])).

tff(c_112422,plain,(
    ! [C_1334,C_1335] :
      ( '#skF_2'(C_1334,C_1334,C_1335,k2_tarski(C_1335,C_1334)) = C_1335
      | k1_enumset1(C_1334,C_1334,C_1335) = k2_tarski(C_1335,C_1334) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_111751,c_111116])).

tff(c_110913,plain,(
    ! [C_1320,C_1321] :
      ( ~ r2_hidden(C_1320,k2_tarski(C_1321,C_1320))
      | '#skF_2'(C_1320,C_1320,C_1321,k2_tarski(C_1321,C_1320)) != C_1321
      | k1_enumset1(C_1320,C_1320,C_1321) = k2_tarski(C_1321,C_1320)
      | k1_enumset1(C_1320,C_1320,C_1321) = k2_tarski(C_1321,C_1320) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_110731,c_12])).

tff(c_111112,plain,(
    ! [C_1320,C_1321] :
      ( '#skF_2'(C_1320,C_1320,C_1321,k2_tarski(C_1321,C_1320)) != C_1321
      | k1_enumset1(C_1320,C_1320,C_1321) = k2_tarski(C_1321,C_1320) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_110913])).

tff(c_114459,plain,(
    ! [C_1337,C_1338] : k1_enumset1(C_1337,C_1337,C_1338) = k2_tarski(C_1338,C_1337) ),
    inference(superposition,[status(thm),theory(equality)],[c_112422,c_111112])).

tff(c_9587,plain,(
    ! [C_444,B_445,C_446] :
      ( '#skF_1'(C_444,B_445,C_446,k2_tarski(B_445,C_444)) = C_446
      | '#skF_1'(C_444,B_445,C_446,k2_tarski(B_445,C_444)) = B_445
      | '#skF_1'(C_444,B_445,C_446,k2_tarski(B_445,C_444)) = C_444
      | k1_enumset1(C_444,B_445,C_446) = k2_tarski(B_445,C_444) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9545,c_18])).

tff(c_9609,plain,(
    ! [C_444,C_446] :
      ( '#skF_1'(C_444,C_446,C_446,k2_tarski(C_446,C_444)) = C_444
      | k1_enumset1(C_444,C_446,C_446) = k2_tarski(C_446,C_444)
      | '#skF_1'(C_444,C_446,C_446,k2_tarski(C_446,C_444)) = C_446 ) ),
    inference(factorization,[status(thm),theory(equality)],[c_9587])).

tff(c_9782,plain,(
    ! [C_451,C_452] :
      ( '#skF_1'(C_451,C_452,C_452,k2_tarski(C_452,C_451)) = C_451
      | k2_tarski(C_452,C_451) = k2_tarski(C_451,C_452)
      | '#skF_1'(C_451,C_452,C_452,k2_tarski(C_452,C_451)) = C_452 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_9609])).

tff(c_9800,plain,(
    ! [C_451,C_452] :
      ( '#skF_2'(C_451,C_452,C_452,k2_tarski(C_452,C_451)) = C_451
      | '#skF_2'(C_451,C_452,C_452,k2_tarski(C_452,C_451)) = C_452
      | ~ r2_hidden(C_451,k2_tarski(C_452,C_451))
      | k1_enumset1(C_451,C_452,C_452) = k2_tarski(C_452,C_451)
      | k2_tarski(C_452,C_451) = k2_tarski(C_451,C_452)
      | '#skF_1'(C_451,C_452,C_452,k2_tarski(C_452,C_451)) = C_452 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9782,c_163])).

tff(c_14105,plain,(
    ! [C_532,C_533] :
      ( '#skF_2'(C_532,C_533,C_533,k2_tarski(C_533,C_532)) = C_532
      | '#skF_2'(C_532,C_533,C_533,k2_tarski(C_533,C_532)) = C_533
      | k2_tarski(C_533,C_532) = k2_tarski(C_532,C_533)
      | '#skF_1'(C_532,C_533,C_533,k2_tarski(C_533,C_532)) = C_533 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_84,c_9800])).

tff(c_9809,plain,(
    ! [C_451,C_452] :
      ( ~ r2_hidden(C_451,k2_tarski(C_452,C_451))
      | '#skF_2'(C_451,C_452,C_452,k2_tarski(C_452,C_451)) != C_451
      | k1_enumset1(C_451,C_452,C_452) = k2_tarski(C_452,C_451)
      | k2_tarski(C_452,C_451) = k2_tarski(C_451,C_452)
      | '#skF_1'(C_451,C_452,C_452,k2_tarski(C_452,C_451)) = C_452 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9782,c_20])).

tff(c_9887,plain,(
    ! [C_451,C_452] :
      ( '#skF_2'(C_451,C_452,C_452,k2_tarski(C_452,C_451)) != C_451
      | k2_tarski(C_452,C_451) = k2_tarski(C_451,C_452)
      | '#skF_1'(C_451,C_452,C_452,k2_tarski(C_452,C_451)) = C_452 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_84,c_9809])).

tff(c_14406,plain,(
    ! [C_534,C_535] :
      ( '#skF_2'(C_534,C_535,C_535,k2_tarski(C_535,C_534)) = C_535
      | k2_tarski(C_535,C_534) = k2_tarski(C_534,C_535)
      | '#skF_1'(C_534,C_535,C_535,k2_tarski(C_535,C_534)) = C_535 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14105,c_9887])).

tff(c_9803,plain,(
    ! [C_451,C_452] :
      ( ~ r2_hidden(C_451,k2_tarski(C_452,C_451))
      | '#skF_2'(C_451,C_452,C_452,k2_tarski(C_452,C_451)) != C_452
      | k1_enumset1(C_451,C_452,C_452) = k2_tarski(C_452,C_451)
      | k2_tarski(C_452,C_451) = k2_tarski(C_451,C_452)
      | '#skF_1'(C_451,C_452,C_452,k2_tarski(C_452,C_451)) = C_452 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9782,c_12])).

tff(c_9883,plain,(
    ! [C_451,C_452] :
      ( '#skF_2'(C_451,C_452,C_452,k2_tarski(C_452,C_451)) != C_452
      | k2_tarski(C_452,C_451) = k2_tarski(C_451,C_452)
      | '#skF_1'(C_451,C_452,C_452,k2_tarski(C_452,C_451)) = C_452 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_84,c_9803])).

tff(c_14628,plain,(
    ! [C_537,C_536] :
      ( k2_tarski(C_537,C_536) = k2_tarski(C_536,C_537)
      | '#skF_1'(C_537,C_536,C_536,k2_tarski(C_536,C_537)) = C_536 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14406,c_9883])).

tff(c_14732,plain,(
    ! [C_537,C_536] :
      ( '#skF_2'(C_537,C_536,C_536,k2_tarski(C_536,C_537)) = C_537
      | '#skF_2'(C_537,C_536,C_536,k2_tarski(C_536,C_537)) = C_536
      | ~ r2_hidden(C_536,k2_tarski(C_536,C_537))
      | k1_enumset1(C_537,C_536,C_536) = k2_tarski(C_536,C_537)
      | k2_tarski(C_537,C_536) = k2_tarski(C_536,C_537) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14628,c_163])).

tff(c_14980,plain,(
    ! [C_542,C_543] :
      ( '#skF_2'(C_542,C_543,C_543,k2_tarski(C_543,C_542)) = C_542
      | '#skF_2'(C_542,C_543,C_543,k2_tarski(C_543,C_542)) = C_543
      | k2_tarski(C_543,C_542) = k2_tarski(C_542,C_543) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_90,c_14732])).

tff(c_14741,plain,(
    ! [C_536,C_537] :
      ( ~ r2_hidden(C_536,k2_tarski(C_536,C_537))
      | '#skF_2'(C_537,C_536,C_536,k2_tarski(C_536,C_537)) != C_537
      | k1_enumset1(C_537,C_536,C_536) = k2_tarski(C_536,C_537)
      | k2_tarski(C_537,C_536) = k2_tarski(C_536,C_537) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14628,c_20])).

tff(c_14861,plain,(
    ! [C_537,C_536] :
      ( '#skF_2'(C_537,C_536,C_536,k2_tarski(C_536,C_537)) != C_537
      | k2_tarski(C_537,C_536) = k2_tarski(C_536,C_537) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_90,c_14741])).

tff(c_15263,plain,(
    ! [C_544,C_545] :
      ( '#skF_2'(C_544,C_545,C_545,k2_tarski(C_545,C_544)) = C_545
      | k2_tarski(C_545,C_544) = k2_tarski(C_544,C_545) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14980,c_14861])).

tff(c_14735,plain,(
    ! [C_536,C_537] :
      ( ~ r2_hidden(C_536,k2_tarski(C_536,C_537))
      | '#skF_2'(C_537,C_536,C_536,k2_tarski(C_536,C_537)) != C_536
      | k1_enumset1(C_537,C_536,C_536) = k2_tarski(C_536,C_537)
      | k2_tarski(C_537,C_536) = k2_tarski(C_536,C_537) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14628,c_12])).

tff(c_14857,plain,(
    ! [C_537,C_536] :
      ( '#skF_2'(C_537,C_536,C_536,k2_tarski(C_536,C_537)) != C_536
      | k2_tarski(C_537,C_536) = k2_tarski(C_536,C_537) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_90,c_14735])).

tff(c_15481,plain,(
    ! [C_547,C_546] : k2_tarski(C_547,C_546) = k2_tarski(C_546,C_547) ),
    inference(superposition,[status(thm),theory(equality)],[c_15263,c_14857])).

tff(c_30,plain,(
    ! [A_12,B_13,C_14] : k2_xboole_0(k1_tarski(A_12),k2_tarski(B_13,C_14)) = k1_enumset1(A_12,B_13,C_14) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_15858,plain,(
    ! [A_548,C_549,C_550] : k2_xboole_0(k1_tarski(A_548),k2_tarski(C_549,C_550)) = k1_enumset1(A_548,C_550,C_549) ),
    inference(superposition,[status(thm),theory(equality)],[c_15481,c_30])).

tff(c_15864,plain,(
    ! [A_548,C_550,C_549] : k1_enumset1(A_548,C_550,C_549) = k1_enumset1(A_548,C_549,C_550) ),
    inference(superposition,[status(thm),theory(equality)],[c_15858,c_30])).

tff(c_114734,plain,(
    ! [C_1337,C_1338] : k1_enumset1(C_1337,C_1338,C_1337) = k2_tarski(C_1338,C_1337) ),
    inference(superposition,[status(thm),theory(equality)],[c_114459,c_15864])).

tff(c_15413,plain,(
    ! [C_545,C_544] : k2_tarski(C_545,C_544) = k2_tarski(C_544,C_545) ),
    inference(superposition,[status(thm),theory(equality)],[c_15263,c_14857])).

tff(c_34,plain,(
    k1_enumset1('#skF_3','#skF_3','#skF_4') != k2_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_15480,plain,(
    k1_enumset1('#skF_3','#skF_3','#skF_4') != k2_tarski('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15413,c_34])).

tff(c_15885,plain,(
    k1_enumset1('#skF_3','#skF_4','#skF_3') != k2_tarski('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15864,c_15480])).

tff(c_115039,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_114734,c_15885])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:51:24 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 25.87/16.84  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 25.87/16.85  
% 25.87/16.85  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 25.87/16.85  %$ r2_hidden > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 25.87/16.85  
% 25.87/16.85  %Foreground sorts:
% 25.87/16.85  
% 25.87/16.85  
% 25.87/16.85  %Background operators:
% 25.87/16.85  
% 25.87/16.85  
% 25.87/16.85  %Foreground operators:
% 25.87/16.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 25.87/16.85  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 25.87/16.85  tff(k1_tarski, type, k1_tarski: $i > $i).
% 25.87/16.85  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 25.87/16.85  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 25.87/16.85  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 25.87/16.85  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 25.87/16.85  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 25.87/16.85  tff('#skF_3', type, '#skF_3': $i).
% 25.87/16.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 25.87/16.85  tff('#skF_4', type, '#skF_4': $i).
% 25.87/16.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 25.87/16.85  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 25.87/16.85  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 25.87/16.85  
% 25.87/16.88  tff(f_44, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 25.87/16.88  tff(f_48, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 25.87/16.88  tff(f_46, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_enumset1)).
% 25.87/16.88  tff(f_42, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 25.87/16.88  tff(f_51, negated_conjecture, ~(![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 25.87/16.88  tff(c_28, plain, (![A_10, B_11]: (k2_xboole_0(k1_tarski(A_10), k1_tarski(B_11))=k2_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 25.87/16.88  tff(c_32, plain, (![A_15]: (k2_tarski(A_15, A_15)=k1_tarski(A_15))), inference(cnfTransformation, [status(thm)], [f_48])).
% 25.87/16.88  tff(c_65, plain, (![A_30, B_31, C_32]: (k2_xboole_0(k1_tarski(A_30), k2_tarski(B_31, C_32))=k1_enumset1(A_30, B_31, C_32))), inference(cnfTransformation, [status(thm)], [f_46])).
% 25.87/16.88  tff(c_74, plain, (![A_30, A_15]: (k2_xboole_0(k1_tarski(A_30), k1_tarski(A_15))=k1_enumset1(A_30, A_15, A_15))), inference(superposition, [status(thm), theory('equality')], [c_32, c_65])).
% 25.87/16.88  tff(c_78, plain, (![A_33, A_34]: (k1_enumset1(A_33, A_34, A_34)=k2_tarski(A_33, A_34))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_74])).
% 25.87/16.88  tff(c_6, plain, (![E_9, A_3, B_4]: (r2_hidden(E_9, k1_enumset1(A_3, B_4, E_9)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 25.87/16.88  tff(c_84, plain, (![A_34, A_33]: (r2_hidden(A_34, k2_tarski(A_33, A_34)))), inference(superposition, [status(thm), theory('equality')], [c_78, c_6])).
% 25.87/16.88  tff(c_10, plain, (![E_9, B_4, C_5]: (r2_hidden(E_9, k1_enumset1(E_9, B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 25.87/16.88  tff(c_90, plain, (![A_33, A_34]: (r2_hidden(A_33, k2_tarski(A_33, A_34)))), inference(superposition, [status(thm), theory('equality')], [c_78, c_10])).
% 25.87/16.88  tff(c_77, plain, (![A_30, A_15]: (k1_enumset1(A_30, A_15, A_15)=k2_tarski(A_30, A_15))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_74])).
% 25.87/16.88  tff(c_169, plain, (![A_81, B_82, C_83, D_84]: ('#skF_1'(A_81, B_82, C_83, D_84)=C_83 | '#skF_1'(A_81, B_82, C_83, D_84)=B_82 | '#skF_1'(A_81, B_82, C_83, D_84)=A_81 | r2_hidden('#skF_2'(A_81, B_82, C_83, D_84), D_84) | k1_enumset1(A_81, B_82, C_83)=D_84)), inference(cnfTransformation, [status(thm)], [f_42])).
% 25.87/16.88  tff(c_4, plain, (![E_9, C_5, B_4, A_3]: (E_9=C_5 | E_9=B_4 | E_9=A_3 | ~r2_hidden(E_9, k1_enumset1(A_3, B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 25.87/16.88  tff(c_184, plain, (![A_3, A_81, B_82, C_83, C_5, B_4]: ('#skF_2'(A_81, B_82, C_83, k1_enumset1(A_3, B_4, C_5))=C_5 | '#skF_2'(A_81, B_82, C_83, k1_enumset1(A_3, B_4, C_5))=B_4 | '#skF_2'(A_81, B_82, C_83, k1_enumset1(A_3, B_4, C_5))=A_3 | '#skF_1'(A_81, B_82, C_83, k1_enumset1(A_3, B_4, C_5))=C_83 | '#skF_1'(A_81, B_82, C_83, k1_enumset1(A_3, B_4, C_5))=B_82 | '#skF_1'(A_81, B_82, C_83, k1_enumset1(A_3, B_4, C_5))=A_81 | k1_enumset1(A_81, B_82, C_83)=k1_enumset1(A_3, B_4, C_5))), inference(resolution, [status(thm)], [c_169, c_4])).
% 25.87/16.88  tff(c_803, plain, (![A_3, A_81, B_82, C_83, C_5]: ('#skF_2'(A_81, B_82, C_83, k1_enumset1(A_3, C_5, C_5))=A_3 | '#skF_1'(A_81, B_82, C_83, k1_enumset1(A_3, C_5, C_5))=C_83 | '#skF_1'(A_81, B_82, C_83, k1_enumset1(A_3, C_5, C_5))=B_82 | '#skF_1'(A_81, B_82, C_83, k1_enumset1(A_3, C_5, C_5))=A_81 | k1_enumset1(A_81, B_82, C_83)=k1_enumset1(A_3, C_5, C_5) | '#skF_2'(A_81, B_82, C_83, k1_enumset1(A_3, C_5, C_5))=C_5)), inference(factorization, [status(thm), theory('equality')], [c_184])).
% 25.87/16.88  tff(c_2639, plain, (![C_151, B_152, A_150, A_148, C_149]: ('#skF_2'(A_148, B_152, C_149, k2_tarski(A_150, C_151))=A_150 | '#skF_1'(A_148, B_152, C_149, k2_tarski(A_150, C_151))=C_149 | '#skF_1'(A_148, B_152, C_149, k2_tarski(A_150, C_151))=B_152 | '#skF_1'(A_148, B_152, C_149, k2_tarski(A_150, C_151))=A_148 | k2_tarski(A_150, C_151)=k1_enumset1(A_148, B_152, C_149) | '#skF_2'(A_148, B_152, C_149, k2_tarski(A_150, C_151))=C_151)), inference(demodulation, [status(thm), theory('equality')], [c_77, c_77, c_77, c_77, c_77, c_77, c_803])).
% 25.87/16.88  tff(c_22, plain, (![A_3, B_4, C_5, D_6]: ('#skF_1'(A_3, B_4, C_5, D_6)=C_5 | '#skF_1'(A_3, B_4, C_5, D_6)=B_4 | '#skF_1'(A_3, B_4, C_5, D_6)=A_3 | '#skF_2'(A_3, B_4, C_5, D_6)!=A_3 | k1_enumset1(A_3, B_4, C_5)=D_6)), inference(cnfTransformation, [status(thm)], [f_42])).
% 25.87/16.88  tff(c_9545, plain, (![C_444, B_445, C_446, A_447]: ('#skF_2'(C_444, B_445, C_446, k2_tarski(A_447, C_444))=A_447 | '#skF_1'(C_444, B_445, C_446, k2_tarski(A_447, C_444))=C_446 | '#skF_1'(C_444, B_445, C_446, k2_tarski(A_447, C_444))=B_445 | '#skF_1'(C_444, B_445, C_446, k2_tarski(A_447, C_444))=C_444 | k2_tarski(A_447, C_444)=k1_enumset1(C_444, B_445, C_446))), inference(superposition, [status(thm), theory('equality')], [c_2639, c_22])).
% 25.87/16.88  tff(c_14, plain, (![A_3, B_4, C_5, D_6]: ('#skF_1'(A_3, B_4, C_5, D_6)=C_5 | '#skF_1'(A_3, B_4, C_5, D_6)=B_4 | '#skF_1'(A_3, B_4, C_5, D_6)=A_3 | '#skF_2'(A_3, B_4, C_5, D_6)!=C_5 | k1_enumset1(A_3, B_4, C_5)=D_6)), inference(cnfTransformation, [status(thm)], [f_42])).
% 25.87/16.88  tff(c_9590, plain, (![C_444, B_445, C_446]: ('#skF_1'(C_444, B_445, C_446, k2_tarski(C_446, C_444))=C_446 | '#skF_1'(C_444, B_445, C_446, k2_tarski(C_446, C_444))=B_445 | '#skF_1'(C_444, B_445, C_446, k2_tarski(C_446, C_444))=C_444 | k1_enumset1(C_444, B_445, C_446)=k2_tarski(C_446, C_444))), inference(superposition, [status(thm), theory('equality')], [c_9545, c_14])).
% 25.87/16.88  tff(c_10557, plain, (![C_470, C_471]: ('#skF_1'(C_470, C_470, C_471, k2_tarski(C_471, C_470))=C_471 | k1_enumset1(C_470, C_470, C_471)=k2_tarski(C_471, C_470) | '#skF_1'(C_470, C_470, C_471, k2_tarski(C_471, C_470))=C_470)), inference(factorization, [status(thm), theory('equality')], [c_9590])).
% 25.87/16.88  tff(c_149, plain, (![A_61, B_62, C_63, D_64]: (~r2_hidden('#skF_1'(A_61, B_62, C_63, D_64), D_64) | r2_hidden('#skF_2'(A_61, B_62, C_63, D_64), D_64) | k1_enumset1(A_61, B_62, C_63)=D_64)), inference(cnfTransformation, [status(thm)], [f_42])).
% 25.87/16.88  tff(c_96, plain, (![E_35, C_36, B_37, A_38]: (E_35=C_36 | E_35=B_37 | E_35=A_38 | ~r2_hidden(E_35, k1_enumset1(A_38, B_37, C_36)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 25.87/16.88  tff(c_99, plain, (![E_35, A_15, A_30]: (E_35=A_15 | E_35=A_15 | E_35=A_30 | ~r2_hidden(E_35, k2_tarski(A_30, A_15)))), inference(superposition, [status(thm), theory('equality')], [c_77, c_96])).
% 25.87/16.88  tff(c_163, plain, (![A_15, A_61, B_62, C_63, A_30]: ('#skF_2'(A_61, B_62, C_63, k2_tarski(A_30, A_15))=A_15 | '#skF_2'(A_61, B_62, C_63, k2_tarski(A_30, A_15))=A_30 | ~r2_hidden('#skF_1'(A_61, B_62, C_63, k2_tarski(A_30, A_15)), k2_tarski(A_30, A_15)) | k2_tarski(A_30, A_15)=k1_enumset1(A_61, B_62, C_63))), inference(resolution, [status(thm)], [c_149, c_99])).
% 25.87/16.88  tff(c_10589, plain, (![C_470, C_471]: ('#skF_2'(C_470, C_470, C_471, k2_tarski(C_471, C_470))=C_470 | '#skF_2'(C_470, C_470, C_471, k2_tarski(C_471, C_470))=C_471 | ~r2_hidden(C_471, k2_tarski(C_471, C_470)) | k1_enumset1(C_470, C_470, C_471)=k2_tarski(C_471, C_470) | k1_enumset1(C_470, C_470, C_471)=k2_tarski(C_471, C_470) | '#skF_1'(C_470, C_470, C_471, k2_tarski(C_471, C_470))=C_470)), inference(superposition, [status(thm), theory('equality')], [c_10557, c_163])).
% 25.87/16.88  tff(c_109308, plain, (![C_1316, C_1317]: ('#skF_2'(C_1316, C_1316, C_1317, k2_tarski(C_1317, C_1316))=C_1316 | '#skF_2'(C_1316, C_1316, C_1317, k2_tarski(C_1317, C_1316))=C_1317 | k1_enumset1(C_1316, C_1316, C_1317)=k2_tarski(C_1317, C_1316) | '#skF_1'(C_1316, C_1316, C_1317, k2_tarski(C_1317, C_1316))=C_1316)), inference(demodulation, [status(thm), theory('equality')], [c_90, c_10589])).
% 25.87/16.88  tff(c_9948, plain, (![C_453, B_454, C_455]: ('#skF_1'(C_453, B_454, C_455, k2_tarski(C_455, C_453))=C_455 | '#skF_1'(C_453, B_454, C_455, k2_tarski(C_455, C_453))=B_454 | '#skF_1'(C_453, B_454, C_455, k2_tarski(C_455, C_453))=C_453 | k1_enumset1(C_453, B_454, C_455)=k2_tarski(C_455, C_453))), inference(superposition, [status(thm), theory('equality')], [c_9545, c_14])).
% 25.87/16.88  tff(c_16, plain, (![A_3, B_4, C_5, D_6]: (~r2_hidden('#skF_1'(A_3, B_4, C_5, D_6), D_6) | '#skF_2'(A_3, B_4, C_5, D_6)!=B_4 | k1_enumset1(A_3, B_4, C_5)=D_6)), inference(cnfTransformation, [status(thm)], [f_42])).
% 25.87/16.88  tff(c_9976, plain, (![C_455, C_453, B_454]: (~r2_hidden(C_455, k2_tarski(C_455, C_453)) | '#skF_2'(C_453, B_454, C_455, k2_tarski(C_455, C_453))!=B_454 | k1_enumset1(C_453, B_454, C_455)=k2_tarski(C_455, C_453) | '#skF_1'(C_453, B_454, C_455, k2_tarski(C_455, C_453))=B_454 | '#skF_1'(C_453, B_454, C_455, k2_tarski(C_455, C_453))=C_453 | k1_enumset1(C_453, B_454, C_455)=k2_tarski(C_455, C_453))), inference(superposition, [status(thm), theory('equality')], [c_9948, c_16])).
% 25.87/16.88  tff(c_10143, plain, (![C_453, B_454, C_455]: ('#skF_2'(C_453, B_454, C_455, k2_tarski(C_455, C_453))!=B_454 | '#skF_1'(C_453, B_454, C_455, k2_tarski(C_455, C_453))=B_454 | '#skF_1'(C_453, B_454, C_455, k2_tarski(C_455, C_453))=C_453 | k1_enumset1(C_453, B_454, C_455)=k2_tarski(C_455, C_453))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_9976])).
% 25.87/16.88  tff(c_110058, plain, (![C_1318, C_1319]: ('#skF_2'(C_1318, C_1318, C_1319, k2_tarski(C_1319, C_1318))=C_1319 | k1_enumset1(C_1318, C_1318, C_1319)=k2_tarski(C_1319, C_1318) | '#skF_1'(C_1318, C_1318, C_1319, k2_tarski(C_1319, C_1318))=C_1318)), inference(superposition, [status(thm), theory('equality')], [c_109308, c_10143])).
% 25.87/16.88  tff(c_836, plain, (![B_115, A_112, A_110, B_114, C_111, C_113]: ('#skF_2'(A_110, B_114, C_111, k1_enumset1(A_112, B_115, C_113))=C_113 | '#skF_2'(A_110, B_114, C_111, k1_enumset1(A_112, B_115, C_113))=B_115 | '#skF_2'(A_110, B_114, C_111, k1_enumset1(A_112, B_115, C_113))=A_112 | '#skF_1'(A_110, B_114, C_111, k1_enumset1(A_112, B_115, C_113))=C_111 | '#skF_1'(A_110, B_114, C_111, k1_enumset1(A_112, B_115, C_113))=B_114 | '#skF_1'(A_110, B_114, C_111, k1_enumset1(A_112, B_115, C_113))=A_110 | k1_enumset1(A_112, B_115, C_113)=k1_enumset1(A_110, B_114, C_111))), inference(resolution, [status(thm)], [c_169, c_4])).
% 25.87/16.88  tff(c_18, plain, (![A_3, B_4, C_5, D_6]: ('#skF_1'(A_3, B_4, C_5, D_6)=C_5 | '#skF_1'(A_3, B_4, C_5, D_6)=B_4 | '#skF_1'(A_3, B_4, C_5, D_6)=A_3 | '#skF_2'(A_3, B_4, C_5, D_6)!=B_4 | k1_enumset1(A_3, B_4, C_5)=D_6)), inference(cnfTransformation, [status(thm)], [f_42])).
% 25.87/16.88  tff(c_6530, plain, (![C_323, A_326, A_322, C_325, B_324]: ('#skF_2'(A_322, B_324, C_325, k1_enumset1(A_326, B_324, C_323))=C_323 | '#skF_2'(A_322, B_324, C_325, k1_enumset1(A_326, B_324, C_323))=A_326 | '#skF_1'(A_322, B_324, C_325, k1_enumset1(A_326, B_324, C_323))=C_325 | '#skF_1'(A_322, B_324, C_325, k1_enumset1(A_326, B_324, C_323))=B_324 | '#skF_1'(A_322, B_324, C_325, k1_enumset1(A_326, B_324, C_323))=A_322 | k1_enumset1(A_326, B_324, C_323)=k1_enumset1(A_322, B_324, C_325))), inference(superposition, [status(thm), theory('equality')], [c_836, c_18])).
% 25.87/16.88  tff(c_6602, plain, (![A_322, C_323, C_325, A_326]: ('#skF_2'(A_322, C_323, C_325, k1_enumset1(A_326, C_323, C_323))=A_326 | '#skF_1'(A_322, C_323, C_325, k1_enumset1(A_326, C_323, C_323))=C_325 | '#skF_1'(A_322, C_323, C_325, k1_enumset1(A_326, C_323, C_323))=C_323 | '#skF_1'(A_322, C_323, C_325, k1_enumset1(A_326, C_323, C_323))=A_322 | k1_enumset1(A_326, C_323, C_323)=k1_enumset1(A_322, C_323, C_325))), inference(superposition, [status(thm), theory('equality')], [c_6530, c_18])).
% 25.87/16.88  tff(c_10288, plain, (![A_464, C_465, C_466, A_467]: ('#skF_2'(A_464, C_465, C_466, k2_tarski(A_467, C_465))=A_467 | '#skF_1'(A_464, C_465, C_466, k2_tarski(A_467, C_465))=C_466 | '#skF_1'(A_464, C_465, C_466, k2_tarski(A_467, C_465))=C_465 | '#skF_1'(A_464, C_465, C_466, k2_tarski(A_467, C_465))=A_464 | k2_tarski(A_467, C_465)=k1_enumset1(A_464, C_465, C_466))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_77, c_77, c_77, c_77, c_6602])).
% 25.87/16.88  tff(c_11573, plain, (![A_489, C_490, C_491]: ('#skF_1'(A_489, C_490, C_491, k2_tarski(C_491, C_490))=C_491 | '#skF_1'(A_489, C_490, C_491, k2_tarski(C_491, C_490))=C_490 | '#skF_1'(A_489, C_490, C_491, k2_tarski(C_491, C_490))=A_489 | k1_enumset1(A_489, C_490, C_491)=k2_tarski(C_491, C_490))), inference(superposition, [status(thm), theory('equality')], [c_10288, c_14])).
% 25.87/16.88  tff(c_12, plain, (![A_3, B_4, C_5, D_6]: (~r2_hidden('#skF_1'(A_3, B_4, C_5, D_6), D_6) | '#skF_2'(A_3, B_4, C_5, D_6)!=C_5 | k1_enumset1(A_3, B_4, C_5)=D_6)), inference(cnfTransformation, [status(thm)], [f_42])).
% 25.87/16.88  tff(c_11632, plain, (![C_491, C_490, A_489]: (~r2_hidden(C_491, k2_tarski(C_491, C_490)) | '#skF_2'(A_489, C_490, C_491, k2_tarski(C_491, C_490))!=C_491 | k1_enumset1(A_489, C_490, C_491)=k2_tarski(C_491, C_490) | '#skF_1'(A_489, C_490, C_491, k2_tarski(C_491, C_490))=C_490 | '#skF_1'(A_489, C_490, C_491, k2_tarski(C_491, C_490))=A_489 | k1_enumset1(A_489, C_490, C_491)=k2_tarski(C_491, C_490))), inference(superposition, [status(thm), theory('equality')], [c_11573, c_12])).
% 25.87/16.88  tff(c_11934, plain, (![A_489, C_490, C_491]: ('#skF_2'(A_489, C_490, C_491, k2_tarski(C_491, C_490))!=C_491 | '#skF_1'(A_489, C_490, C_491, k2_tarski(C_491, C_490))=C_490 | '#skF_1'(A_489, C_490, C_491, k2_tarski(C_491, C_490))=A_489 | k1_enumset1(A_489, C_490, C_491)=k2_tarski(C_491, C_490))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_11632])).
% 25.87/16.88  tff(c_110731, plain, (![C_1320, C_1321]: (k1_enumset1(C_1320, C_1320, C_1321)=k2_tarski(C_1321, C_1320) | '#skF_1'(C_1320, C_1320, C_1321, k2_tarski(C_1321, C_1320))=C_1320)), inference(superposition, [status(thm), theory('equality')], [c_110058, c_11934])).
% 25.87/16.88  tff(c_110910, plain, (![C_1320, C_1321]: ('#skF_2'(C_1320, C_1320, C_1321, k2_tarski(C_1321, C_1320))=C_1320 | '#skF_2'(C_1320, C_1320, C_1321, k2_tarski(C_1321, C_1320))=C_1321 | ~r2_hidden(C_1320, k2_tarski(C_1321, C_1320)) | k1_enumset1(C_1320, C_1320, C_1321)=k2_tarski(C_1321, C_1320) | k1_enumset1(C_1320, C_1320, C_1321)=k2_tarski(C_1321, C_1320))), inference(superposition, [status(thm), theory('equality')], [c_110731, c_163])).
% 25.87/16.88  tff(c_111751, plain, (![C_1332, C_1333]: ('#skF_2'(C_1332, C_1332, C_1333, k2_tarski(C_1333, C_1332))=C_1332 | '#skF_2'(C_1332, C_1332, C_1333, k2_tarski(C_1333, C_1332))=C_1333 | k1_enumset1(C_1332, C_1332, C_1333)=k2_tarski(C_1333, C_1332))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_110910])).
% 25.87/16.88  tff(c_20, plain, (![A_3, B_4, C_5, D_6]: (~r2_hidden('#skF_1'(A_3, B_4, C_5, D_6), D_6) | '#skF_2'(A_3, B_4, C_5, D_6)!=A_3 | k1_enumset1(A_3, B_4, C_5)=D_6)), inference(cnfTransformation, [status(thm)], [f_42])).
% 25.87/16.88  tff(c_110919, plain, (![C_1320, C_1321]: (~r2_hidden(C_1320, k2_tarski(C_1321, C_1320)) | '#skF_2'(C_1320, C_1320, C_1321, k2_tarski(C_1321, C_1320))!=C_1320 | k1_enumset1(C_1320, C_1320, C_1321)=k2_tarski(C_1321, C_1320) | k1_enumset1(C_1320, C_1320, C_1321)=k2_tarski(C_1321, C_1320))), inference(superposition, [status(thm), theory('equality')], [c_110731, c_20])).
% 25.87/16.88  tff(c_111116, plain, (![C_1320, C_1321]: ('#skF_2'(C_1320, C_1320, C_1321, k2_tarski(C_1321, C_1320))!=C_1320 | k1_enumset1(C_1320, C_1320, C_1321)=k2_tarski(C_1321, C_1320))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_110919])).
% 25.87/16.88  tff(c_112422, plain, (![C_1334, C_1335]: ('#skF_2'(C_1334, C_1334, C_1335, k2_tarski(C_1335, C_1334))=C_1335 | k1_enumset1(C_1334, C_1334, C_1335)=k2_tarski(C_1335, C_1334))), inference(superposition, [status(thm), theory('equality')], [c_111751, c_111116])).
% 25.87/16.88  tff(c_110913, plain, (![C_1320, C_1321]: (~r2_hidden(C_1320, k2_tarski(C_1321, C_1320)) | '#skF_2'(C_1320, C_1320, C_1321, k2_tarski(C_1321, C_1320))!=C_1321 | k1_enumset1(C_1320, C_1320, C_1321)=k2_tarski(C_1321, C_1320) | k1_enumset1(C_1320, C_1320, C_1321)=k2_tarski(C_1321, C_1320))), inference(superposition, [status(thm), theory('equality')], [c_110731, c_12])).
% 25.87/16.88  tff(c_111112, plain, (![C_1320, C_1321]: ('#skF_2'(C_1320, C_1320, C_1321, k2_tarski(C_1321, C_1320))!=C_1321 | k1_enumset1(C_1320, C_1320, C_1321)=k2_tarski(C_1321, C_1320))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_110913])).
% 25.87/16.88  tff(c_114459, plain, (![C_1337, C_1338]: (k1_enumset1(C_1337, C_1337, C_1338)=k2_tarski(C_1338, C_1337))), inference(superposition, [status(thm), theory('equality')], [c_112422, c_111112])).
% 25.87/16.88  tff(c_9587, plain, (![C_444, B_445, C_446]: ('#skF_1'(C_444, B_445, C_446, k2_tarski(B_445, C_444))=C_446 | '#skF_1'(C_444, B_445, C_446, k2_tarski(B_445, C_444))=B_445 | '#skF_1'(C_444, B_445, C_446, k2_tarski(B_445, C_444))=C_444 | k1_enumset1(C_444, B_445, C_446)=k2_tarski(B_445, C_444))), inference(superposition, [status(thm), theory('equality')], [c_9545, c_18])).
% 25.87/16.88  tff(c_9609, plain, (![C_444, C_446]: ('#skF_1'(C_444, C_446, C_446, k2_tarski(C_446, C_444))=C_444 | k1_enumset1(C_444, C_446, C_446)=k2_tarski(C_446, C_444) | '#skF_1'(C_444, C_446, C_446, k2_tarski(C_446, C_444))=C_446)), inference(factorization, [status(thm), theory('equality')], [c_9587])).
% 25.87/16.88  tff(c_9782, plain, (![C_451, C_452]: ('#skF_1'(C_451, C_452, C_452, k2_tarski(C_452, C_451))=C_451 | k2_tarski(C_452, C_451)=k2_tarski(C_451, C_452) | '#skF_1'(C_451, C_452, C_452, k2_tarski(C_452, C_451))=C_452)), inference(demodulation, [status(thm), theory('equality')], [c_77, c_9609])).
% 25.87/16.88  tff(c_9800, plain, (![C_451, C_452]: ('#skF_2'(C_451, C_452, C_452, k2_tarski(C_452, C_451))=C_451 | '#skF_2'(C_451, C_452, C_452, k2_tarski(C_452, C_451))=C_452 | ~r2_hidden(C_451, k2_tarski(C_452, C_451)) | k1_enumset1(C_451, C_452, C_452)=k2_tarski(C_452, C_451) | k2_tarski(C_452, C_451)=k2_tarski(C_451, C_452) | '#skF_1'(C_451, C_452, C_452, k2_tarski(C_452, C_451))=C_452)), inference(superposition, [status(thm), theory('equality')], [c_9782, c_163])).
% 25.87/16.88  tff(c_14105, plain, (![C_532, C_533]: ('#skF_2'(C_532, C_533, C_533, k2_tarski(C_533, C_532))=C_532 | '#skF_2'(C_532, C_533, C_533, k2_tarski(C_533, C_532))=C_533 | k2_tarski(C_533, C_532)=k2_tarski(C_532, C_533) | '#skF_1'(C_532, C_533, C_533, k2_tarski(C_533, C_532))=C_533)), inference(demodulation, [status(thm), theory('equality')], [c_77, c_84, c_9800])).
% 25.87/16.88  tff(c_9809, plain, (![C_451, C_452]: (~r2_hidden(C_451, k2_tarski(C_452, C_451)) | '#skF_2'(C_451, C_452, C_452, k2_tarski(C_452, C_451))!=C_451 | k1_enumset1(C_451, C_452, C_452)=k2_tarski(C_452, C_451) | k2_tarski(C_452, C_451)=k2_tarski(C_451, C_452) | '#skF_1'(C_451, C_452, C_452, k2_tarski(C_452, C_451))=C_452)), inference(superposition, [status(thm), theory('equality')], [c_9782, c_20])).
% 25.87/16.88  tff(c_9887, plain, (![C_451, C_452]: ('#skF_2'(C_451, C_452, C_452, k2_tarski(C_452, C_451))!=C_451 | k2_tarski(C_452, C_451)=k2_tarski(C_451, C_452) | '#skF_1'(C_451, C_452, C_452, k2_tarski(C_452, C_451))=C_452)), inference(demodulation, [status(thm), theory('equality')], [c_77, c_84, c_9809])).
% 25.87/16.88  tff(c_14406, plain, (![C_534, C_535]: ('#skF_2'(C_534, C_535, C_535, k2_tarski(C_535, C_534))=C_535 | k2_tarski(C_535, C_534)=k2_tarski(C_534, C_535) | '#skF_1'(C_534, C_535, C_535, k2_tarski(C_535, C_534))=C_535)), inference(superposition, [status(thm), theory('equality')], [c_14105, c_9887])).
% 25.87/16.88  tff(c_9803, plain, (![C_451, C_452]: (~r2_hidden(C_451, k2_tarski(C_452, C_451)) | '#skF_2'(C_451, C_452, C_452, k2_tarski(C_452, C_451))!=C_452 | k1_enumset1(C_451, C_452, C_452)=k2_tarski(C_452, C_451) | k2_tarski(C_452, C_451)=k2_tarski(C_451, C_452) | '#skF_1'(C_451, C_452, C_452, k2_tarski(C_452, C_451))=C_452)), inference(superposition, [status(thm), theory('equality')], [c_9782, c_12])).
% 25.87/16.88  tff(c_9883, plain, (![C_451, C_452]: ('#skF_2'(C_451, C_452, C_452, k2_tarski(C_452, C_451))!=C_452 | k2_tarski(C_452, C_451)=k2_tarski(C_451, C_452) | '#skF_1'(C_451, C_452, C_452, k2_tarski(C_452, C_451))=C_452)), inference(demodulation, [status(thm), theory('equality')], [c_77, c_84, c_9803])).
% 25.87/16.88  tff(c_14628, plain, (![C_537, C_536]: (k2_tarski(C_537, C_536)=k2_tarski(C_536, C_537) | '#skF_1'(C_537, C_536, C_536, k2_tarski(C_536, C_537))=C_536)), inference(superposition, [status(thm), theory('equality')], [c_14406, c_9883])).
% 25.87/16.88  tff(c_14732, plain, (![C_537, C_536]: ('#skF_2'(C_537, C_536, C_536, k2_tarski(C_536, C_537))=C_537 | '#skF_2'(C_537, C_536, C_536, k2_tarski(C_536, C_537))=C_536 | ~r2_hidden(C_536, k2_tarski(C_536, C_537)) | k1_enumset1(C_537, C_536, C_536)=k2_tarski(C_536, C_537) | k2_tarski(C_537, C_536)=k2_tarski(C_536, C_537))), inference(superposition, [status(thm), theory('equality')], [c_14628, c_163])).
% 25.87/16.88  tff(c_14980, plain, (![C_542, C_543]: ('#skF_2'(C_542, C_543, C_543, k2_tarski(C_543, C_542))=C_542 | '#skF_2'(C_542, C_543, C_543, k2_tarski(C_543, C_542))=C_543 | k2_tarski(C_543, C_542)=k2_tarski(C_542, C_543))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_90, c_14732])).
% 25.87/16.88  tff(c_14741, plain, (![C_536, C_537]: (~r2_hidden(C_536, k2_tarski(C_536, C_537)) | '#skF_2'(C_537, C_536, C_536, k2_tarski(C_536, C_537))!=C_537 | k1_enumset1(C_537, C_536, C_536)=k2_tarski(C_536, C_537) | k2_tarski(C_537, C_536)=k2_tarski(C_536, C_537))), inference(superposition, [status(thm), theory('equality')], [c_14628, c_20])).
% 25.87/16.88  tff(c_14861, plain, (![C_537, C_536]: ('#skF_2'(C_537, C_536, C_536, k2_tarski(C_536, C_537))!=C_537 | k2_tarski(C_537, C_536)=k2_tarski(C_536, C_537))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_90, c_14741])).
% 25.87/16.88  tff(c_15263, plain, (![C_544, C_545]: ('#skF_2'(C_544, C_545, C_545, k2_tarski(C_545, C_544))=C_545 | k2_tarski(C_545, C_544)=k2_tarski(C_544, C_545))), inference(superposition, [status(thm), theory('equality')], [c_14980, c_14861])).
% 25.87/16.88  tff(c_14735, plain, (![C_536, C_537]: (~r2_hidden(C_536, k2_tarski(C_536, C_537)) | '#skF_2'(C_537, C_536, C_536, k2_tarski(C_536, C_537))!=C_536 | k1_enumset1(C_537, C_536, C_536)=k2_tarski(C_536, C_537) | k2_tarski(C_537, C_536)=k2_tarski(C_536, C_537))), inference(superposition, [status(thm), theory('equality')], [c_14628, c_12])).
% 25.87/16.88  tff(c_14857, plain, (![C_537, C_536]: ('#skF_2'(C_537, C_536, C_536, k2_tarski(C_536, C_537))!=C_536 | k2_tarski(C_537, C_536)=k2_tarski(C_536, C_537))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_90, c_14735])).
% 25.87/16.88  tff(c_15481, plain, (![C_547, C_546]: (k2_tarski(C_547, C_546)=k2_tarski(C_546, C_547))), inference(superposition, [status(thm), theory('equality')], [c_15263, c_14857])).
% 25.87/16.88  tff(c_30, plain, (![A_12, B_13, C_14]: (k2_xboole_0(k1_tarski(A_12), k2_tarski(B_13, C_14))=k1_enumset1(A_12, B_13, C_14))), inference(cnfTransformation, [status(thm)], [f_46])).
% 25.87/16.88  tff(c_15858, plain, (![A_548, C_549, C_550]: (k2_xboole_0(k1_tarski(A_548), k2_tarski(C_549, C_550))=k1_enumset1(A_548, C_550, C_549))), inference(superposition, [status(thm), theory('equality')], [c_15481, c_30])).
% 25.87/16.88  tff(c_15864, plain, (![A_548, C_550, C_549]: (k1_enumset1(A_548, C_550, C_549)=k1_enumset1(A_548, C_549, C_550))), inference(superposition, [status(thm), theory('equality')], [c_15858, c_30])).
% 25.87/16.88  tff(c_114734, plain, (![C_1337, C_1338]: (k1_enumset1(C_1337, C_1338, C_1337)=k2_tarski(C_1338, C_1337))), inference(superposition, [status(thm), theory('equality')], [c_114459, c_15864])).
% 25.87/16.88  tff(c_15413, plain, (![C_545, C_544]: (k2_tarski(C_545, C_544)=k2_tarski(C_544, C_545))), inference(superposition, [status(thm), theory('equality')], [c_15263, c_14857])).
% 25.87/16.88  tff(c_34, plain, (k1_enumset1('#skF_3', '#skF_3', '#skF_4')!=k2_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_51])).
% 25.87/16.88  tff(c_15480, plain, (k1_enumset1('#skF_3', '#skF_3', '#skF_4')!=k2_tarski('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_15413, c_34])).
% 25.87/16.88  tff(c_15885, plain, (k1_enumset1('#skF_3', '#skF_4', '#skF_3')!=k2_tarski('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_15864, c_15480])).
% 25.87/16.88  tff(c_115039, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_114734, c_15885])).
% 25.87/16.88  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 25.87/16.88  
% 25.87/16.88  Inference rules
% 25.87/16.88  ----------------------
% 25.87/16.88  #Ref     : 0
% 25.87/16.88  #Sup     : 16721
% 25.87/16.88  #Fact    : 304
% 25.87/16.88  #Define  : 0
% 25.87/16.88  #Split   : 0
% 25.87/16.88  #Chain   : 0
% 25.87/16.88  #Close   : 0
% 25.87/16.88  
% 25.87/16.88  Ordering : KBO
% 25.87/16.88  
% 25.87/16.88  Simplification rules
% 25.87/16.88  ----------------------
% 25.87/16.88  #Subsume      : 6977
% 25.87/16.88  #Demod        : 54639
% 25.87/16.88  #Tautology    : 8073
% 25.87/16.88  #SimpNegUnit  : 0
% 25.87/16.88  #BackRed      : 231
% 25.87/16.88  
% 25.87/16.88  #Partial instantiations: 0
% 25.87/16.88  #Strategies tried      : 1
% 25.87/16.88  
% 25.87/16.88  Timing (in seconds)
% 25.87/16.88  ----------------------
% 25.87/16.88  Preprocessing        : 0.30
% 25.87/16.88  Parsing              : 0.15
% 25.87/16.88  CNF conversion       : 0.02
% 25.87/16.88  Main loop            : 15.80
% 25.87/16.88  Inferencing          : 5.51
% 25.87/16.88  Reduction            : 4.24
% 25.87/16.88  Demodulation         : 3.40
% 25.87/16.88  BG Simplification    : 0.45
% 25.87/16.88  Subsumption          : 5.24
% 25.87/16.88  Abstraction          : 1.25
% 25.87/16.88  MUC search           : 0.00
% 25.87/16.88  Cooper               : 0.00
% 25.87/16.88  Total                : 16.15
% 25.87/16.88  Index Insertion      : 0.00
% 25.87/16.88  Index Deletion       : 0.00
% 25.87/16.88  Index Matching       : 0.00
% 25.87/16.88  BG Taut test         : 0.00
%------------------------------------------------------------------------------
