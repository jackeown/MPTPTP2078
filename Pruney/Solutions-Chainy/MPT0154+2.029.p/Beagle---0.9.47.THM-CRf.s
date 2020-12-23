%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:07 EST 2020

% Result     : Theorem 22.10s
% Output     : CNFRefutation 22.26s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 425 expanded)
%              Number of leaves         :   15 ( 150 expanded)
%              Depth                    :   14
%              Number of atoms          :  194 (1558 expanded)
%              Number of equality atoms :  166 (1288 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k1_enumset1 > k2_tarski > #nlpp > #skF_4 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_40,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_52,negated_conjecture,(
    ~ ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(c_8,plain,(
    ! [E_7,B_2,C_3] : r2_hidden(E_7,k1_enumset1(E_7,B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_4,plain,(
    ! [E_7,A_1,B_2] : r2_hidden(E_7,k1_enumset1(A_1,B_2,E_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_106,plain,(
    ! [A_65,B_66,C_67] :
      ( '#skF_3'(A_65,B_66,C_67) = B_66
      | '#skF_3'(A_65,B_66,C_67) = A_65
      | r2_hidden('#skF_4'(A_65,B_66,C_67),C_67)
      | k2_tarski(A_65,B_66) = C_67 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2,plain,(
    ! [E_7,C_3,B_2,A_1] :
      ( E_7 = C_3
      | E_7 = B_2
      | E_7 = A_1
      | ~ r2_hidden(E_7,k1_enumset1(A_1,B_2,C_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1420,plain,(
    ! [C_163,A_161,A_164,B_160,B_162] :
      ( '#skF_4'(A_161,B_160,k1_enumset1(A_164,B_162,C_163)) = C_163
      | '#skF_4'(A_161,B_160,k1_enumset1(A_164,B_162,C_163)) = B_162
      | '#skF_4'(A_161,B_160,k1_enumset1(A_164,B_162,C_163)) = A_164
      | '#skF_3'(A_161,B_160,k1_enumset1(A_164,B_162,C_163)) = B_160
      | '#skF_3'(A_161,B_160,k1_enumset1(A_164,B_162,C_163)) = A_161
      | k2_tarski(A_161,B_160) = k1_enumset1(A_164,B_162,C_163) ) ),
    inference(resolution,[status(thm)],[c_106,c_2])).

tff(c_34,plain,(
    ! [A_8,B_9,C_10] :
      ( '#skF_3'(A_8,B_9,C_10) = B_9
      | '#skF_3'(A_8,B_9,C_10) = A_8
      | '#skF_4'(A_8,B_9,C_10) != B_9
      | k2_tarski(A_8,B_9) = C_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_3767,plain,(
    ! [A_238,B_239,B_240,C_241] :
      ( '#skF_4'(A_238,B_239,k1_enumset1(B_239,B_240,C_241)) = C_241
      | '#skF_4'(A_238,B_239,k1_enumset1(B_239,B_240,C_241)) = B_240
      | '#skF_3'(A_238,B_239,k1_enumset1(B_239,B_240,C_241)) = B_239
      | '#skF_3'(A_238,B_239,k1_enumset1(B_239,B_240,C_241)) = A_238
      | k2_tarski(A_238,B_239) = k1_enumset1(B_239,B_240,C_241) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1420,c_34])).

tff(c_38,plain,(
    ! [A_8,B_9,C_10] :
      ( '#skF_3'(A_8,B_9,C_10) = B_9
      | '#skF_3'(A_8,B_9,C_10) = A_8
      | '#skF_4'(A_8,B_9,C_10) != A_8
      | k2_tarski(A_8,B_9) = C_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_7235,plain,(
    ! [C_353,B_354,B_355] :
      ( '#skF_4'(C_353,B_354,k1_enumset1(B_354,B_355,C_353)) = B_355
      | '#skF_3'(C_353,B_354,k1_enumset1(B_354,B_355,C_353)) = B_354
      | '#skF_3'(C_353,B_354,k1_enumset1(B_354,B_355,C_353)) = C_353
      | k1_enumset1(B_354,B_355,C_353) = k2_tarski(C_353,B_354) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3767,c_38])).

tff(c_7501,plain,(
    ! [C_356,B_357] :
      ( '#skF_3'(C_356,B_357,k1_enumset1(B_357,B_357,C_356)) = B_357
      | '#skF_3'(C_356,B_357,k1_enumset1(B_357,B_357,C_356)) = C_356
      | k1_enumset1(B_357,B_357,C_356) = k2_tarski(C_356,B_357) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7235,c_34])).

tff(c_79,plain,(
    ! [A_40,B_41,C_42] :
      ( ~ r2_hidden('#skF_3'(A_40,B_41,C_42),C_42)
      | r2_hidden('#skF_4'(A_40,B_41,C_42),C_42)
      | k2_tarski(A_40,B_41) = C_42 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_88,plain,(
    ! [B_2,C_3,A_1,A_40,B_41] :
      ( '#skF_4'(A_40,B_41,k1_enumset1(A_1,B_2,C_3)) = C_3
      | '#skF_4'(A_40,B_41,k1_enumset1(A_1,B_2,C_3)) = B_2
      | '#skF_4'(A_40,B_41,k1_enumset1(A_1,B_2,C_3)) = A_1
      | ~ r2_hidden('#skF_3'(A_40,B_41,k1_enumset1(A_1,B_2,C_3)),k1_enumset1(A_1,B_2,C_3))
      | k2_tarski(A_40,B_41) = k1_enumset1(A_1,B_2,C_3) ) ),
    inference(resolution,[status(thm)],[c_79,c_2])).

tff(c_7557,plain,(
    ! [C_356,B_357] :
      ( '#skF_4'(C_356,B_357,k1_enumset1(B_357,B_357,C_356)) = C_356
      | '#skF_4'(C_356,B_357,k1_enumset1(B_357,B_357,C_356)) = B_357
      | '#skF_4'(C_356,B_357,k1_enumset1(B_357,B_357,C_356)) = B_357
      | ~ r2_hidden(C_356,k1_enumset1(B_357,B_357,C_356))
      | k1_enumset1(B_357,B_357,C_356) = k2_tarski(C_356,B_357)
      | '#skF_3'(C_356,B_357,k1_enumset1(B_357,B_357,C_356)) = B_357
      | k1_enumset1(B_357,B_357,C_356) = k2_tarski(C_356,B_357) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7501,c_88])).

tff(c_96988,plain,(
    ! [C_1259,B_1260] :
      ( '#skF_4'(C_1259,B_1260,k1_enumset1(B_1260,B_1260,C_1259)) = C_1259
      | '#skF_4'(C_1259,B_1260,k1_enumset1(B_1260,B_1260,C_1259)) = B_1260
      | '#skF_3'(C_1259,B_1260,k1_enumset1(B_1260,B_1260,C_1259)) = B_1260
      | k1_enumset1(B_1260,B_1260,C_1259) = k2_tarski(C_1259,B_1260) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_7557])).

tff(c_36,plain,(
    ! [A_8,B_9,C_10] :
      ( ~ r2_hidden('#skF_3'(A_8,B_9,C_10),C_10)
      | '#skF_4'(A_8,B_9,C_10) != A_8
      | k2_tarski(A_8,B_9) = C_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_7560,plain,(
    ! [C_356,B_357] :
      ( ~ r2_hidden(C_356,k1_enumset1(B_357,B_357,C_356))
      | '#skF_4'(C_356,B_357,k1_enumset1(B_357,B_357,C_356)) != C_356
      | k1_enumset1(B_357,B_357,C_356) = k2_tarski(C_356,B_357)
      | '#skF_3'(C_356,B_357,k1_enumset1(B_357,B_357,C_356)) = B_357
      | k1_enumset1(B_357,B_357,C_356) = k2_tarski(C_356,B_357) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7501,c_36])).

tff(c_7625,plain,(
    ! [C_356,B_357] :
      ( '#skF_4'(C_356,B_357,k1_enumset1(B_357,B_357,C_356)) != C_356
      | '#skF_3'(C_356,B_357,k1_enumset1(B_357,B_357,C_356)) = B_357
      | k1_enumset1(B_357,B_357,C_356) = k2_tarski(C_356,B_357) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_7560])).

tff(c_97669,plain,(
    ! [C_1261,B_1262] :
      ( '#skF_4'(C_1261,B_1262,k1_enumset1(B_1262,B_1262,C_1261)) = B_1262
      | '#skF_3'(C_1261,B_1262,k1_enumset1(B_1262,B_1262,C_1261)) = B_1262
      | k1_enumset1(B_1262,B_1262,C_1261) = k2_tarski(C_1261,B_1262) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_96988,c_7625])).

tff(c_32,plain,(
    ! [A_8,B_9,C_10] :
      ( ~ r2_hidden('#skF_3'(A_8,B_9,C_10),C_10)
      | '#skF_4'(A_8,B_9,C_10) != B_9
      | k2_tarski(A_8,B_9) = C_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_7563,plain,(
    ! [C_356,B_357] :
      ( ~ r2_hidden(C_356,k1_enumset1(B_357,B_357,C_356))
      | '#skF_4'(C_356,B_357,k1_enumset1(B_357,B_357,C_356)) != B_357
      | k1_enumset1(B_357,B_357,C_356) = k2_tarski(C_356,B_357)
      | '#skF_3'(C_356,B_357,k1_enumset1(B_357,B_357,C_356)) = B_357
      | k1_enumset1(B_357,B_357,C_356) = k2_tarski(C_356,B_357) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7501,c_32])).

tff(c_7627,plain,(
    ! [C_356,B_357] :
      ( '#skF_4'(C_356,B_357,k1_enumset1(B_357,B_357,C_356)) != B_357
      | '#skF_3'(C_356,B_357,k1_enumset1(B_357,B_357,C_356)) = B_357
      | k1_enumset1(B_357,B_357,C_356) = k2_tarski(C_356,B_357) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_7563])).

tff(c_98180,plain,(
    ! [C_1263,B_1264] :
      ( '#skF_3'(C_1263,B_1264,k1_enumset1(B_1264,B_1264,C_1263)) = B_1264
      | k1_enumset1(B_1264,B_1264,C_1263) = k2_tarski(C_1263,B_1264) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_97669,c_7627])).

tff(c_98226,plain,(
    ! [C_1263,B_1264] :
      ( '#skF_4'(C_1263,B_1264,k1_enumset1(B_1264,B_1264,C_1263)) = C_1263
      | '#skF_4'(C_1263,B_1264,k1_enumset1(B_1264,B_1264,C_1263)) = B_1264
      | '#skF_4'(C_1263,B_1264,k1_enumset1(B_1264,B_1264,C_1263)) = B_1264
      | ~ r2_hidden(B_1264,k1_enumset1(B_1264,B_1264,C_1263))
      | k1_enumset1(B_1264,B_1264,C_1263) = k2_tarski(C_1263,B_1264)
      | k1_enumset1(B_1264,B_1264,C_1263) = k2_tarski(C_1263,B_1264) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_98180,c_88])).

tff(c_99965,plain,(
    ! [C_1272,B_1273] :
      ( '#skF_4'(C_1272,B_1273,k1_enumset1(B_1273,B_1273,C_1272)) = C_1272
      | '#skF_4'(C_1272,B_1273,k1_enumset1(B_1273,B_1273,C_1272)) = B_1273
      | k1_enumset1(B_1273,B_1273,C_1272) = k2_tarski(C_1272,B_1273) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_98226])).

tff(c_98229,plain,(
    ! [B_1264,C_1263] :
      ( ~ r2_hidden(B_1264,k1_enumset1(B_1264,B_1264,C_1263))
      | '#skF_4'(C_1263,B_1264,k1_enumset1(B_1264,B_1264,C_1263)) != C_1263
      | k1_enumset1(B_1264,B_1264,C_1263) = k2_tarski(C_1263,B_1264)
      | k1_enumset1(B_1264,B_1264,C_1263) = k2_tarski(C_1263,B_1264) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_98180,c_36])).

tff(c_98283,plain,(
    ! [C_1263,B_1264] :
      ( '#skF_4'(C_1263,B_1264,k1_enumset1(B_1264,B_1264,C_1263)) != C_1263
      | k1_enumset1(B_1264,B_1264,C_1263) = k2_tarski(C_1263,B_1264) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_98229])).

tff(c_100628,plain,(
    ! [C_1274,B_1275] :
      ( '#skF_4'(C_1274,B_1275,k1_enumset1(B_1275,B_1275,C_1274)) = B_1275
      | k1_enumset1(B_1275,B_1275,C_1274) = k2_tarski(C_1274,B_1275) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_99965,c_98283])).

tff(c_98232,plain,(
    ! [B_1264,C_1263] :
      ( ~ r2_hidden(B_1264,k1_enumset1(B_1264,B_1264,C_1263))
      | '#skF_4'(C_1263,B_1264,k1_enumset1(B_1264,B_1264,C_1263)) != B_1264
      | k1_enumset1(B_1264,B_1264,C_1263) = k2_tarski(C_1263,B_1264)
      | k1_enumset1(B_1264,B_1264,C_1263) = k2_tarski(C_1263,B_1264) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_98180,c_32])).

tff(c_98285,plain,(
    ! [C_1263,B_1264] :
      ( '#skF_4'(C_1263,B_1264,k1_enumset1(B_1264,B_1264,C_1263)) != B_1264
      | k1_enumset1(B_1264,B_1264,C_1263) = k2_tarski(C_1263,B_1264) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_98232])).

tff(c_101004,plain,(
    ! [B_1275,C_1274] : k1_enumset1(B_1275,B_1275,C_1274) = k2_tarski(C_1274,B_1275) ),
    inference(superposition,[status(thm),theory(equality)],[c_100628,c_98285])).

tff(c_28,plain,(
    ! [D_13,A_8] : r2_hidden(D_13,k2_tarski(A_8,D_13)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_30,plain,(
    ! [D_13,B_9] : r2_hidden(D_13,k2_tarski(D_13,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_26,plain,(
    ! [D_13,B_9,A_8] :
      ( D_13 = B_9
      | D_13 = A_8
      | ~ r2_hidden(D_13,k2_tarski(A_8,B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_150,plain,(
    ! [A_88,B_89,A_90,B_91] :
      ( '#skF_4'(A_88,B_89,k2_tarski(A_90,B_91)) = B_91
      | '#skF_4'(A_88,B_89,k2_tarski(A_90,B_91)) = A_90
      | '#skF_3'(A_88,B_89,k2_tarski(A_90,B_91)) = B_89
      | '#skF_3'(A_88,B_89,k2_tarski(A_90,B_91)) = A_88
      | k2_tarski(A_90,B_91) = k2_tarski(A_88,B_89) ) ),
    inference(resolution,[status(thm)],[c_106,c_26])).

tff(c_440,plain,(
    ! [A_106,B_107,B_108] :
      ( '#skF_4'(A_106,B_107,k2_tarski(B_107,B_108)) = B_108
      | '#skF_3'(A_106,B_107,k2_tarski(B_107,B_108)) = B_107
      | '#skF_3'(A_106,B_107,k2_tarski(B_107,B_108)) = A_106
      | k2_tarski(B_107,B_108) = k2_tarski(A_106,B_107) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_34])).

tff(c_508,plain,(
    ! [B_109,B_110] :
      ( '#skF_3'(B_109,B_110,k2_tarski(B_110,B_109)) = B_110
      | '#skF_3'(B_109,B_110,k2_tarski(B_110,B_109)) = B_109
      | k2_tarski(B_110,B_109) = k2_tarski(B_109,B_110) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_440,c_38])).

tff(c_89,plain,(
    ! [A_40,B_41,A_8,B_9] :
      ( '#skF_4'(A_40,B_41,k2_tarski(A_8,B_9)) = B_9
      | '#skF_4'(A_40,B_41,k2_tarski(A_8,B_9)) = A_8
      | ~ r2_hidden('#skF_3'(A_40,B_41,k2_tarski(A_8,B_9)),k2_tarski(A_8,B_9))
      | k2_tarski(A_8,B_9) = k2_tarski(A_40,B_41) ) ),
    inference(resolution,[status(thm)],[c_79,c_26])).

tff(c_525,plain,(
    ! [B_109,B_110] :
      ( '#skF_4'(B_109,B_110,k2_tarski(B_110,B_109)) = B_109
      | '#skF_4'(B_109,B_110,k2_tarski(B_110,B_109)) = B_110
      | ~ r2_hidden(B_110,k2_tarski(B_110,B_109))
      | k2_tarski(B_110,B_109) = k2_tarski(B_109,B_110)
      | '#skF_3'(B_109,B_110,k2_tarski(B_110,B_109)) = B_109
      | k2_tarski(B_110,B_109) = k2_tarski(B_109,B_110) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_508,c_89])).

tff(c_1538,plain,(
    ! [B_165,B_166] :
      ( '#skF_4'(B_165,B_166,k2_tarski(B_166,B_165)) = B_165
      | '#skF_4'(B_165,B_166,k2_tarski(B_166,B_165)) = B_166
      | '#skF_3'(B_165,B_166,k2_tarski(B_166,B_165)) = B_165
      | k2_tarski(B_166,B_165) = k2_tarski(B_165,B_166) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_525])).

tff(c_528,plain,(
    ! [B_110,B_109] :
      ( ~ r2_hidden(B_110,k2_tarski(B_110,B_109))
      | '#skF_4'(B_109,B_110,k2_tarski(B_110,B_109)) != B_109
      | k2_tarski(B_110,B_109) = k2_tarski(B_109,B_110)
      | '#skF_3'(B_109,B_110,k2_tarski(B_110,B_109)) = B_109
      | k2_tarski(B_110,B_109) = k2_tarski(B_109,B_110) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_508,c_36])).

tff(c_587,plain,(
    ! [B_109,B_110] :
      ( '#skF_4'(B_109,B_110,k2_tarski(B_110,B_109)) != B_109
      | '#skF_3'(B_109,B_110,k2_tarski(B_110,B_109)) = B_109
      | k2_tarski(B_110,B_109) = k2_tarski(B_109,B_110) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_528])).

tff(c_1722,plain,(
    ! [B_167,B_168] :
      ( '#skF_4'(B_167,B_168,k2_tarski(B_168,B_167)) = B_168
      | '#skF_3'(B_167,B_168,k2_tarski(B_168,B_167)) = B_167
      | k2_tarski(B_168,B_167) = k2_tarski(B_167,B_168) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1538,c_587])).

tff(c_531,plain,(
    ! [B_110,B_109] :
      ( ~ r2_hidden(B_110,k2_tarski(B_110,B_109))
      | '#skF_4'(B_109,B_110,k2_tarski(B_110,B_109)) != B_110
      | k2_tarski(B_110,B_109) = k2_tarski(B_109,B_110)
      | '#skF_3'(B_109,B_110,k2_tarski(B_110,B_109)) = B_109
      | k2_tarski(B_110,B_109) = k2_tarski(B_109,B_110) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_508,c_32])).

tff(c_589,plain,(
    ! [B_109,B_110] :
      ( '#skF_4'(B_109,B_110,k2_tarski(B_110,B_109)) != B_110
      | '#skF_3'(B_109,B_110,k2_tarski(B_110,B_109)) = B_109
      | k2_tarski(B_110,B_109) = k2_tarski(B_109,B_110) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_531])).

tff(c_1814,plain,(
    ! [B_169,B_170] :
      ( '#skF_3'(B_169,B_170,k2_tarski(B_170,B_169)) = B_169
      | k2_tarski(B_170,B_169) = k2_tarski(B_169,B_170) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1722,c_589])).

tff(c_1828,plain,(
    ! [B_169,B_170] :
      ( '#skF_4'(B_169,B_170,k2_tarski(B_170,B_169)) = B_169
      | '#skF_4'(B_169,B_170,k2_tarski(B_170,B_169)) = B_170
      | ~ r2_hidden(B_169,k2_tarski(B_170,B_169))
      | k2_tarski(B_170,B_169) = k2_tarski(B_169,B_170)
      | k2_tarski(B_170,B_169) = k2_tarski(B_169,B_170) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1814,c_89])).

tff(c_1945,plain,(
    ! [B_181,B_182] :
      ( '#skF_4'(B_181,B_182,k2_tarski(B_182,B_181)) = B_181
      | '#skF_4'(B_181,B_182,k2_tarski(B_182,B_181)) = B_182
      | k2_tarski(B_182,B_181) = k2_tarski(B_181,B_182) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1828])).

tff(c_1831,plain,(
    ! [B_169,B_170] :
      ( ~ r2_hidden(B_169,k2_tarski(B_170,B_169))
      | '#skF_4'(B_169,B_170,k2_tarski(B_170,B_169)) != B_169
      | k2_tarski(B_170,B_169) = k2_tarski(B_169,B_170)
      | k2_tarski(B_170,B_169) = k2_tarski(B_169,B_170) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1814,c_36])).

tff(c_1852,plain,(
    ! [B_169,B_170] :
      ( '#skF_4'(B_169,B_170,k2_tarski(B_170,B_169)) != B_169
      | k2_tarski(B_170,B_169) = k2_tarski(B_169,B_170) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1831])).

tff(c_2112,plain,(
    ! [B_183,B_184] :
      ( '#skF_4'(B_183,B_184,k2_tarski(B_184,B_183)) = B_184
      | k2_tarski(B_184,B_183) = k2_tarski(B_183,B_184) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1945,c_1852])).

tff(c_1834,plain,(
    ! [B_169,B_170] :
      ( ~ r2_hidden(B_169,k2_tarski(B_170,B_169))
      | '#skF_4'(B_169,B_170,k2_tarski(B_170,B_169)) != B_170
      | k2_tarski(B_170,B_169) = k2_tarski(B_169,B_170)
      | k2_tarski(B_170,B_169) = k2_tarski(B_169,B_170) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1814,c_32])).

tff(c_1854,plain,(
    ! [B_169,B_170] :
      ( '#skF_4'(B_169,B_170,k2_tarski(B_170,B_169)) != B_170
      | k2_tarski(B_170,B_169) = k2_tarski(B_169,B_170) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1834])).

tff(c_2188,plain,(
    ! [B_184,B_183] : k2_tarski(B_184,B_183) = k2_tarski(B_183,B_184) ),
    inference(superposition,[status(thm),theory(equality)],[c_2112,c_1854])).

tff(c_44,plain,(
    k1_enumset1('#skF_5','#skF_5','#skF_6') != k2_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2196,plain,(
    k1_enumset1('#skF_5','#skF_5','#skF_6') != k2_tarski('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2188,c_44])).

tff(c_102085,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_101004,c_2196])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:47:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 22.10/14.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 22.10/14.38  
% 22.10/14.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 22.10/14.38  %$ r2_hidden > k1_enumset1 > k2_tarski > #nlpp > #skF_4 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_1
% 22.10/14.38  
% 22.10/14.38  %Foreground sorts:
% 22.10/14.38  
% 22.10/14.38  
% 22.10/14.38  %Background operators:
% 22.10/14.38  
% 22.10/14.38  
% 22.10/14.38  %Foreground operators:
% 22.10/14.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 22.10/14.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 22.10/14.38  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 22.10/14.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 22.10/14.38  tff('#skF_5', type, '#skF_5': $i).
% 22.10/14.38  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 22.10/14.38  tff('#skF_6', type, '#skF_6': $i).
% 22.10/14.38  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 22.10/14.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 22.10/14.38  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 22.10/14.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 22.10/14.38  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 22.10/14.38  
% 22.26/14.40  tff(f_40, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 22.26/14.40  tff(f_49, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 22.26/14.40  tff(f_52, negated_conjecture, ~(![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 22.26/14.40  tff(c_8, plain, (![E_7, B_2, C_3]: (r2_hidden(E_7, k1_enumset1(E_7, B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 22.26/14.40  tff(c_4, plain, (![E_7, A_1, B_2]: (r2_hidden(E_7, k1_enumset1(A_1, B_2, E_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 22.26/14.40  tff(c_106, plain, (![A_65, B_66, C_67]: ('#skF_3'(A_65, B_66, C_67)=B_66 | '#skF_3'(A_65, B_66, C_67)=A_65 | r2_hidden('#skF_4'(A_65, B_66, C_67), C_67) | k2_tarski(A_65, B_66)=C_67)), inference(cnfTransformation, [status(thm)], [f_49])).
% 22.26/14.40  tff(c_2, plain, (![E_7, C_3, B_2, A_1]: (E_7=C_3 | E_7=B_2 | E_7=A_1 | ~r2_hidden(E_7, k1_enumset1(A_1, B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 22.26/14.40  tff(c_1420, plain, (![C_163, A_161, A_164, B_160, B_162]: ('#skF_4'(A_161, B_160, k1_enumset1(A_164, B_162, C_163))=C_163 | '#skF_4'(A_161, B_160, k1_enumset1(A_164, B_162, C_163))=B_162 | '#skF_4'(A_161, B_160, k1_enumset1(A_164, B_162, C_163))=A_164 | '#skF_3'(A_161, B_160, k1_enumset1(A_164, B_162, C_163))=B_160 | '#skF_3'(A_161, B_160, k1_enumset1(A_164, B_162, C_163))=A_161 | k2_tarski(A_161, B_160)=k1_enumset1(A_164, B_162, C_163))), inference(resolution, [status(thm)], [c_106, c_2])).
% 22.26/14.40  tff(c_34, plain, (![A_8, B_9, C_10]: ('#skF_3'(A_8, B_9, C_10)=B_9 | '#skF_3'(A_8, B_9, C_10)=A_8 | '#skF_4'(A_8, B_9, C_10)!=B_9 | k2_tarski(A_8, B_9)=C_10)), inference(cnfTransformation, [status(thm)], [f_49])).
% 22.26/14.40  tff(c_3767, plain, (![A_238, B_239, B_240, C_241]: ('#skF_4'(A_238, B_239, k1_enumset1(B_239, B_240, C_241))=C_241 | '#skF_4'(A_238, B_239, k1_enumset1(B_239, B_240, C_241))=B_240 | '#skF_3'(A_238, B_239, k1_enumset1(B_239, B_240, C_241))=B_239 | '#skF_3'(A_238, B_239, k1_enumset1(B_239, B_240, C_241))=A_238 | k2_tarski(A_238, B_239)=k1_enumset1(B_239, B_240, C_241))), inference(superposition, [status(thm), theory('equality')], [c_1420, c_34])).
% 22.26/14.40  tff(c_38, plain, (![A_8, B_9, C_10]: ('#skF_3'(A_8, B_9, C_10)=B_9 | '#skF_3'(A_8, B_9, C_10)=A_8 | '#skF_4'(A_8, B_9, C_10)!=A_8 | k2_tarski(A_8, B_9)=C_10)), inference(cnfTransformation, [status(thm)], [f_49])).
% 22.26/14.40  tff(c_7235, plain, (![C_353, B_354, B_355]: ('#skF_4'(C_353, B_354, k1_enumset1(B_354, B_355, C_353))=B_355 | '#skF_3'(C_353, B_354, k1_enumset1(B_354, B_355, C_353))=B_354 | '#skF_3'(C_353, B_354, k1_enumset1(B_354, B_355, C_353))=C_353 | k1_enumset1(B_354, B_355, C_353)=k2_tarski(C_353, B_354))), inference(superposition, [status(thm), theory('equality')], [c_3767, c_38])).
% 22.26/14.40  tff(c_7501, plain, (![C_356, B_357]: ('#skF_3'(C_356, B_357, k1_enumset1(B_357, B_357, C_356))=B_357 | '#skF_3'(C_356, B_357, k1_enumset1(B_357, B_357, C_356))=C_356 | k1_enumset1(B_357, B_357, C_356)=k2_tarski(C_356, B_357))), inference(superposition, [status(thm), theory('equality')], [c_7235, c_34])).
% 22.26/14.40  tff(c_79, plain, (![A_40, B_41, C_42]: (~r2_hidden('#skF_3'(A_40, B_41, C_42), C_42) | r2_hidden('#skF_4'(A_40, B_41, C_42), C_42) | k2_tarski(A_40, B_41)=C_42)), inference(cnfTransformation, [status(thm)], [f_49])).
% 22.26/14.40  tff(c_88, plain, (![B_2, C_3, A_1, A_40, B_41]: ('#skF_4'(A_40, B_41, k1_enumset1(A_1, B_2, C_3))=C_3 | '#skF_4'(A_40, B_41, k1_enumset1(A_1, B_2, C_3))=B_2 | '#skF_4'(A_40, B_41, k1_enumset1(A_1, B_2, C_3))=A_1 | ~r2_hidden('#skF_3'(A_40, B_41, k1_enumset1(A_1, B_2, C_3)), k1_enumset1(A_1, B_2, C_3)) | k2_tarski(A_40, B_41)=k1_enumset1(A_1, B_2, C_3))), inference(resolution, [status(thm)], [c_79, c_2])).
% 22.26/14.40  tff(c_7557, plain, (![C_356, B_357]: ('#skF_4'(C_356, B_357, k1_enumset1(B_357, B_357, C_356))=C_356 | '#skF_4'(C_356, B_357, k1_enumset1(B_357, B_357, C_356))=B_357 | '#skF_4'(C_356, B_357, k1_enumset1(B_357, B_357, C_356))=B_357 | ~r2_hidden(C_356, k1_enumset1(B_357, B_357, C_356)) | k1_enumset1(B_357, B_357, C_356)=k2_tarski(C_356, B_357) | '#skF_3'(C_356, B_357, k1_enumset1(B_357, B_357, C_356))=B_357 | k1_enumset1(B_357, B_357, C_356)=k2_tarski(C_356, B_357))), inference(superposition, [status(thm), theory('equality')], [c_7501, c_88])).
% 22.26/14.40  tff(c_96988, plain, (![C_1259, B_1260]: ('#skF_4'(C_1259, B_1260, k1_enumset1(B_1260, B_1260, C_1259))=C_1259 | '#skF_4'(C_1259, B_1260, k1_enumset1(B_1260, B_1260, C_1259))=B_1260 | '#skF_3'(C_1259, B_1260, k1_enumset1(B_1260, B_1260, C_1259))=B_1260 | k1_enumset1(B_1260, B_1260, C_1259)=k2_tarski(C_1259, B_1260))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_7557])).
% 22.26/14.40  tff(c_36, plain, (![A_8, B_9, C_10]: (~r2_hidden('#skF_3'(A_8, B_9, C_10), C_10) | '#skF_4'(A_8, B_9, C_10)!=A_8 | k2_tarski(A_8, B_9)=C_10)), inference(cnfTransformation, [status(thm)], [f_49])).
% 22.26/14.40  tff(c_7560, plain, (![C_356, B_357]: (~r2_hidden(C_356, k1_enumset1(B_357, B_357, C_356)) | '#skF_4'(C_356, B_357, k1_enumset1(B_357, B_357, C_356))!=C_356 | k1_enumset1(B_357, B_357, C_356)=k2_tarski(C_356, B_357) | '#skF_3'(C_356, B_357, k1_enumset1(B_357, B_357, C_356))=B_357 | k1_enumset1(B_357, B_357, C_356)=k2_tarski(C_356, B_357))), inference(superposition, [status(thm), theory('equality')], [c_7501, c_36])).
% 22.26/14.40  tff(c_7625, plain, (![C_356, B_357]: ('#skF_4'(C_356, B_357, k1_enumset1(B_357, B_357, C_356))!=C_356 | '#skF_3'(C_356, B_357, k1_enumset1(B_357, B_357, C_356))=B_357 | k1_enumset1(B_357, B_357, C_356)=k2_tarski(C_356, B_357))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_7560])).
% 22.26/14.40  tff(c_97669, plain, (![C_1261, B_1262]: ('#skF_4'(C_1261, B_1262, k1_enumset1(B_1262, B_1262, C_1261))=B_1262 | '#skF_3'(C_1261, B_1262, k1_enumset1(B_1262, B_1262, C_1261))=B_1262 | k1_enumset1(B_1262, B_1262, C_1261)=k2_tarski(C_1261, B_1262))), inference(superposition, [status(thm), theory('equality')], [c_96988, c_7625])).
% 22.26/14.40  tff(c_32, plain, (![A_8, B_9, C_10]: (~r2_hidden('#skF_3'(A_8, B_9, C_10), C_10) | '#skF_4'(A_8, B_9, C_10)!=B_9 | k2_tarski(A_8, B_9)=C_10)), inference(cnfTransformation, [status(thm)], [f_49])).
% 22.26/14.40  tff(c_7563, plain, (![C_356, B_357]: (~r2_hidden(C_356, k1_enumset1(B_357, B_357, C_356)) | '#skF_4'(C_356, B_357, k1_enumset1(B_357, B_357, C_356))!=B_357 | k1_enumset1(B_357, B_357, C_356)=k2_tarski(C_356, B_357) | '#skF_3'(C_356, B_357, k1_enumset1(B_357, B_357, C_356))=B_357 | k1_enumset1(B_357, B_357, C_356)=k2_tarski(C_356, B_357))), inference(superposition, [status(thm), theory('equality')], [c_7501, c_32])).
% 22.26/14.40  tff(c_7627, plain, (![C_356, B_357]: ('#skF_4'(C_356, B_357, k1_enumset1(B_357, B_357, C_356))!=B_357 | '#skF_3'(C_356, B_357, k1_enumset1(B_357, B_357, C_356))=B_357 | k1_enumset1(B_357, B_357, C_356)=k2_tarski(C_356, B_357))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_7563])).
% 22.26/14.40  tff(c_98180, plain, (![C_1263, B_1264]: ('#skF_3'(C_1263, B_1264, k1_enumset1(B_1264, B_1264, C_1263))=B_1264 | k1_enumset1(B_1264, B_1264, C_1263)=k2_tarski(C_1263, B_1264))), inference(superposition, [status(thm), theory('equality')], [c_97669, c_7627])).
% 22.26/14.40  tff(c_98226, plain, (![C_1263, B_1264]: ('#skF_4'(C_1263, B_1264, k1_enumset1(B_1264, B_1264, C_1263))=C_1263 | '#skF_4'(C_1263, B_1264, k1_enumset1(B_1264, B_1264, C_1263))=B_1264 | '#skF_4'(C_1263, B_1264, k1_enumset1(B_1264, B_1264, C_1263))=B_1264 | ~r2_hidden(B_1264, k1_enumset1(B_1264, B_1264, C_1263)) | k1_enumset1(B_1264, B_1264, C_1263)=k2_tarski(C_1263, B_1264) | k1_enumset1(B_1264, B_1264, C_1263)=k2_tarski(C_1263, B_1264))), inference(superposition, [status(thm), theory('equality')], [c_98180, c_88])).
% 22.26/14.40  tff(c_99965, plain, (![C_1272, B_1273]: ('#skF_4'(C_1272, B_1273, k1_enumset1(B_1273, B_1273, C_1272))=C_1272 | '#skF_4'(C_1272, B_1273, k1_enumset1(B_1273, B_1273, C_1272))=B_1273 | k1_enumset1(B_1273, B_1273, C_1272)=k2_tarski(C_1272, B_1273))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_98226])).
% 22.26/14.40  tff(c_98229, plain, (![B_1264, C_1263]: (~r2_hidden(B_1264, k1_enumset1(B_1264, B_1264, C_1263)) | '#skF_4'(C_1263, B_1264, k1_enumset1(B_1264, B_1264, C_1263))!=C_1263 | k1_enumset1(B_1264, B_1264, C_1263)=k2_tarski(C_1263, B_1264) | k1_enumset1(B_1264, B_1264, C_1263)=k2_tarski(C_1263, B_1264))), inference(superposition, [status(thm), theory('equality')], [c_98180, c_36])).
% 22.26/14.40  tff(c_98283, plain, (![C_1263, B_1264]: ('#skF_4'(C_1263, B_1264, k1_enumset1(B_1264, B_1264, C_1263))!=C_1263 | k1_enumset1(B_1264, B_1264, C_1263)=k2_tarski(C_1263, B_1264))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_98229])).
% 22.26/14.40  tff(c_100628, plain, (![C_1274, B_1275]: ('#skF_4'(C_1274, B_1275, k1_enumset1(B_1275, B_1275, C_1274))=B_1275 | k1_enumset1(B_1275, B_1275, C_1274)=k2_tarski(C_1274, B_1275))), inference(superposition, [status(thm), theory('equality')], [c_99965, c_98283])).
% 22.26/14.40  tff(c_98232, plain, (![B_1264, C_1263]: (~r2_hidden(B_1264, k1_enumset1(B_1264, B_1264, C_1263)) | '#skF_4'(C_1263, B_1264, k1_enumset1(B_1264, B_1264, C_1263))!=B_1264 | k1_enumset1(B_1264, B_1264, C_1263)=k2_tarski(C_1263, B_1264) | k1_enumset1(B_1264, B_1264, C_1263)=k2_tarski(C_1263, B_1264))), inference(superposition, [status(thm), theory('equality')], [c_98180, c_32])).
% 22.26/14.40  tff(c_98285, plain, (![C_1263, B_1264]: ('#skF_4'(C_1263, B_1264, k1_enumset1(B_1264, B_1264, C_1263))!=B_1264 | k1_enumset1(B_1264, B_1264, C_1263)=k2_tarski(C_1263, B_1264))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_98232])).
% 22.26/14.40  tff(c_101004, plain, (![B_1275, C_1274]: (k1_enumset1(B_1275, B_1275, C_1274)=k2_tarski(C_1274, B_1275))), inference(superposition, [status(thm), theory('equality')], [c_100628, c_98285])).
% 22.26/14.40  tff(c_28, plain, (![D_13, A_8]: (r2_hidden(D_13, k2_tarski(A_8, D_13)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 22.26/14.40  tff(c_30, plain, (![D_13, B_9]: (r2_hidden(D_13, k2_tarski(D_13, B_9)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 22.26/14.40  tff(c_26, plain, (![D_13, B_9, A_8]: (D_13=B_9 | D_13=A_8 | ~r2_hidden(D_13, k2_tarski(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 22.26/14.40  tff(c_150, plain, (![A_88, B_89, A_90, B_91]: ('#skF_4'(A_88, B_89, k2_tarski(A_90, B_91))=B_91 | '#skF_4'(A_88, B_89, k2_tarski(A_90, B_91))=A_90 | '#skF_3'(A_88, B_89, k2_tarski(A_90, B_91))=B_89 | '#skF_3'(A_88, B_89, k2_tarski(A_90, B_91))=A_88 | k2_tarski(A_90, B_91)=k2_tarski(A_88, B_89))), inference(resolution, [status(thm)], [c_106, c_26])).
% 22.26/14.40  tff(c_440, plain, (![A_106, B_107, B_108]: ('#skF_4'(A_106, B_107, k2_tarski(B_107, B_108))=B_108 | '#skF_3'(A_106, B_107, k2_tarski(B_107, B_108))=B_107 | '#skF_3'(A_106, B_107, k2_tarski(B_107, B_108))=A_106 | k2_tarski(B_107, B_108)=k2_tarski(A_106, B_107))), inference(superposition, [status(thm), theory('equality')], [c_150, c_34])).
% 22.26/14.40  tff(c_508, plain, (![B_109, B_110]: ('#skF_3'(B_109, B_110, k2_tarski(B_110, B_109))=B_110 | '#skF_3'(B_109, B_110, k2_tarski(B_110, B_109))=B_109 | k2_tarski(B_110, B_109)=k2_tarski(B_109, B_110))), inference(superposition, [status(thm), theory('equality')], [c_440, c_38])).
% 22.26/14.40  tff(c_89, plain, (![A_40, B_41, A_8, B_9]: ('#skF_4'(A_40, B_41, k2_tarski(A_8, B_9))=B_9 | '#skF_4'(A_40, B_41, k2_tarski(A_8, B_9))=A_8 | ~r2_hidden('#skF_3'(A_40, B_41, k2_tarski(A_8, B_9)), k2_tarski(A_8, B_9)) | k2_tarski(A_8, B_9)=k2_tarski(A_40, B_41))), inference(resolution, [status(thm)], [c_79, c_26])).
% 22.26/14.40  tff(c_525, plain, (![B_109, B_110]: ('#skF_4'(B_109, B_110, k2_tarski(B_110, B_109))=B_109 | '#skF_4'(B_109, B_110, k2_tarski(B_110, B_109))=B_110 | ~r2_hidden(B_110, k2_tarski(B_110, B_109)) | k2_tarski(B_110, B_109)=k2_tarski(B_109, B_110) | '#skF_3'(B_109, B_110, k2_tarski(B_110, B_109))=B_109 | k2_tarski(B_110, B_109)=k2_tarski(B_109, B_110))), inference(superposition, [status(thm), theory('equality')], [c_508, c_89])).
% 22.26/14.40  tff(c_1538, plain, (![B_165, B_166]: ('#skF_4'(B_165, B_166, k2_tarski(B_166, B_165))=B_165 | '#skF_4'(B_165, B_166, k2_tarski(B_166, B_165))=B_166 | '#skF_3'(B_165, B_166, k2_tarski(B_166, B_165))=B_165 | k2_tarski(B_166, B_165)=k2_tarski(B_165, B_166))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_525])).
% 22.26/14.40  tff(c_528, plain, (![B_110, B_109]: (~r2_hidden(B_110, k2_tarski(B_110, B_109)) | '#skF_4'(B_109, B_110, k2_tarski(B_110, B_109))!=B_109 | k2_tarski(B_110, B_109)=k2_tarski(B_109, B_110) | '#skF_3'(B_109, B_110, k2_tarski(B_110, B_109))=B_109 | k2_tarski(B_110, B_109)=k2_tarski(B_109, B_110))), inference(superposition, [status(thm), theory('equality')], [c_508, c_36])).
% 22.26/14.40  tff(c_587, plain, (![B_109, B_110]: ('#skF_4'(B_109, B_110, k2_tarski(B_110, B_109))!=B_109 | '#skF_3'(B_109, B_110, k2_tarski(B_110, B_109))=B_109 | k2_tarski(B_110, B_109)=k2_tarski(B_109, B_110))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_528])).
% 22.26/14.40  tff(c_1722, plain, (![B_167, B_168]: ('#skF_4'(B_167, B_168, k2_tarski(B_168, B_167))=B_168 | '#skF_3'(B_167, B_168, k2_tarski(B_168, B_167))=B_167 | k2_tarski(B_168, B_167)=k2_tarski(B_167, B_168))), inference(superposition, [status(thm), theory('equality')], [c_1538, c_587])).
% 22.26/14.40  tff(c_531, plain, (![B_110, B_109]: (~r2_hidden(B_110, k2_tarski(B_110, B_109)) | '#skF_4'(B_109, B_110, k2_tarski(B_110, B_109))!=B_110 | k2_tarski(B_110, B_109)=k2_tarski(B_109, B_110) | '#skF_3'(B_109, B_110, k2_tarski(B_110, B_109))=B_109 | k2_tarski(B_110, B_109)=k2_tarski(B_109, B_110))), inference(superposition, [status(thm), theory('equality')], [c_508, c_32])).
% 22.26/14.40  tff(c_589, plain, (![B_109, B_110]: ('#skF_4'(B_109, B_110, k2_tarski(B_110, B_109))!=B_110 | '#skF_3'(B_109, B_110, k2_tarski(B_110, B_109))=B_109 | k2_tarski(B_110, B_109)=k2_tarski(B_109, B_110))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_531])).
% 22.26/14.40  tff(c_1814, plain, (![B_169, B_170]: ('#skF_3'(B_169, B_170, k2_tarski(B_170, B_169))=B_169 | k2_tarski(B_170, B_169)=k2_tarski(B_169, B_170))), inference(superposition, [status(thm), theory('equality')], [c_1722, c_589])).
% 22.26/14.40  tff(c_1828, plain, (![B_169, B_170]: ('#skF_4'(B_169, B_170, k2_tarski(B_170, B_169))=B_169 | '#skF_4'(B_169, B_170, k2_tarski(B_170, B_169))=B_170 | ~r2_hidden(B_169, k2_tarski(B_170, B_169)) | k2_tarski(B_170, B_169)=k2_tarski(B_169, B_170) | k2_tarski(B_170, B_169)=k2_tarski(B_169, B_170))), inference(superposition, [status(thm), theory('equality')], [c_1814, c_89])).
% 22.26/14.40  tff(c_1945, plain, (![B_181, B_182]: ('#skF_4'(B_181, B_182, k2_tarski(B_182, B_181))=B_181 | '#skF_4'(B_181, B_182, k2_tarski(B_182, B_181))=B_182 | k2_tarski(B_182, B_181)=k2_tarski(B_181, B_182))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1828])).
% 22.26/14.40  tff(c_1831, plain, (![B_169, B_170]: (~r2_hidden(B_169, k2_tarski(B_170, B_169)) | '#skF_4'(B_169, B_170, k2_tarski(B_170, B_169))!=B_169 | k2_tarski(B_170, B_169)=k2_tarski(B_169, B_170) | k2_tarski(B_170, B_169)=k2_tarski(B_169, B_170))), inference(superposition, [status(thm), theory('equality')], [c_1814, c_36])).
% 22.26/14.40  tff(c_1852, plain, (![B_169, B_170]: ('#skF_4'(B_169, B_170, k2_tarski(B_170, B_169))!=B_169 | k2_tarski(B_170, B_169)=k2_tarski(B_169, B_170))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1831])).
% 22.26/14.40  tff(c_2112, plain, (![B_183, B_184]: ('#skF_4'(B_183, B_184, k2_tarski(B_184, B_183))=B_184 | k2_tarski(B_184, B_183)=k2_tarski(B_183, B_184))), inference(superposition, [status(thm), theory('equality')], [c_1945, c_1852])).
% 22.26/14.40  tff(c_1834, plain, (![B_169, B_170]: (~r2_hidden(B_169, k2_tarski(B_170, B_169)) | '#skF_4'(B_169, B_170, k2_tarski(B_170, B_169))!=B_170 | k2_tarski(B_170, B_169)=k2_tarski(B_169, B_170) | k2_tarski(B_170, B_169)=k2_tarski(B_169, B_170))), inference(superposition, [status(thm), theory('equality')], [c_1814, c_32])).
% 22.26/14.40  tff(c_1854, plain, (![B_169, B_170]: ('#skF_4'(B_169, B_170, k2_tarski(B_170, B_169))!=B_170 | k2_tarski(B_170, B_169)=k2_tarski(B_169, B_170))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1834])).
% 22.26/14.40  tff(c_2188, plain, (![B_184, B_183]: (k2_tarski(B_184, B_183)=k2_tarski(B_183, B_184))), inference(superposition, [status(thm), theory('equality')], [c_2112, c_1854])).
% 22.26/14.40  tff(c_44, plain, (k1_enumset1('#skF_5', '#skF_5', '#skF_6')!=k2_tarski('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_52])).
% 22.26/14.40  tff(c_2196, plain, (k1_enumset1('#skF_5', '#skF_5', '#skF_6')!=k2_tarski('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2188, c_44])).
% 22.26/14.40  tff(c_102085, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_101004, c_2196])).
% 22.26/14.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 22.26/14.40  
% 22.26/14.40  Inference rules
% 22.26/14.40  ----------------------
% 22.26/14.40  #Ref     : 0
% 22.26/14.40  #Sup     : 14839
% 22.26/14.40  #Fact    : 348
% 22.26/14.40  #Define  : 0
% 22.26/14.40  #Split   : 0
% 22.26/14.40  #Chain   : 0
% 22.26/14.40  #Close   : 0
% 22.26/14.40  
% 22.26/14.40  Ordering : KBO
% 22.26/14.40  
% 22.26/14.40  Simplification rules
% 22.26/14.40  ----------------------
% 22.26/14.40  #Subsume      : 6910
% 22.26/14.40  #Demod        : 17155
% 22.26/14.40  #Tautology    : 7105
% 22.26/14.40  #SimpNegUnit  : 0
% 22.26/14.40  #BackRed      : 93
% 22.26/14.40  
% 22.26/14.40  #Partial instantiations: 0
% 22.26/14.40  #Strategies tried      : 1
% 22.26/14.40  
% 22.26/14.40  Timing (in seconds)
% 22.26/14.40  ----------------------
% 22.26/14.40  Preprocessing        : 0.30
% 22.26/14.40  Parsing              : 0.15
% 22.26/14.40  CNF conversion       : 0.03
% 22.26/14.40  Main loop            : 13.29
% 22.26/14.40  Inferencing          : 5.49
% 22.26/14.40  Reduction            : 2.84
% 22.26/14.40  Demodulation         : 2.13
% 22.26/14.40  BG Simplification    : 0.42
% 22.26/14.40  Subsumption          : 4.23
% 22.26/14.40  Abstraction          : 1.10
% 22.26/14.41  MUC search           : 0.00
% 22.26/14.41  Cooper               : 0.00
% 22.26/14.41  Total                : 13.63
% 22.26/14.41  Index Insertion      : 0.00
% 22.26/14.41  Index Deletion       : 0.00
% 22.26/14.41  Index Matching       : 0.00
% 22.26/14.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
