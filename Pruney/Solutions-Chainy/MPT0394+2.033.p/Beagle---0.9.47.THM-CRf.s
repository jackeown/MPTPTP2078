%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:25 EST 2020

% Result     : Theorem 5.14s
% Output     : CNFRefutation 5.14s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 463 expanded)
%              Number of leaves         :   27 ( 159 expanded)
%              Depth                    :   18
%              Number of atoms          :  131 (1096 expanded)
%              Number of equality atoms :   52 ( 189 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_52,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_66,axiom,(
    ! [A,B] :
      ( k3_xboole_0(A,k1_tarski(B)) = k1_tarski(B)
     => r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l29_zfmisc_1)).

tff(f_78,axiom,(
    ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_56,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_76,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & k1_setfam_1(k2_xboole_0(A,B)) != k3_xboole_0(k1_setfam_1(A),k1_setfam_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_setfam_1)).

tff(f_81,negated_conjecture,(
    ~ ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_115,plain,(
    ! [A_55,B_56] :
      ( r2_hidden('#skF_3'(A_55,B_56),k3_xboole_0(A_55,B_56))
      | r1_xboole_0(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_6,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,A_1)
      | ~ r2_hidden(D_6,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_127,plain,(
    ! [A_55,B_56] :
      ( r2_hidden('#skF_3'(A_55,B_56),A_55)
      | r1_xboole_0(A_55,B_56) ) ),
    inference(resolution,[status(thm)],[c_115,c_6])).

tff(c_16,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),B_2)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k3_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_453,plain,(
    ! [A_108,B_109,C_110] :
      ( ~ r2_hidden('#skF_1'(A_108,B_109,C_110),C_110)
      | r2_hidden('#skF_2'(A_108,B_109,C_110),C_110)
      | k3_xboole_0(A_108,B_109) = C_110 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_462,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_2'(A_1,B_2,B_2),B_2)
      | k3_xboole_0(A_1,B_2) = B_2 ) ),
    inference(resolution,[status(thm)],[c_16,c_453])).

tff(c_602,plain,(
    ! [A_146,B_147,C_148] :
      ( r2_hidden('#skF_1'(A_146,B_147,C_148),B_147)
      | ~ r2_hidden('#skF_2'(A_146,B_147,C_148),B_147)
      | ~ r2_hidden('#skF_2'(A_146,B_147,C_148),A_146)
      | k3_xboole_0(A_146,B_147) = C_148 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_3206,plain,(
    ! [C_217,B_218] :
      ( ~ r2_hidden('#skF_2'(C_217,B_218,C_217),B_218)
      | r2_hidden('#skF_1'(C_217,B_218,C_217),B_218)
      | k3_xboole_0(C_217,B_218) = C_217 ) ),
    inference(resolution,[status(thm)],[c_16,c_602])).

tff(c_8,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),B_2)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),A_1)
      | k3_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_3493,plain,(
    ! [B_222] :
      ( ~ r2_hidden('#skF_2'(B_222,B_222,B_222),B_222)
      | k3_xboole_0(B_222,B_222) = B_222 ) ),
    inference(resolution,[status(thm)],[c_3206,c_8])).

tff(c_3519,plain,(
    ! [B_223] : k3_xboole_0(B_223,B_223) = B_223 ),
    inference(resolution,[status(thm)],[c_462,c_3493])).

tff(c_157,plain,(
    ! [A_62,B_63] :
      ( r2_hidden('#skF_3'(A_62,B_63),A_62)
      | r1_xboole_0(A_62,B_63) ) ),
    inference(resolution,[status(thm)],[c_115,c_6])).

tff(c_26,plain,(
    ! [A_9,B_10,C_13] :
      ( ~ r1_xboole_0(A_9,B_10)
      | ~ r2_hidden(C_13,k3_xboole_0(A_9,B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_178,plain,(
    ! [A_67,B_68,B_69] :
      ( ~ r1_xboole_0(A_67,B_68)
      | r1_xboole_0(k3_xboole_0(A_67,B_68),B_69) ) ),
    inference(resolution,[status(thm)],[c_157,c_26])).

tff(c_20,plain,(
    ! [A_7,B_8] :
      ( k3_xboole_0(A_7,B_8) = k1_xboole_0
      | ~ r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_229,plain,(
    ! [A_75,B_76,B_77] :
      ( k3_xboole_0(k3_xboole_0(A_75,B_76),B_77) = k1_xboole_0
      | ~ r1_xboole_0(A_75,B_76) ) ),
    inference(resolution,[status(thm)],[c_178,c_20])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_257,plain,(
    ! [D_6,B_77,A_75,B_76] :
      ( r2_hidden(D_6,B_77)
      | ~ r2_hidden(D_6,k1_xboole_0)
      | ~ r1_xboole_0(A_75,B_76) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_229,c_4])).

tff(c_325,plain,(
    ! [A_75,B_76] : ~ r1_xboole_0(A_75,B_76) ),
    inference(splitLeft,[status(thm)],[c_257])).

tff(c_22,plain,(
    ! [A_7,B_8] :
      ( r1_xboole_0(A_7,B_8)
      | k3_xboole_0(A_7,B_8) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_331,plain,(
    ! [A_7,B_8] : k3_xboole_0(A_7,B_8) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_325,c_22])).

tff(c_3598,plain,(
    ! [B_223] : k1_xboole_0 != B_223 ),
    inference(superposition,[status(thm),theory(equality)],[c_3519,c_331])).

tff(c_3665,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_3598])).

tff(c_3667,plain,(
    ! [D_224,B_225] :
      ( r2_hidden(D_224,B_225)
      | ~ r2_hidden(D_224,k1_xboole_0) ) ),
    inference(splitRight,[status(thm)],[c_257])).

tff(c_3676,plain,(
    ! [B_226,B_227] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_226),B_227)
      | r1_xboole_0(k1_xboole_0,B_226) ) ),
    inference(resolution,[status(thm)],[c_127,c_3667])).

tff(c_3692,plain,(
    ! [A_9,B_10,B_226] :
      ( ~ r1_xboole_0(A_9,B_10)
      | r1_xboole_0(k1_xboole_0,B_226) ) ),
    inference(resolution,[status(thm)],[c_3676,c_26])).

tff(c_3695,plain,(
    ! [A_9,B_10] : ~ r1_xboole_0(A_9,B_10) ),
    inference(splitLeft,[status(thm)],[c_3692])).

tff(c_3738,plain,(
    ! [A_7,B_8] : k3_xboole_0(A_7,B_8) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_3695,c_22])).

tff(c_18,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),A_1)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k3_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_3850,plain,(
    ! [A_248,B_249,C_250] :
      ( ~ r2_hidden('#skF_1'(A_248,B_249,C_250),C_250)
      | r2_hidden('#skF_2'(A_248,B_249,C_250),C_250)
      | k3_xboole_0(A_248,B_249) = C_250 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_4157,plain,(
    ! [A_310,B_311] :
      ( r2_hidden('#skF_2'(A_310,B_311,A_310),A_310)
      | k3_xboole_0(A_310,B_311) = A_310 ) ),
    inference(resolution,[status(thm)],[c_18,c_3850])).

tff(c_3666,plain,(
    ! [D_6,B_77] :
      ( r2_hidden(D_6,B_77)
      | ~ r2_hidden(D_6,k1_xboole_0) ) ),
    inference(splitRight,[status(thm)],[c_257])).

tff(c_4165,plain,(
    ! [B_311,B_77] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_311,k1_xboole_0),B_77)
      | k3_xboole_0(k1_xboole_0,B_311) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4157,c_3666])).

tff(c_4178,plain,(
    ! [B_311,B_77] : r2_hidden('#skF_2'(k1_xboole_0,B_311,k1_xboole_0),B_77) ),
    inference(negUnitSimplification,[status(thm)],[c_3738,c_4165])).

tff(c_4181,plain,(
    ! [B_312,B_313] : r2_hidden('#skF_2'(k1_xboole_0,B_312,k1_xboole_0),B_313) ),
    inference(negUnitSimplification,[status(thm)],[c_3738,c_4165])).

tff(c_10,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),B_2)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),B_2)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),A_1)
      | k3_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_4184,plain,(
    ! [B_312] :
      ( r2_hidden('#skF_1'(k1_xboole_0,B_312,k1_xboole_0),B_312)
      | ~ r2_hidden('#skF_2'(k1_xboole_0,B_312,k1_xboole_0),B_312)
      | k3_xboole_0(k1_xboole_0,B_312) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4181,c_10])).

tff(c_4201,plain,(
    ! [B_312] :
      ( r2_hidden('#skF_1'(k1_xboole_0,B_312,k1_xboole_0),B_312)
      | k3_xboole_0(k1_xboole_0,B_312) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4178,c_4184])).

tff(c_4213,plain,(
    ! [B_314] : r2_hidden('#skF_1'(k1_xboole_0,B_314,k1_xboole_0),B_314) ),
    inference(negUnitSimplification,[status(thm)],[c_3738,c_4201])).

tff(c_4216,plain,
    ( ~ r2_hidden('#skF_2'(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4213,c_8])).

tff(c_4234,plain,(
    k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4178,c_4216])).

tff(c_4236,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3738,c_4234])).

tff(c_4237,plain,(
    ! [B_226] : r1_xboole_0(k1_xboole_0,B_226) ),
    inference(splitRight,[status(thm)],[c_3692])).

tff(c_4239,plain,(
    ! [B_315] : r1_xboole_0(k1_xboole_0,B_315) ),
    inference(splitRight,[status(thm)],[c_3692])).

tff(c_4283,plain,(
    ! [B_319] : k3_xboole_0(k1_xboole_0,B_319) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4239,c_20])).

tff(c_4313,plain,(
    ! [B_319,C_13] :
      ( ~ r1_xboole_0(k1_xboole_0,B_319)
      | ~ r2_hidden(C_13,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4283,c_26])).

tff(c_4337,plain,(
    ! [C_13] : ~ r2_hidden(C_13,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4237,c_4313])).

tff(c_38,plain,(
    ! [B_25,A_24] :
      ( r2_hidden(B_25,A_24)
      | k3_xboole_0(A_24,k1_tarski(B_25)) != k1_tarski(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_4310,plain,(
    ! [B_25] :
      ( r2_hidden(B_25,k1_xboole_0)
      | k1_tarski(B_25) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4283,c_38])).

tff(c_4472,plain,(
    ! [B_25] : k1_tarski(B_25) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_4337,c_4310])).

tff(c_42,plain,(
    ! [A_28] : k1_setfam_1(k1_tarski(A_28)) = A_28 ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_30,plain,(
    ! [A_16,B_17] : k2_xboole_0(k1_tarski(A_16),k1_tarski(B_17)) = k2_tarski(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_183,plain,(
    ! [A_70,B_71] :
      ( k3_xboole_0(k1_setfam_1(A_70),k1_setfam_1(B_71)) = k1_setfam_1(k2_xboole_0(A_70,B_71))
      | k1_xboole_0 = B_71
      | k1_xboole_0 = A_70 ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_213,plain,(
    ! [A_28,B_71] :
      ( k1_setfam_1(k2_xboole_0(k1_tarski(A_28),B_71)) = k3_xboole_0(A_28,k1_setfam_1(B_71))
      | k1_xboole_0 = B_71
      | k1_tarski(A_28) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_183])).

tff(c_5573,plain,(
    ! [A_389,B_390] :
      ( k1_setfam_1(k2_xboole_0(k1_tarski(A_389),B_390)) = k3_xboole_0(A_389,k1_setfam_1(B_390))
      | k1_xboole_0 = B_390 ) ),
    inference(negUnitSimplification,[status(thm)],[c_4472,c_213])).

tff(c_5591,plain,(
    ! [A_16,B_17] :
      ( k3_xboole_0(A_16,k1_setfam_1(k1_tarski(B_17))) = k1_setfam_1(k2_tarski(A_16,B_17))
      | k1_tarski(B_17) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_5573])).

tff(c_5595,plain,(
    ! [A_16,B_17] :
      ( k1_setfam_1(k2_tarski(A_16,B_17)) = k3_xboole_0(A_16,B_17)
      | k1_tarski(B_17) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_5591])).

tff(c_5596,plain,(
    ! [A_16,B_17] : k1_setfam_1(k2_tarski(A_16,B_17)) = k3_xboole_0(A_16,B_17) ),
    inference(negUnitSimplification,[status(thm)],[c_4472,c_5595])).

tff(c_44,plain,(
    k1_setfam_1(k2_tarski('#skF_4','#skF_5')) != k3_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_5600,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5596,c_44])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:07:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.14/2.01  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.14/2.02  
% 5.14/2.02  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.14/2.02  %$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4
% 5.14/2.02  
% 5.14/2.02  %Foreground sorts:
% 5.14/2.02  
% 5.14/2.02  
% 5.14/2.02  %Background operators:
% 5.14/2.02  
% 5.14/2.02  
% 5.14/2.02  %Foreground operators:
% 5.14/2.02  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.14/2.02  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.14/2.02  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.14/2.02  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.14/2.02  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.14/2.02  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.14/2.02  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.14/2.02  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.14/2.02  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.14/2.02  tff('#skF_5', type, '#skF_5': $i).
% 5.14/2.02  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.14/2.02  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.14/2.02  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.14/2.02  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.14/2.02  tff('#skF_4', type, '#skF_4': $i).
% 5.14/2.02  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.14/2.02  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.14/2.02  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.14/2.02  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 5.14/2.02  
% 5.14/2.03  tff(f_52, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 5.14/2.03  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 5.14/2.03  tff(f_38, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 5.14/2.03  tff(f_66, axiom, (![A, B]: ((k3_xboole_0(A, k1_tarski(B)) = k1_tarski(B)) => r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l29_zfmisc_1)).
% 5.14/2.03  tff(f_78, axiom, (![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_setfam_1)).
% 5.14/2.03  tff(f_56, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 5.14/2.03  tff(f_76, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(k1_setfam_1(k2_xboole_0(A, B)) = k3_xboole_0(k1_setfam_1(A), k1_setfam_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_setfam_1)).
% 5.14/2.03  tff(f_81, negated_conjecture, ~(![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 5.14/2.03  tff(c_115, plain, (![A_55, B_56]: (r2_hidden('#skF_3'(A_55, B_56), k3_xboole_0(A_55, B_56)) | r1_xboole_0(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.14/2.03  tff(c_6, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, A_1) | ~r2_hidden(D_6, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.14/2.03  tff(c_127, plain, (![A_55, B_56]: (r2_hidden('#skF_3'(A_55, B_56), A_55) | r1_xboole_0(A_55, B_56))), inference(resolution, [status(thm)], [c_115, c_6])).
% 5.14/2.03  tff(c_16, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), B_2) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k3_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.14/2.03  tff(c_453, plain, (![A_108, B_109, C_110]: (~r2_hidden('#skF_1'(A_108, B_109, C_110), C_110) | r2_hidden('#skF_2'(A_108, B_109, C_110), C_110) | k3_xboole_0(A_108, B_109)=C_110)), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.14/2.03  tff(c_462, plain, (![A_1, B_2]: (r2_hidden('#skF_2'(A_1, B_2, B_2), B_2) | k3_xboole_0(A_1, B_2)=B_2)), inference(resolution, [status(thm)], [c_16, c_453])).
% 5.14/2.03  tff(c_602, plain, (![A_146, B_147, C_148]: (r2_hidden('#skF_1'(A_146, B_147, C_148), B_147) | ~r2_hidden('#skF_2'(A_146, B_147, C_148), B_147) | ~r2_hidden('#skF_2'(A_146, B_147, C_148), A_146) | k3_xboole_0(A_146, B_147)=C_148)), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.14/2.03  tff(c_3206, plain, (![C_217, B_218]: (~r2_hidden('#skF_2'(C_217, B_218, C_217), B_218) | r2_hidden('#skF_1'(C_217, B_218, C_217), B_218) | k3_xboole_0(C_217, B_218)=C_217)), inference(resolution, [status(thm)], [c_16, c_602])).
% 5.14/2.03  tff(c_8, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), B_2) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), A_1) | k3_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.14/2.03  tff(c_3493, plain, (![B_222]: (~r2_hidden('#skF_2'(B_222, B_222, B_222), B_222) | k3_xboole_0(B_222, B_222)=B_222)), inference(resolution, [status(thm)], [c_3206, c_8])).
% 5.14/2.03  tff(c_3519, plain, (![B_223]: (k3_xboole_0(B_223, B_223)=B_223)), inference(resolution, [status(thm)], [c_462, c_3493])).
% 5.14/2.03  tff(c_157, plain, (![A_62, B_63]: (r2_hidden('#skF_3'(A_62, B_63), A_62) | r1_xboole_0(A_62, B_63))), inference(resolution, [status(thm)], [c_115, c_6])).
% 5.14/2.03  tff(c_26, plain, (![A_9, B_10, C_13]: (~r1_xboole_0(A_9, B_10) | ~r2_hidden(C_13, k3_xboole_0(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.14/2.03  tff(c_178, plain, (![A_67, B_68, B_69]: (~r1_xboole_0(A_67, B_68) | r1_xboole_0(k3_xboole_0(A_67, B_68), B_69))), inference(resolution, [status(thm)], [c_157, c_26])).
% 5.14/2.03  tff(c_20, plain, (![A_7, B_8]: (k3_xboole_0(A_7, B_8)=k1_xboole_0 | ~r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.14/2.03  tff(c_229, plain, (![A_75, B_76, B_77]: (k3_xboole_0(k3_xboole_0(A_75, B_76), B_77)=k1_xboole_0 | ~r1_xboole_0(A_75, B_76))), inference(resolution, [status(thm)], [c_178, c_20])).
% 5.14/2.03  tff(c_4, plain, (![D_6, B_2, A_1]: (r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.14/2.03  tff(c_257, plain, (![D_6, B_77, A_75, B_76]: (r2_hidden(D_6, B_77) | ~r2_hidden(D_6, k1_xboole_0) | ~r1_xboole_0(A_75, B_76))), inference(superposition, [status(thm), theory('equality')], [c_229, c_4])).
% 5.14/2.03  tff(c_325, plain, (![A_75, B_76]: (~r1_xboole_0(A_75, B_76))), inference(splitLeft, [status(thm)], [c_257])).
% 5.14/2.03  tff(c_22, plain, (![A_7, B_8]: (r1_xboole_0(A_7, B_8) | k3_xboole_0(A_7, B_8)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.14/2.03  tff(c_331, plain, (![A_7, B_8]: (k3_xboole_0(A_7, B_8)!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_325, c_22])).
% 5.14/2.03  tff(c_3598, plain, (![B_223]: (k1_xboole_0!=B_223)), inference(superposition, [status(thm), theory('equality')], [c_3519, c_331])).
% 5.14/2.03  tff(c_3665, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_3598])).
% 5.14/2.03  tff(c_3667, plain, (![D_224, B_225]: (r2_hidden(D_224, B_225) | ~r2_hidden(D_224, k1_xboole_0))), inference(splitRight, [status(thm)], [c_257])).
% 5.14/2.03  tff(c_3676, plain, (![B_226, B_227]: (r2_hidden('#skF_3'(k1_xboole_0, B_226), B_227) | r1_xboole_0(k1_xboole_0, B_226))), inference(resolution, [status(thm)], [c_127, c_3667])).
% 5.14/2.03  tff(c_3692, plain, (![A_9, B_10, B_226]: (~r1_xboole_0(A_9, B_10) | r1_xboole_0(k1_xboole_0, B_226))), inference(resolution, [status(thm)], [c_3676, c_26])).
% 5.14/2.03  tff(c_3695, plain, (![A_9, B_10]: (~r1_xboole_0(A_9, B_10))), inference(splitLeft, [status(thm)], [c_3692])).
% 5.14/2.03  tff(c_3738, plain, (![A_7, B_8]: (k3_xboole_0(A_7, B_8)!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_3695, c_22])).
% 5.14/2.03  tff(c_18, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), A_1) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k3_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.14/2.03  tff(c_3850, plain, (![A_248, B_249, C_250]: (~r2_hidden('#skF_1'(A_248, B_249, C_250), C_250) | r2_hidden('#skF_2'(A_248, B_249, C_250), C_250) | k3_xboole_0(A_248, B_249)=C_250)), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.14/2.03  tff(c_4157, plain, (![A_310, B_311]: (r2_hidden('#skF_2'(A_310, B_311, A_310), A_310) | k3_xboole_0(A_310, B_311)=A_310)), inference(resolution, [status(thm)], [c_18, c_3850])).
% 5.14/2.03  tff(c_3666, plain, (![D_6, B_77]: (r2_hidden(D_6, B_77) | ~r2_hidden(D_6, k1_xboole_0))), inference(splitRight, [status(thm)], [c_257])).
% 5.14/2.03  tff(c_4165, plain, (![B_311, B_77]: (r2_hidden('#skF_2'(k1_xboole_0, B_311, k1_xboole_0), B_77) | k3_xboole_0(k1_xboole_0, B_311)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4157, c_3666])).
% 5.14/2.03  tff(c_4178, plain, (![B_311, B_77]: (r2_hidden('#skF_2'(k1_xboole_0, B_311, k1_xboole_0), B_77))), inference(negUnitSimplification, [status(thm)], [c_3738, c_4165])).
% 5.14/2.03  tff(c_4181, plain, (![B_312, B_313]: (r2_hidden('#skF_2'(k1_xboole_0, B_312, k1_xboole_0), B_313))), inference(negUnitSimplification, [status(thm)], [c_3738, c_4165])).
% 5.14/2.03  tff(c_10, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), B_2) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), B_2) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), A_1) | k3_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.14/2.03  tff(c_4184, plain, (![B_312]: (r2_hidden('#skF_1'(k1_xboole_0, B_312, k1_xboole_0), B_312) | ~r2_hidden('#skF_2'(k1_xboole_0, B_312, k1_xboole_0), B_312) | k3_xboole_0(k1_xboole_0, B_312)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4181, c_10])).
% 5.14/2.03  tff(c_4201, plain, (![B_312]: (r2_hidden('#skF_1'(k1_xboole_0, B_312, k1_xboole_0), B_312) | k3_xboole_0(k1_xboole_0, B_312)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4178, c_4184])).
% 5.14/2.03  tff(c_4213, plain, (![B_314]: (r2_hidden('#skF_1'(k1_xboole_0, B_314, k1_xboole_0), B_314))), inference(negUnitSimplification, [status(thm)], [c_3738, c_4201])).
% 5.14/2.03  tff(c_4216, plain, (~r2_hidden('#skF_2'(k1_xboole_0, k1_xboole_0, k1_xboole_0), k1_xboole_0) | k3_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_4213, c_8])).
% 5.14/2.03  tff(c_4234, plain, (k3_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_4178, c_4216])).
% 5.14/2.03  tff(c_4236, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3738, c_4234])).
% 5.14/2.03  tff(c_4237, plain, (![B_226]: (r1_xboole_0(k1_xboole_0, B_226))), inference(splitRight, [status(thm)], [c_3692])).
% 5.14/2.03  tff(c_4239, plain, (![B_315]: (r1_xboole_0(k1_xboole_0, B_315))), inference(splitRight, [status(thm)], [c_3692])).
% 5.14/2.03  tff(c_4283, plain, (![B_319]: (k3_xboole_0(k1_xboole_0, B_319)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4239, c_20])).
% 5.14/2.03  tff(c_4313, plain, (![B_319, C_13]: (~r1_xboole_0(k1_xboole_0, B_319) | ~r2_hidden(C_13, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4283, c_26])).
% 5.14/2.03  tff(c_4337, plain, (![C_13]: (~r2_hidden(C_13, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_4237, c_4313])).
% 5.14/2.03  tff(c_38, plain, (![B_25, A_24]: (r2_hidden(B_25, A_24) | k3_xboole_0(A_24, k1_tarski(B_25))!=k1_tarski(B_25))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.14/2.03  tff(c_4310, plain, (![B_25]: (r2_hidden(B_25, k1_xboole_0) | k1_tarski(B_25)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4283, c_38])).
% 5.14/2.03  tff(c_4472, plain, (![B_25]: (k1_tarski(B_25)!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_4337, c_4310])).
% 5.14/2.03  tff(c_42, plain, (![A_28]: (k1_setfam_1(k1_tarski(A_28))=A_28)), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.14/2.03  tff(c_30, plain, (![A_16, B_17]: (k2_xboole_0(k1_tarski(A_16), k1_tarski(B_17))=k2_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.14/2.03  tff(c_183, plain, (![A_70, B_71]: (k3_xboole_0(k1_setfam_1(A_70), k1_setfam_1(B_71))=k1_setfam_1(k2_xboole_0(A_70, B_71)) | k1_xboole_0=B_71 | k1_xboole_0=A_70)), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.14/2.03  tff(c_213, plain, (![A_28, B_71]: (k1_setfam_1(k2_xboole_0(k1_tarski(A_28), B_71))=k3_xboole_0(A_28, k1_setfam_1(B_71)) | k1_xboole_0=B_71 | k1_tarski(A_28)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_42, c_183])).
% 5.14/2.03  tff(c_5573, plain, (![A_389, B_390]: (k1_setfam_1(k2_xboole_0(k1_tarski(A_389), B_390))=k3_xboole_0(A_389, k1_setfam_1(B_390)) | k1_xboole_0=B_390)), inference(negUnitSimplification, [status(thm)], [c_4472, c_213])).
% 5.14/2.03  tff(c_5591, plain, (![A_16, B_17]: (k3_xboole_0(A_16, k1_setfam_1(k1_tarski(B_17)))=k1_setfam_1(k2_tarski(A_16, B_17)) | k1_tarski(B_17)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_30, c_5573])).
% 5.14/2.03  tff(c_5595, plain, (![A_16, B_17]: (k1_setfam_1(k2_tarski(A_16, B_17))=k3_xboole_0(A_16, B_17) | k1_tarski(B_17)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_5591])).
% 5.14/2.03  tff(c_5596, plain, (![A_16, B_17]: (k1_setfam_1(k2_tarski(A_16, B_17))=k3_xboole_0(A_16, B_17))), inference(negUnitSimplification, [status(thm)], [c_4472, c_5595])).
% 5.14/2.03  tff(c_44, plain, (k1_setfam_1(k2_tarski('#skF_4', '#skF_5'))!=k3_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.14/2.03  tff(c_5600, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5596, c_44])).
% 5.14/2.03  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.14/2.03  
% 5.14/2.03  Inference rules
% 5.14/2.03  ----------------------
% 5.14/2.03  #Ref     : 5
% 5.14/2.03  #Sup     : 1264
% 5.14/2.03  #Fact    : 2
% 5.14/2.03  #Define  : 0
% 5.14/2.03  #Split   : 4
% 5.14/2.03  #Chain   : 0
% 5.14/2.03  #Close   : 0
% 5.14/2.03  
% 5.14/2.03  Ordering : KBO
% 5.14/2.03  
% 5.14/2.03  Simplification rules
% 5.14/2.03  ----------------------
% 5.14/2.03  #Subsume      : 466
% 5.14/2.03  #Demod        : 567
% 5.14/2.03  #Tautology    : 312
% 5.14/2.03  #SimpNegUnit  : 46
% 5.14/2.03  #BackRed      : 17
% 5.14/2.03  
% 5.14/2.03  #Partial instantiations: 0
% 5.14/2.03  #Strategies tried      : 1
% 5.14/2.03  
% 5.14/2.03  Timing (in seconds)
% 5.14/2.03  ----------------------
% 5.14/2.04  Preprocessing        : 0.31
% 5.14/2.04  Parsing              : 0.16
% 5.14/2.04  CNF conversion       : 0.02
% 5.14/2.04  Main loop            : 0.92
% 5.14/2.04  Inferencing          : 0.32
% 5.14/2.04  Reduction            : 0.32
% 5.14/2.04  Demodulation         : 0.23
% 5.14/2.04  BG Simplification    : 0.04
% 5.14/2.04  Subsumption          : 0.19
% 5.14/2.04  Abstraction          : 0.05
% 5.14/2.04  MUC search           : 0.00
% 5.14/2.04  Cooper               : 0.00
% 5.14/2.04  Total                : 1.27
% 5.14/2.04  Index Insertion      : 0.00
% 5.14/2.04  Index Deletion       : 0.00
% 5.14/2.04  Index Matching       : 0.00
% 5.14/2.04  BG Taut test         : 0.00
%------------------------------------------------------------------------------
