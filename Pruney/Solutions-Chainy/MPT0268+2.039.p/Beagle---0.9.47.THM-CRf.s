%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:39 EST 2020

% Result     : Theorem 4.34s
% Output     : CNFRefutation 4.42s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 162 expanded)
%              Number of leaves         :   39 (  69 expanded)
%              Depth                    :    9
%              Number of atoms          :  103 ( 172 expanded)
%              Number of equality atoms :   72 ( 126 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

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

tff(f_47,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_77,axiom,(
    ! [A] : k3_tarski(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_zfmisc_1)).

tff(f_51,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_70,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_39,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_49,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_87,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(A,k1_tarski(B)) = A
      <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => k4_xboole_0(k2_xboole_0(A,B),B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k3_xboole_0(B,k1_tarski(A)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_zfmisc_1)).

tff(c_18,plain,(
    ! [A_18] : k5_xboole_0(A_18,A_18) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_44,plain,(
    ! [A_55] : k3_tarski(k1_tarski(A_55)) = A_55 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_22,plain,(
    ! [A_21] : k2_tarski(A_21,A_21) = k1_tarski(A_21) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2027,plain,(
    ! [A_170,B_171] : k3_tarski(k2_tarski(A_170,B_171)) = k2_xboole_0(A_170,B_171) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2036,plain,(
    ! [A_21] : k3_tarski(k1_tarski(A_21)) = k2_xboole_0(A_21,A_21) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_2027])).

tff(c_2039,plain,(
    ! [A_21] : k2_xboole_0(A_21,A_21) = A_21 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_2036])).

tff(c_1928,plain,(
    ! [B_163,A_164] : k5_xboole_0(B_163,A_164) = k5_xboole_0(A_164,B_163) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_12] : k5_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1944,plain,(
    ! [A_164] : k5_xboole_0(k1_xboole_0,A_164) = A_164 ),
    inference(superposition,[status(thm),theory(equality)],[c_1928,c_12])).

tff(c_2727,plain,(
    ! [A_212,B_213] : k5_xboole_0(k5_xboole_0(A_212,B_213),k2_xboole_0(A_212,B_213)) = k3_xboole_0(A_212,B_213) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2812,plain,(
    ! [A_18] : k5_xboole_0(k1_xboole_0,k2_xboole_0(A_18,A_18)) = k3_xboole_0(A_18,A_18) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_2727])).

tff(c_2817,plain,(
    ! [A_214] : k3_xboole_0(A_214,A_214) = A_214 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2039,c_1944,c_2812])).

tff(c_6,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2827,plain,(
    ! [A_214] : k5_xboole_0(A_214,A_214) = k4_xboole_0(A_214,A_214) ),
    inference(superposition,[status(thm),theory(equality)],[c_2817,c_6])).

tff(c_2839,plain,(
    ! [A_214] : k4_xboole_0(A_214,A_214) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_2827])).

tff(c_40,plain,(
    ! [B_54] : k4_xboole_0(k1_tarski(B_54),k1_tarski(B_54)) != k1_tarski(B_54) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2845,plain,(
    ! [B_54] : k1_tarski(B_54) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2839,c_40])).

tff(c_101,plain,(
    ! [B_62,A_63] : k5_xboole_0(B_62,A_63) = k5_xboole_0(A_63,B_62) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_117,plain,(
    ! [A_63] : k5_xboole_0(k1_xboole_0,A_63) = A_63 ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_12])).

tff(c_218,plain,(
    ! [A_74,B_75] : k3_tarski(k2_tarski(A_74,B_75)) = k2_xboole_0(A_74,B_75) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_227,plain,(
    ! [A_21] : k3_tarski(k1_tarski(A_21)) = k2_xboole_0(A_21,A_21) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_218])).

tff(c_230,plain,(
    ! [A_21] : k2_xboole_0(A_21,A_21) = A_21 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_227])).

tff(c_535,plain,(
    ! [A_106,B_107] : k5_xboole_0(k5_xboole_0(A_106,B_107),k2_xboole_0(A_106,B_107)) = k3_xboole_0(A_106,B_107) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_580,plain,(
    ! [A_18] : k5_xboole_0(k1_xboole_0,k2_xboole_0(A_18,A_18)) = k3_xboole_0(A_18,A_18) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_535])).

tff(c_585,plain,(
    ! [A_108] : k3_xboole_0(A_108,A_108) = A_108 ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_230,c_580])).

tff(c_595,plain,(
    ! [A_108] : k5_xboole_0(A_108,A_108) = k4_xboole_0(A_108,A_108) ),
    inference(superposition,[status(thm),theory(equality)],[c_585,c_6])).

tff(c_607,plain,(
    ! [A_108] : k4_xboole_0(A_108,A_108) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_595])).

tff(c_704,plain,(
    ! [B_54] : k1_tarski(B_54) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_607,c_40])).

tff(c_50,plain,
    ( ~ r2_hidden('#skF_2','#skF_1')
    | r2_hidden('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_100,plain,(
    ~ r2_hidden('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_200,plain,(
    ! [A_68,B_69] :
      ( r1_xboole_0(k1_tarski(A_68),B_69)
      | r2_hidden(A_68,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_241,plain,(
    ! [B_77,A_78] :
      ( r1_xboole_0(B_77,k1_tarski(A_78))
      | r2_hidden(A_78,B_77) ) ),
    inference(resolution,[status(thm)],[c_200,c_4])).

tff(c_8,plain,(
    ! [A_7,B_8] : k4_xboole_0(k2_xboole_0(A_7,B_8),B_8) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14,plain,(
    ! [A_13,B_14] :
      ( k4_xboole_0(k2_xboole_0(A_13,B_14),B_14) = A_13
      | ~ r1_xboole_0(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_55,plain,(
    ! [A_13,B_14] :
      ( k4_xboole_0(A_13,B_14) = A_13
      | ~ r1_xboole_0(A_13,B_14) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_14])).

tff(c_289,plain,(
    ! [B_84,A_85] :
      ( k4_xboole_0(B_84,k1_tarski(A_85)) = B_84
      | r2_hidden(A_85,B_84) ) ),
    inference(resolution,[status(thm)],[c_241,c_55])).

tff(c_48,plain,
    ( k4_xboole_0('#skF_1',k1_tarski('#skF_2')) != '#skF_1'
    | r2_hidden('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_240,plain,(
    k4_xboole_0('#skF_1',k1_tarski('#skF_2')) != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_303,plain,(
    r2_hidden('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_289,c_240])).

tff(c_323,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_303])).

tff(c_324,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_325,plain,(
    k4_xboole_0('#skF_1',k1_tarski('#skF_2')) = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_52,plain,
    ( k4_xboole_0('#skF_1',k1_tarski('#skF_2')) != '#skF_1'
    | k4_xboole_0('#skF_3',k1_tarski('#skF_4')) = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_331,plain,(
    k4_xboole_0('#skF_3',k1_tarski('#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_325,c_52])).

tff(c_612,plain,(
    ! [A_109,B_110,C_111] : k5_xboole_0(k5_xboole_0(A_109,B_110),C_111) = k5_xboole_0(A_109,k5_xboole_0(B_110,C_111)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_689,plain,(
    ! [A_18,C_111] : k5_xboole_0(A_18,k5_xboole_0(A_18,C_111)) = k5_xboole_0(k1_xboole_0,C_111) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_612])).

tff(c_787,plain,(
    ! [A_117,C_118] : k5_xboole_0(A_117,k5_xboole_0(A_117,C_118)) = C_118 ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_689])).

tff(c_1822,plain,(
    ! [A_161,B_162] : k5_xboole_0(A_161,k4_xboole_0(A_161,B_162)) = k3_xboole_0(A_161,B_162) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_787])).

tff(c_1888,plain,(
    k3_xboole_0('#skF_3',k1_tarski('#skF_4')) = k5_xboole_0('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_331,c_1822])).

tff(c_1906,plain,(
    k3_xboole_0('#skF_3',k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1888])).

tff(c_46,plain,(
    ! [B_57,A_56] :
      ( k3_xboole_0(B_57,k1_tarski(A_56)) = k1_tarski(A_56)
      | ~ r2_hidden(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1912,plain,
    ( k1_tarski('#skF_4') = k1_xboole_0
    | ~ r2_hidden('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1906,c_46])).

tff(c_1922,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_324,c_1912])).

tff(c_1924,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_704,c_1922])).

tff(c_1925,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_1926,plain,(
    r2_hidden('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_54,plain,
    ( ~ r2_hidden('#skF_2','#skF_1')
    | k4_xboole_0('#skF_3',k1_tarski('#skF_4')) = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_2041,plain,(
    k4_xboole_0('#skF_3',k1_tarski('#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1926,c_54])).

tff(c_2294,plain,(
    ! [A_201,B_202,C_203] : k5_xboole_0(k5_xboole_0(A_201,B_202),C_203) = k5_xboole_0(A_201,k5_xboole_0(B_202,C_203)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2358,plain,(
    ! [A_18,C_203] : k5_xboole_0(A_18,k5_xboole_0(A_18,C_203)) = k5_xboole_0(k1_xboole_0,C_203) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_2294])).

tff(c_2372,plain,(
    ! [A_204,C_205] : k5_xboole_0(A_204,k5_xboole_0(A_204,C_205)) = C_205 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1944,c_2358])).

tff(c_3177,plain,(
    ! [A_249,B_250] : k5_xboole_0(A_249,k4_xboole_0(A_249,B_250)) = k3_xboole_0(A_249,B_250) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_2372])).

tff(c_3237,plain,(
    k3_xboole_0('#skF_3',k1_tarski('#skF_4')) = k5_xboole_0('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2041,c_3177])).

tff(c_3252,plain,(
    k3_xboole_0('#skF_3',k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_3237])).

tff(c_3257,plain,
    ( k1_tarski('#skF_4') = k1_xboole_0
    | ~ r2_hidden('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3252,c_46])).

tff(c_3267,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1925,c_3257])).

tff(c_3269,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2845,c_3267])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:29:50 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.34/1.79  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.42/1.80  
% 4.42/1.80  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.42/1.80  %$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.42/1.80  
% 4.42/1.80  %Foreground sorts:
% 4.42/1.80  
% 4.42/1.80  
% 4.42/1.80  %Background operators:
% 4.42/1.80  
% 4.42/1.80  
% 4.42/1.80  %Foreground operators:
% 4.42/1.80  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.42/1.80  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.42/1.80  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.42/1.80  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.42/1.80  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.42/1.80  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.42/1.80  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.42/1.80  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.42/1.80  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.42/1.80  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.42/1.80  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.42/1.80  tff('#skF_2', type, '#skF_2': $i).
% 4.42/1.80  tff('#skF_3', type, '#skF_3': $i).
% 4.42/1.80  tff('#skF_1', type, '#skF_1': $i).
% 4.42/1.80  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.42/1.80  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.42/1.80  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.42/1.80  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.42/1.80  tff('#skF_4', type, '#skF_4': $i).
% 4.42/1.80  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.42/1.80  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.42/1.80  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.42/1.80  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.42/1.80  
% 4.42/1.82  tff(f_47, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 4.42/1.82  tff(f_77, axiom, (![A]: (k3_tarski(k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 4.42/1.82  tff(f_51, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 4.42/1.82  tff(f_70, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 4.42/1.82  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 4.42/1.82  tff(f_39, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 4.42/1.82  tff(f_49, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 4.42/1.82  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.42/1.82  tff(f_75, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 4.42/1.82  tff(f_87, negated_conjecture, ~(![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 4.42/1.82  tff(f_68, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 4.42/1.82  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 4.42/1.82  tff(f_35, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 4.42/1.82  tff(f_43, axiom, (![A, B]: (r1_xboole_0(A, B) => (k4_xboole_0(k2_xboole_0(A, B), B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_xboole_1)).
% 4.42/1.82  tff(f_45, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 4.42/1.82  tff(f_81, axiom, (![A, B]: (r2_hidden(A, B) => (k3_xboole_0(B, k1_tarski(A)) = k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_zfmisc_1)).
% 4.42/1.82  tff(c_18, plain, (![A_18]: (k5_xboole_0(A_18, A_18)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.42/1.82  tff(c_44, plain, (![A_55]: (k3_tarski(k1_tarski(A_55))=A_55)), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.42/1.82  tff(c_22, plain, (![A_21]: (k2_tarski(A_21, A_21)=k1_tarski(A_21))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.42/1.82  tff(c_2027, plain, (![A_170, B_171]: (k3_tarski(k2_tarski(A_170, B_171))=k2_xboole_0(A_170, B_171))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.42/1.82  tff(c_2036, plain, (![A_21]: (k3_tarski(k1_tarski(A_21))=k2_xboole_0(A_21, A_21))), inference(superposition, [status(thm), theory('equality')], [c_22, c_2027])).
% 4.42/1.82  tff(c_2039, plain, (![A_21]: (k2_xboole_0(A_21, A_21)=A_21)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_2036])).
% 4.42/1.82  tff(c_1928, plain, (![B_163, A_164]: (k5_xboole_0(B_163, A_164)=k5_xboole_0(A_164, B_163))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.42/1.82  tff(c_12, plain, (![A_12]: (k5_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.42/1.82  tff(c_1944, plain, (![A_164]: (k5_xboole_0(k1_xboole_0, A_164)=A_164)), inference(superposition, [status(thm), theory('equality')], [c_1928, c_12])).
% 4.42/1.82  tff(c_2727, plain, (![A_212, B_213]: (k5_xboole_0(k5_xboole_0(A_212, B_213), k2_xboole_0(A_212, B_213))=k3_xboole_0(A_212, B_213))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.42/1.82  tff(c_2812, plain, (![A_18]: (k5_xboole_0(k1_xboole_0, k2_xboole_0(A_18, A_18))=k3_xboole_0(A_18, A_18))), inference(superposition, [status(thm), theory('equality')], [c_18, c_2727])).
% 4.42/1.82  tff(c_2817, plain, (![A_214]: (k3_xboole_0(A_214, A_214)=A_214)), inference(demodulation, [status(thm), theory('equality')], [c_2039, c_1944, c_2812])).
% 4.42/1.82  tff(c_6, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.42/1.82  tff(c_2827, plain, (![A_214]: (k5_xboole_0(A_214, A_214)=k4_xboole_0(A_214, A_214))), inference(superposition, [status(thm), theory('equality')], [c_2817, c_6])).
% 4.42/1.82  tff(c_2839, plain, (![A_214]: (k4_xboole_0(A_214, A_214)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_2827])).
% 4.42/1.82  tff(c_40, plain, (![B_54]: (k4_xboole_0(k1_tarski(B_54), k1_tarski(B_54))!=k1_tarski(B_54))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.42/1.82  tff(c_2845, plain, (![B_54]: (k1_tarski(B_54)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2839, c_40])).
% 4.42/1.82  tff(c_101, plain, (![B_62, A_63]: (k5_xboole_0(B_62, A_63)=k5_xboole_0(A_63, B_62))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.42/1.82  tff(c_117, plain, (![A_63]: (k5_xboole_0(k1_xboole_0, A_63)=A_63)), inference(superposition, [status(thm), theory('equality')], [c_101, c_12])).
% 4.42/1.82  tff(c_218, plain, (![A_74, B_75]: (k3_tarski(k2_tarski(A_74, B_75))=k2_xboole_0(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.42/1.82  tff(c_227, plain, (![A_21]: (k3_tarski(k1_tarski(A_21))=k2_xboole_0(A_21, A_21))), inference(superposition, [status(thm), theory('equality')], [c_22, c_218])).
% 4.42/1.82  tff(c_230, plain, (![A_21]: (k2_xboole_0(A_21, A_21)=A_21)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_227])).
% 4.42/1.82  tff(c_535, plain, (![A_106, B_107]: (k5_xboole_0(k5_xboole_0(A_106, B_107), k2_xboole_0(A_106, B_107))=k3_xboole_0(A_106, B_107))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.42/1.82  tff(c_580, plain, (![A_18]: (k5_xboole_0(k1_xboole_0, k2_xboole_0(A_18, A_18))=k3_xboole_0(A_18, A_18))), inference(superposition, [status(thm), theory('equality')], [c_18, c_535])).
% 4.42/1.82  tff(c_585, plain, (![A_108]: (k3_xboole_0(A_108, A_108)=A_108)), inference(demodulation, [status(thm), theory('equality')], [c_117, c_230, c_580])).
% 4.42/1.82  tff(c_595, plain, (![A_108]: (k5_xboole_0(A_108, A_108)=k4_xboole_0(A_108, A_108))), inference(superposition, [status(thm), theory('equality')], [c_585, c_6])).
% 4.42/1.82  tff(c_607, plain, (![A_108]: (k4_xboole_0(A_108, A_108)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_595])).
% 4.42/1.82  tff(c_704, plain, (![B_54]: (k1_tarski(B_54)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_607, c_40])).
% 4.42/1.82  tff(c_50, plain, (~r2_hidden('#skF_2', '#skF_1') | r2_hidden('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.42/1.82  tff(c_100, plain, (~r2_hidden('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_50])).
% 4.42/1.82  tff(c_200, plain, (![A_68, B_69]: (r1_xboole_0(k1_tarski(A_68), B_69) | r2_hidden(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.42/1.82  tff(c_4, plain, (![B_4, A_3]: (r1_xboole_0(B_4, A_3) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.42/1.82  tff(c_241, plain, (![B_77, A_78]: (r1_xboole_0(B_77, k1_tarski(A_78)) | r2_hidden(A_78, B_77))), inference(resolution, [status(thm)], [c_200, c_4])).
% 4.42/1.82  tff(c_8, plain, (![A_7, B_8]: (k4_xboole_0(k2_xboole_0(A_7, B_8), B_8)=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.42/1.82  tff(c_14, plain, (![A_13, B_14]: (k4_xboole_0(k2_xboole_0(A_13, B_14), B_14)=A_13 | ~r1_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.42/1.82  tff(c_55, plain, (![A_13, B_14]: (k4_xboole_0(A_13, B_14)=A_13 | ~r1_xboole_0(A_13, B_14))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_14])).
% 4.42/1.82  tff(c_289, plain, (![B_84, A_85]: (k4_xboole_0(B_84, k1_tarski(A_85))=B_84 | r2_hidden(A_85, B_84))), inference(resolution, [status(thm)], [c_241, c_55])).
% 4.42/1.82  tff(c_48, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))!='#skF_1' | r2_hidden('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.42/1.82  tff(c_240, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))!='#skF_1'), inference(splitLeft, [status(thm)], [c_48])).
% 4.42/1.82  tff(c_303, plain, (r2_hidden('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_289, c_240])).
% 4.42/1.82  tff(c_323, plain, $false, inference(negUnitSimplification, [status(thm)], [c_100, c_303])).
% 4.42/1.82  tff(c_324, plain, (r2_hidden('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_48])).
% 4.42/1.82  tff(c_325, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))='#skF_1'), inference(splitRight, [status(thm)], [c_48])).
% 4.42/1.82  tff(c_52, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))!='#skF_1' | k4_xboole_0('#skF_3', k1_tarski('#skF_4'))='#skF_3'), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.42/1.82  tff(c_331, plain, (k4_xboole_0('#skF_3', k1_tarski('#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_325, c_52])).
% 4.42/1.82  tff(c_612, plain, (![A_109, B_110, C_111]: (k5_xboole_0(k5_xboole_0(A_109, B_110), C_111)=k5_xboole_0(A_109, k5_xboole_0(B_110, C_111)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.42/1.82  tff(c_689, plain, (![A_18, C_111]: (k5_xboole_0(A_18, k5_xboole_0(A_18, C_111))=k5_xboole_0(k1_xboole_0, C_111))), inference(superposition, [status(thm), theory('equality')], [c_18, c_612])).
% 4.42/1.82  tff(c_787, plain, (![A_117, C_118]: (k5_xboole_0(A_117, k5_xboole_0(A_117, C_118))=C_118)), inference(demodulation, [status(thm), theory('equality')], [c_117, c_689])).
% 4.42/1.82  tff(c_1822, plain, (![A_161, B_162]: (k5_xboole_0(A_161, k4_xboole_0(A_161, B_162))=k3_xboole_0(A_161, B_162))), inference(superposition, [status(thm), theory('equality')], [c_6, c_787])).
% 4.42/1.82  tff(c_1888, plain, (k3_xboole_0('#skF_3', k1_tarski('#skF_4'))=k5_xboole_0('#skF_3', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_331, c_1822])).
% 4.42/1.82  tff(c_1906, plain, (k3_xboole_0('#skF_3', k1_tarski('#skF_4'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1888])).
% 4.42/1.82  tff(c_46, plain, (![B_57, A_56]: (k3_xboole_0(B_57, k1_tarski(A_56))=k1_tarski(A_56) | ~r2_hidden(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.42/1.82  tff(c_1912, plain, (k1_tarski('#skF_4')=k1_xboole_0 | ~r2_hidden('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1906, c_46])).
% 4.42/1.82  tff(c_1922, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_324, c_1912])).
% 4.42/1.82  tff(c_1924, plain, $false, inference(negUnitSimplification, [status(thm)], [c_704, c_1922])).
% 4.42/1.82  tff(c_1925, plain, (r2_hidden('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_50])).
% 4.42/1.82  tff(c_1926, plain, (r2_hidden('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_50])).
% 4.42/1.82  tff(c_54, plain, (~r2_hidden('#skF_2', '#skF_1') | k4_xboole_0('#skF_3', k1_tarski('#skF_4'))='#skF_3'), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.42/1.82  tff(c_2041, plain, (k4_xboole_0('#skF_3', k1_tarski('#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1926, c_54])).
% 4.42/1.82  tff(c_2294, plain, (![A_201, B_202, C_203]: (k5_xboole_0(k5_xboole_0(A_201, B_202), C_203)=k5_xboole_0(A_201, k5_xboole_0(B_202, C_203)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.42/1.82  tff(c_2358, plain, (![A_18, C_203]: (k5_xboole_0(A_18, k5_xboole_0(A_18, C_203))=k5_xboole_0(k1_xboole_0, C_203))), inference(superposition, [status(thm), theory('equality')], [c_18, c_2294])).
% 4.42/1.82  tff(c_2372, plain, (![A_204, C_205]: (k5_xboole_0(A_204, k5_xboole_0(A_204, C_205))=C_205)), inference(demodulation, [status(thm), theory('equality')], [c_1944, c_2358])).
% 4.42/1.82  tff(c_3177, plain, (![A_249, B_250]: (k5_xboole_0(A_249, k4_xboole_0(A_249, B_250))=k3_xboole_0(A_249, B_250))), inference(superposition, [status(thm), theory('equality')], [c_6, c_2372])).
% 4.42/1.82  tff(c_3237, plain, (k3_xboole_0('#skF_3', k1_tarski('#skF_4'))=k5_xboole_0('#skF_3', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2041, c_3177])).
% 4.42/1.82  tff(c_3252, plain, (k3_xboole_0('#skF_3', k1_tarski('#skF_4'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_18, c_3237])).
% 4.42/1.82  tff(c_3257, plain, (k1_tarski('#skF_4')=k1_xboole_0 | ~r2_hidden('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3252, c_46])).
% 4.42/1.82  tff(c_3267, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1925, c_3257])).
% 4.42/1.82  tff(c_3269, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2845, c_3267])).
% 4.42/1.82  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.42/1.82  
% 4.42/1.82  Inference rules
% 4.42/1.82  ----------------------
% 4.42/1.82  #Ref     : 0
% 4.42/1.82  #Sup     : 783
% 4.42/1.82  #Fact    : 0
% 4.42/1.82  #Define  : 0
% 4.42/1.82  #Split   : 2
% 4.42/1.82  #Chain   : 0
% 4.42/1.82  #Close   : 0
% 4.42/1.82  
% 4.42/1.82  Ordering : KBO
% 4.42/1.82  
% 4.42/1.82  Simplification rules
% 4.42/1.82  ----------------------
% 4.42/1.82  #Subsume      : 25
% 4.42/1.82  #Demod        : 395
% 4.42/1.82  #Tautology    : 473
% 4.42/1.82  #SimpNegUnit  : 9
% 4.42/1.82  #BackRed      : 2
% 4.42/1.82  
% 4.42/1.82  #Partial instantiations: 0
% 4.42/1.82  #Strategies tried      : 1
% 4.42/1.82  
% 4.42/1.82  Timing (in seconds)
% 4.42/1.82  ----------------------
% 4.42/1.82  Preprocessing        : 0.34
% 4.42/1.82  Parsing              : 0.17
% 4.42/1.82  CNF conversion       : 0.02
% 4.42/1.82  Main loop            : 0.71
% 4.42/1.82  Inferencing          : 0.25
% 4.56/1.82  Reduction            : 0.29
% 4.56/1.82  Demodulation         : 0.23
% 4.56/1.82  BG Simplification    : 0.04
% 4.56/1.82  Subsumption          : 0.09
% 4.56/1.82  Abstraction          : 0.04
% 4.56/1.82  MUC search           : 0.00
% 4.56/1.82  Cooper               : 0.00
% 4.56/1.82  Total                : 1.09
% 4.56/1.82  Index Insertion      : 0.00
% 4.56/1.82  Index Deletion       : 0.00
% 4.56/1.82  Index Matching       : 0.00
% 4.56/1.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
