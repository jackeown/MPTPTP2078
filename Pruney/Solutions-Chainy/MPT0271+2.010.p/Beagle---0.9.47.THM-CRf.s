%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:02 EST 2020

% Result     : Theorem 10.90s
% Output     : CNFRefutation 10.90s
% Verified   : 
% Statistics : Number of formulae       :  147 ( 392 expanded)
%              Number of leaves         :   38 ( 147 expanded)
%              Depth                    :   15
%              Number of atoms          :  150 ( 407 expanded)
%              Number of equality atoms :  112 ( 355 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

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

tff(f_86,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
      <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_zfmisc_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_47,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_39,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_76,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => k4_xboole_0(k2_xboole_0(A,B),B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_xboole_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k3_xboole_0(B,k1_tarski(A)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l31_zfmisc_1)).

tff(c_50,plain,
    ( r2_hidden('#skF_1','#skF_2')
    | ~ r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_99,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_38,plain,(
    ! [A_51,B_52] :
      ( r1_xboole_0(k1_tarski(A_51),B_52)
      | r2_hidden(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_18,plain,(
    ! [A_18] : k5_xboole_0(A_18,A_18) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_100,plain,(
    ! [B_63,A_64] : k5_xboole_0(B_63,A_64) = k5_xboole_0(A_64,B_63) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_12] : k5_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_116,plain,(
    ! [A_64] : k5_xboole_0(k1_xboole_0,A_64) = A_64 ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_12])).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_647,plain,(
    ! [A_107,B_108] : k5_xboole_0(k5_xboole_0(A_107,B_108),k2_xboole_0(A_107,B_108)) = k3_xboole_0(A_107,B_108) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_701,plain,(
    ! [A_3] : k5_xboole_0(k5_xboole_0(A_3,A_3),A_3) = k3_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_647])).

tff(c_714,plain,(
    ! [A_109] : k3_xboole_0(A_109,A_109) = A_109 ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_18,c_701])).

tff(c_8,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_724,plain,(
    ! [A_109] : k5_xboole_0(A_109,A_109) = k4_xboole_0(A_109,A_109) ),
    inference(superposition,[status(thm),theory(equality)],[c_714,c_8])).

tff(c_736,plain,(
    ! [A_109] : k4_xboole_0(A_109,A_109) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_724])).

tff(c_44,plain,(
    ! [B_58] : k4_xboole_0(k1_tarski(B_58),k1_tarski(B_58)) != k1_tarski(B_58) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_834,plain,(
    ! [B_58] : k1_tarski(B_58) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_736,c_44])).

tff(c_54,plain,
    ( r2_hidden('#skF_1','#skF_2')
    | k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_195,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_22,plain,(
    ! [B_22,A_21] : k2_tarski(B_22,A_21) = k2_tarski(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_245,plain,(
    ! [A_72,B_73] : k3_tarski(k2_tarski(A_72,B_73)) = k2_xboole_0(A_72,B_73) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_278,plain,(
    ! [A_78,B_79] : k3_tarski(k2_tarski(A_78,B_79)) = k2_xboole_0(B_79,A_78) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_245])).

tff(c_42,plain,(
    ! [A_55,B_56] : k3_tarski(k2_tarski(A_55,B_56)) = k2_xboole_0(A_55,B_56) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_284,plain,(
    ! [B_79,A_78] : k2_xboole_0(B_79,A_78) = k2_xboole_0(A_78,B_79) ),
    inference(superposition,[status(thm),theory(equality)],[c_278,c_42])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_741,plain,(
    ! [A_110,B_111,C_112] : k5_xboole_0(k5_xboole_0(A_110,B_111),C_112) = k5_xboole_0(A_110,k5_xboole_0(B_111,C_112)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_818,plain,(
    ! [A_18,C_112] : k5_xboole_0(A_18,k5_xboole_0(A_18,C_112)) = k5_xboole_0(k1_xboole_0,C_112) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_741])).

tff(c_887,plain,(
    ! [A_120,C_121] : k5_xboole_0(A_120,k5_xboole_0(A_120,C_121)) = C_121 ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_818])).

tff(c_936,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k5_xboole_0(B_2,A_1)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_887])).

tff(c_471,plain,(
    ! [A_100,B_101,C_102] : k2_xboole_0(k2_xboole_0(A_100,B_101),C_102) = k2_xboole_0(A_100,k2_xboole_0(B_101,C_102)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_516,plain,(
    ! [A_3,C_102] : k2_xboole_0(A_3,k2_xboole_0(A_3,C_102)) = k2_xboole_0(A_3,C_102) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_471])).

tff(c_1684,plain,(
    ! [A_154,B_155] : k5_xboole_0(k5_xboole_0(A_154,B_155),k2_xboole_0(B_155,A_154)) = k3_xboole_0(B_155,A_154) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_647])).

tff(c_1768,plain,(
    ! [A_3,C_102] : k5_xboole_0(k5_xboole_0(k2_xboole_0(A_3,C_102),A_3),k2_xboole_0(A_3,C_102)) = k3_xboole_0(A_3,k2_xboole_0(A_3,C_102)) ),
    inference(superposition,[status(thm),theory(equality)],[c_516,c_1684])).

tff(c_1828,plain,(
    ! [A_156,C_157] : k3_xboole_0(A_156,k2_xboole_0(A_156,C_157)) = A_156 ),
    inference(demodulation,[status(thm),theory(equality)],[c_936,c_2,c_2,c_1768])).

tff(c_1857,plain,(
    ! [A_78,B_79] : k3_xboole_0(A_78,k2_xboole_0(B_79,A_78)) = A_78 ),
    inference(superposition,[status(thm),theory(equality)],[c_284,c_1828])).

tff(c_525,plain,(
    ! [A_103,C_104] : k2_xboole_0(A_103,k2_xboole_0(A_103,C_104)) = k2_xboole_0(A_103,C_104) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_471])).

tff(c_560,plain,(
    ! [A_78,B_79] : k2_xboole_0(A_78,k2_xboole_0(B_79,A_78)) = k2_xboole_0(A_78,B_79) ),
    inference(superposition,[status(thm),theory(equality)],[c_284,c_525])).

tff(c_20,plain,(
    ! [A_19,B_20] : k5_xboole_0(k5_xboole_0(A_19,B_20),k2_xboole_0(A_19,B_20)) = k3_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_4717,plain,(
    ! [A_201,B_202] : k5_xboole_0(A_201,k5_xboole_0(B_202,k2_xboole_0(A_201,B_202))) = k3_xboole_0(A_201,B_202) ),
    inference(superposition,[status(thm),theory(equality)],[c_741,c_20])).

tff(c_831,plain,(
    ! [A_18,C_112] : k5_xboole_0(A_18,k5_xboole_0(A_18,C_112)) = C_112 ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_818])).

tff(c_4757,plain,(
    ! [B_202,A_201] : k5_xboole_0(B_202,k2_xboole_0(A_201,B_202)) = k5_xboole_0(A_201,k3_xboole_0(A_201,B_202)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4717,c_831])).

tff(c_4864,plain,(
    ! [B_203,A_204] : k5_xboole_0(B_203,k2_xboole_0(A_204,B_203)) = k4_xboole_0(A_204,B_203) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_4757])).

tff(c_4923,plain,(
    ! [A_204,B_203] : k5_xboole_0(k4_xboole_0(A_204,B_203),k2_xboole_0(B_203,k2_xboole_0(A_204,B_203))) = k3_xboole_0(B_203,k2_xboole_0(A_204,B_203)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4864,c_20])).

tff(c_6261,plain,(
    ! [B_219,A_220] : k5_xboole_0(k2_xboole_0(B_219,A_220),k4_xboole_0(A_220,B_219)) = B_219 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1857,c_2,c_560,c_4923])).

tff(c_6357,plain,(
    k5_xboole_0(k2_xboole_0('#skF_4',k1_tarski('#skF_3')),k1_xboole_0) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_195,c_6261])).

tff(c_958,plain,(
    ! [A_122,B_123] : k5_xboole_0(A_122,k5_xboole_0(B_123,A_122)) = B_123 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_887])).

tff(c_994,plain,(
    ! [A_18,C_112] : k5_xboole_0(k5_xboole_0(A_18,C_112),C_112) = A_18 ),
    inference(superposition,[status(thm),theory(equality)],[c_831,c_958])).

tff(c_6412,plain,(
    k2_xboole_0('#skF_4',k1_tarski('#skF_3')) = k5_xboole_0('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6357,c_994])).

tff(c_6452,plain,(
    k2_xboole_0('#skF_4',k1_tarski('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_6412])).

tff(c_387,plain,(
    ! [A_89,B_90] :
      ( k4_xboole_0(k2_xboole_0(A_89,B_90),B_90) = A_89
      | ~ r1_xboole_0(A_89,B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_399,plain,(
    ! [A_78,B_79] :
      ( k4_xboole_0(k2_xboole_0(A_78,B_79),A_78) = B_79
      | ~ r1_xboole_0(B_79,A_78) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_284,c_387])).

tff(c_6504,plain,
    ( k4_xboole_0('#skF_4','#skF_4') = k1_tarski('#skF_3')
    | ~ r1_xboole_0(k1_tarski('#skF_3'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_6452,c_399])).

tff(c_6520,plain,
    ( k1_tarski('#skF_3') = k1_xboole_0
    | ~ r1_xboole_0(k1_tarski('#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_736,c_6504])).

tff(c_6521,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_3'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_834,c_6520])).

tff(c_6525,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_6521])).

tff(c_6529,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_6525])).

tff(c_6530,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_6991,plain,(
    ! [A_266,B_267,C_268] : k5_xboole_0(k5_xboole_0(A_266,B_267),C_268) = k5_xboole_0(A_266,k5_xboole_0(B_267,C_268)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_12989,plain,(
    ! [A_376,B_377] : k5_xboole_0(A_376,k5_xboole_0(B_377,k2_xboole_0(A_376,B_377))) = k3_xboole_0(A_376,B_377) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_6991])).

tff(c_7068,plain,(
    ! [A_18,C_268] : k5_xboole_0(A_18,k5_xboole_0(A_18,C_268)) = k5_xboole_0(k1_xboole_0,C_268) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_6991])).

tff(c_7081,plain,(
    ! [A_18,C_268] : k5_xboole_0(A_18,k5_xboole_0(A_18,C_268)) = C_268 ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_7068])).

tff(c_13039,plain,(
    ! [B_377,A_376] : k5_xboole_0(B_377,k2_xboole_0(A_376,B_377)) = k5_xboole_0(A_376,k3_xboole_0(A_376,B_377)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12989,c_7081])).

tff(c_13156,plain,(
    ! [B_378,A_379] : k5_xboole_0(B_378,k2_xboole_0(A_379,B_378)) = k4_xboole_0(A_379,B_378) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_13039])).

tff(c_13215,plain,(
    ! [B_378,A_379] : k5_xboole_0(B_378,k4_xboole_0(A_379,B_378)) = k2_xboole_0(A_379,B_378) ),
    inference(superposition,[status(thm),theory(equality)],[c_13156,c_7081])).

tff(c_6703,plain,(
    ! [B_244,A_245] :
      ( k3_xboole_0(B_244,k1_tarski(A_245)) = k1_tarski(A_245)
      | ~ r2_hidden(A_245,B_244) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_17271,plain,(
    ! [B_428,A_429] :
      ( k5_xboole_0(B_428,k1_tarski(A_429)) = k4_xboole_0(B_428,k1_tarski(A_429))
      | ~ r2_hidden(A_429,B_428) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6703,c_8])).

tff(c_7082,plain,(
    ! [A_269,C_270] : k5_xboole_0(A_269,k5_xboole_0(A_269,C_270)) = C_270 ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_7068])).

tff(c_7131,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k5_xboole_0(B_2,A_1)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_7082])).

tff(c_17378,plain,(
    ! [A_429,B_428] :
      ( k5_xboole_0(k1_tarski(A_429),k4_xboole_0(B_428,k1_tarski(A_429))) = B_428
      | ~ r2_hidden(A_429,B_428) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17271,c_7131])).

tff(c_17546,plain,(
    ! [B_430,A_431] :
      ( k2_xboole_0(B_430,k1_tarski(A_431)) = B_430
      | ~ r2_hidden(A_431,B_430) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13215,c_17378])).

tff(c_6582,plain,(
    ! [A_232,B_233] : k3_tarski(k2_tarski(A_232,B_233)) = k2_xboole_0(A_232,B_233) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_6641,plain,(
    ! [A_240,B_241] : k3_tarski(k2_tarski(A_240,B_241)) = k2_xboole_0(B_241,A_240) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_6582])).

tff(c_6647,plain,(
    ! [B_241,A_240] : k2_xboole_0(B_241,A_240) = k2_xboole_0(A_240,B_241) ),
    inference(superposition,[status(thm),theory(equality)],[c_6641,c_42])).

tff(c_13269,plain,(
    ! [A_240,B_241] : k5_xboole_0(A_240,k2_xboole_0(A_240,B_241)) = k4_xboole_0(B_241,A_240) ),
    inference(superposition,[status(thm),theory(equality)],[c_6647,c_13156])).

tff(c_17595,plain,(
    ! [B_430,A_431] :
      ( k5_xboole_0(B_430,B_430) = k4_xboole_0(k1_tarski(A_431),B_430)
      | ~ r2_hidden(A_431,B_430) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17546,c_13269])).

tff(c_18282,plain,(
    ! [A_439,B_440] :
      ( k4_xboole_0(k1_tarski(A_439),B_440) = k1_xboole_0
      | ~ r2_hidden(A_439,B_440) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_17595])).

tff(c_6531,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_52,plain,
    ( k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_xboole_0
    | k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_6668,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_6531,c_52])).

tff(c_18352,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_18282,c_6668])).

tff(c_18414,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6530,c_18352])).

tff(c_18415,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_16,plain,(
    ! [A_15,B_16,C_17] : k5_xboole_0(k5_xboole_0(A_15,B_16),C_17) = k5_xboole_0(A_15,k5_xboole_0(B_16,C_17)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_19244,plain,(
    ! [A_490,B_491] : k5_xboole_0(k5_xboole_0(A_490,B_491),k2_xboole_0(A_490,B_491)) = k3_xboole_0(A_490,B_491) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_21013,plain,(
    ! [A_556,B_557] : k5_xboole_0(A_556,k5_xboole_0(B_557,k2_xboole_0(A_556,B_557))) = k3_xboole_0(A_556,B_557) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_19244])).

tff(c_18452,plain,(
    ! [B_443,A_444] : k5_xboole_0(B_443,A_444) = k5_xboole_0(A_444,B_443) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_18468,plain,(
    ! [A_444] : k5_xboole_0(k1_xboole_0,A_444) = A_444 ),
    inference(superposition,[status(thm),theory(equality)],[c_18452,c_12])).

tff(c_18757,plain,(
    ! [A_476,B_477,C_478] : k5_xboole_0(k5_xboole_0(A_476,B_477),C_478) = k5_xboole_0(A_476,k5_xboole_0(B_477,C_478)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_18821,plain,(
    ! [A_18,C_478] : k5_xboole_0(A_18,k5_xboole_0(A_18,C_478)) = k5_xboole_0(k1_xboole_0,C_478) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_18757])).

tff(c_18834,plain,(
    ! [A_18,C_478] : k5_xboole_0(A_18,k5_xboole_0(A_18,C_478)) = C_478 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18468,c_18821])).

tff(c_21038,plain,(
    ! [B_557,A_556] : k5_xboole_0(B_557,k2_xboole_0(A_556,B_557)) = k5_xboole_0(A_556,k3_xboole_0(A_556,B_557)) ),
    inference(superposition,[status(thm),theory(equality)],[c_21013,c_18834])).

tff(c_21130,plain,(
    ! [B_558,A_559] : k5_xboole_0(B_558,k2_xboole_0(A_559,B_558)) = k4_xboole_0(A_559,B_558) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_21038])).

tff(c_21171,plain,(
    ! [B_558,A_559] : k5_xboole_0(B_558,k4_xboole_0(A_559,B_558)) = k2_xboole_0(A_559,B_558) ),
    inference(superposition,[status(thm),theory(equality)],[c_21130,c_18834])).

tff(c_18728,plain,(
    ! [B_472,A_473] :
      ( k3_xboole_0(B_472,k1_tarski(A_473)) = k1_tarski(A_473)
      | ~ r2_hidden(A_473,B_472) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_29564,plain,(
    ! [B_655,A_656] :
      ( k5_xboole_0(B_655,k1_tarski(A_656)) = k4_xboole_0(B_655,k1_tarski(A_656))
      | ~ r2_hidden(A_656,B_655) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18728,c_8])).

tff(c_18835,plain,(
    ! [A_479,C_480] : k5_xboole_0(A_479,k5_xboole_0(A_479,C_480)) = C_480 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18468,c_18821])).

tff(c_18878,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k5_xboole_0(B_2,A_1)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_18835])).

tff(c_29670,plain,(
    ! [A_656,B_655] :
      ( k5_xboole_0(k1_tarski(A_656),k4_xboole_0(B_655,k1_tarski(A_656))) = B_655
      | ~ r2_hidden(A_656,B_655) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_29564,c_18878])).

tff(c_29829,plain,(
    ! [B_657,A_658] :
      ( k2_xboole_0(B_657,k1_tarski(A_658)) = B_657
      | ~ r2_hidden(A_658,B_657) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21171,c_29670])).

tff(c_18551,plain,(
    ! [A_449,B_450] : k3_tarski(k2_tarski(A_449,B_450)) = k2_xboole_0(A_449,B_450) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_18593,plain,(
    ! [A_456,B_457] : k3_tarski(k2_tarski(A_456,B_457)) = k2_xboole_0(B_457,A_456) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_18551])).

tff(c_18599,plain,(
    ! [B_457,A_456] : k2_xboole_0(B_457,A_456) = k2_xboole_0(A_456,B_457) ),
    inference(superposition,[status(thm),theory(equality)],[c_18593,c_42])).

tff(c_21219,plain,(
    ! [A_456,B_457] : k5_xboole_0(A_456,k2_xboole_0(A_456,B_457)) = k4_xboole_0(B_457,A_456) ),
    inference(superposition,[status(thm),theory(equality)],[c_18599,c_21130])).

tff(c_29879,plain,(
    ! [B_657,A_658] :
      ( k5_xboole_0(B_657,B_657) = k4_xboole_0(k1_tarski(A_658),B_657)
      | ~ r2_hidden(A_658,B_657) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_29829,c_21219])).

tff(c_30778,plain,(
    ! [A_668,B_669] :
      ( k4_xboole_0(k1_tarski(A_668),B_669) = k1_xboole_0
      | ~ r2_hidden(A_668,B_669) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_29879])).

tff(c_18416,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_48,plain,
    ( k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_xboole_0
    | ~ r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_18418,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18416,c_48])).

tff(c_30849,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_30778,c_18418])).

tff(c_30914,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18415,c_30849])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:56:35 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.90/4.66  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.90/4.67  
% 10.90/4.67  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.90/4.67  %$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 10.90/4.67  
% 10.90/4.67  %Foreground sorts:
% 10.90/4.67  
% 10.90/4.67  
% 10.90/4.67  %Background operators:
% 10.90/4.67  
% 10.90/4.67  
% 10.90/4.67  %Foreground operators:
% 10.90/4.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.90/4.67  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.90/4.67  tff(k1_tarski, type, k1_tarski: $i > $i).
% 10.90/4.67  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.90/4.67  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.90/4.67  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 10.90/4.67  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 10.90/4.67  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 10.90/4.67  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.90/4.67  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 10.90/4.67  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 10.90/4.67  tff('#skF_2', type, '#skF_2': $i).
% 10.90/4.67  tff('#skF_3', type, '#skF_3': $i).
% 10.90/4.67  tff('#skF_1', type, '#skF_1': $i).
% 10.90/4.67  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 10.90/4.67  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 10.90/4.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.90/4.67  tff(k3_tarski, type, k3_tarski: $i > $i).
% 10.90/4.67  tff('#skF_4', type, '#skF_4': $i).
% 10.90/4.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.90/4.67  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.90/4.67  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 10.90/4.67  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 10.90/4.67  
% 10.90/4.70  tff(f_86, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_zfmisc_1)).
% 10.90/4.70  tff(f_70, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 10.90/4.70  tff(f_47, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 10.90/4.70  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 10.90/4.70  tff(f_39, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 10.90/4.70  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 10.90/4.70  tff(f_49, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 10.90/4.70  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 10.90/4.70  tff(f_81, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 10.90/4.70  tff(f_51, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 10.90/4.70  tff(f_76, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 10.90/4.70  tff(f_45, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 10.90/4.70  tff(f_37, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 10.90/4.70  tff(f_43, axiom, (![A, B]: (r1_xboole_0(A, B) => (k4_xboole_0(k2_xboole_0(A, B), B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_xboole_1)).
% 10.90/4.70  tff(f_74, axiom, (![A, B]: (r2_hidden(A, B) => (k3_xboole_0(B, k1_tarski(A)) = k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l31_zfmisc_1)).
% 10.90/4.70  tff(c_50, plain, (r2_hidden('#skF_1', '#skF_2') | ~r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_86])).
% 10.90/4.70  tff(c_99, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_50])).
% 10.90/4.70  tff(c_38, plain, (![A_51, B_52]: (r1_xboole_0(k1_tarski(A_51), B_52) | r2_hidden(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_70])).
% 10.90/4.70  tff(c_18, plain, (![A_18]: (k5_xboole_0(A_18, A_18)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.90/4.70  tff(c_100, plain, (![B_63, A_64]: (k5_xboole_0(B_63, A_64)=k5_xboole_0(A_64, B_63))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.90/4.70  tff(c_12, plain, (![A_12]: (k5_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.90/4.70  tff(c_116, plain, (![A_64]: (k5_xboole_0(k1_xboole_0, A_64)=A_64)), inference(superposition, [status(thm), theory('equality')], [c_100, c_12])).
% 10.90/4.70  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 10.90/4.70  tff(c_647, plain, (![A_107, B_108]: (k5_xboole_0(k5_xboole_0(A_107, B_108), k2_xboole_0(A_107, B_108))=k3_xboole_0(A_107, B_108))), inference(cnfTransformation, [status(thm)], [f_49])).
% 10.90/4.70  tff(c_701, plain, (![A_3]: (k5_xboole_0(k5_xboole_0(A_3, A_3), A_3)=k3_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_647])).
% 10.90/4.70  tff(c_714, plain, (![A_109]: (k3_xboole_0(A_109, A_109)=A_109)), inference(demodulation, [status(thm), theory('equality')], [c_116, c_18, c_701])).
% 10.90/4.70  tff(c_8, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.90/4.70  tff(c_724, plain, (![A_109]: (k5_xboole_0(A_109, A_109)=k4_xboole_0(A_109, A_109))), inference(superposition, [status(thm), theory('equality')], [c_714, c_8])).
% 10.90/4.70  tff(c_736, plain, (![A_109]: (k4_xboole_0(A_109, A_109)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_724])).
% 10.90/4.70  tff(c_44, plain, (![B_58]: (k4_xboole_0(k1_tarski(B_58), k1_tarski(B_58))!=k1_tarski(B_58))), inference(cnfTransformation, [status(thm)], [f_81])).
% 10.90/4.70  tff(c_834, plain, (![B_58]: (k1_tarski(B_58)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_736, c_44])).
% 10.90/4.70  tff(c_54, plain, (r2_hidden('#skF_1', '#skF_2') | k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_86])).
% 10.90/4.70  tff(c_195, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_54])).
% 10.90/4.70  tff(c_22, plain, (![B_22, A_21]: (k2_tarski(B_22, A_21)=k2_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_51])).
% 10.90/4.70  tff(c_245, plain, (![A_72, B_73]: (k3_tarski(k2_tarski(A_72, B_73))=k2_xboole_0(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_76])).
% 10.90/4.70  tff(c_278, plain, (![A_78, B_79]: (k3_tarski(k2_tarski(A_78, B_79))=k2_xboole_0(B_79, A_78))), inference(superposition, [status(thm), theory('equality')], [c_22, c_245])).
% 10.90/4.70  tff(c_42, plain, (![A_55, B_56]: (k3_tarski(k2_tarski(A_55, B_56))=k2_xboole_0(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_76])).
% 10.90/4.70  tff(c_284, plain, (![B_79, A_78]: (k2_xboole_0(B_79, A_78)=k2_xboole_0(A_78, B_79))), inference(superposition, [status(thm), theory('equality')], [c_278, c_42])).
% 10.90/4.70  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.90/4.70  tff(c_741, plain, (![A_110, B_111, C_112]: (k5_xboole_0(k5_xboole_0(A_110, B_111), C_112)=k5_xboole_0(A_110, k5_xboole_0(B_111, C_112)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 10.90/4.70  tff(c_818, plain, (![A_18, C_112]: (k5_xboole_0(A_18, k5_xboole_0(A_18, C_112))=k5_xboole_0(k1_xboole_0, C_112))), inference(superposition, [status(thm), theory('equality')], [c_18, c_741])).
% 10.90/4.70  tff(c_887, plain, (![A_120, C_121]: (k5_xboole_0(A_120, k5_xboole_0(A_120, C_121))=C_121)), inference(demodulation, [status(thm), theory('equality')], [c_116, c_818])).
% 10.90/4.70  tff(c_936, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k5_xboole_0(B_2, A_1))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_887])).
% 10.90/4.70  tff(c_471, plain, (![A_100, B_101, C_102]: (k2_xboole_0(k2_xboole_0(A_100, B_101), C_102)=k2_xboole_0(A_100, k2_xboole_0(B_101, C_102)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.90/4.70  tff(c_516, plain, (![A_3, C_102]: (k2_xboole_0(A_3, k2_xboole_0(A_3, C_102))=k2_xboole_0(A_3, C_102))), inference(superposition, [status(thm), theory('equality')], [c_4, c_471])).
% 10.90/4.70  tff(c_1684, plain, (![A_154, B_155]: (k5_xboole_0(k5_xboole_0(A_154, B_155), k2_xboole_0(B_155, A_154))=k3_xboole_0(B_155, A_154))), inference(superposition, [status(thm), theory('equality')], [c_2, c_647])).
% 10.90/4.70  tff(c_1768, plain, (![A_3, C_102]: (k5_xboole_0(k5_xboole_0(k2_xboole_0(A_3, C_102), A_3), k2_xboole_0(A_3, C_102))=k3_xboole_0(A_3, k2_xboole_0(A_3, C_102)))), inference(superposition, [status(thm), theory('equality')], [c_516, c_1684])).
% 10.90/4.70  tff(c_1828, plain, (![A_156, C_157]: (k3_xboole_0(A_156, k2_xboole_0(A_156, C_157))=A_156)), inference(demodulation, [status(thm), theory('equality')], [c_936, c_2, c_2, c_1768])).
% 10.90/4.70  tff(c_1857, plain, (![A_78, B_79]: (k3_xboole_0(A_78, k2_xboole_0(B_79, A_78))=A_78)), inference(superposition, [status(thm), theory('equality')], [c_284, c_1828])).
% 10.90/4.70  tff(c_525, plain, (![A_103, C_104]: (k2_xboole_0(A_103, k2_xboole_0(A_103, C_104))=k2_xboole_0(A_103, C_104))), inference(superposition, [status(thm), theory('equality')], [c_4, c_471])).
% 10.90/4.70  tff(c_560, plain, (![A_78, B_79]: (k2_xboole_0(A_78, k2_xboole_0(B_79, A_78))=k2_xboole_0(A_78, B_79))), inference(superposition, [status(thm), theory('equality')], [c_284, c_525])).
% 10.90/4.70  tff(c_20, plain, (![A_19, B_20]: (k5_xboole_0(k5_xboole_0(A_19, B_20), k2_xboole_0(A_19, B_20))=k3_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_49])).
% 10.90/4.70  tff(c_4717, plain, (![A_201, B_202]: (k5_xboole_0(A_201, k5_xboole_0(B_202, k2_xboole_0(A_201, B_202)))=k3_xboole_0(A_201, B_202))), inference(superposition, [status(thm), theory('equality')], [c_741, c_20])).
% 10.90/4.70  tff(c_831, plain, (![A_18, C_112]: (k5_xboole_0(A_18, k5_xboole_0(A_18, C_112))=C_112)), inference(demodulation, [status(thm), theory('equality')], [c_116, c_818])).
% 10.90/4.70  tff(c_4757, plain, (![B_202, A_201]: (k5_xboole_0(B_202, k2_xboole_0(A_201, B_202))=k5_xboole_0(A_201, k3_xboole_0(A_201, B_202)))), inference(superposition, [status(thm), theory('equality')], [c_4717, c_831])).
% 10.90/4.70  tff(c_4864, plain, (![B_203, A_204]: (k5_xboole_0(B_203, k2_xboole_0(A_204, B_203))=k4_xboole_0(A_204, B_203))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_4757])).
% 10.90/4.70  tff(c_4923, plain, (![A_204, B_203]: (k5_xboole_0(k4_xboole_0(A_204, B_203), k2_xboole_0(B_203, k2_xboole_0(A_204, B_203)))=k3_xboole_0(B_203, k2_xboole_0(A_204, B_203)))), inference(superposition, [status(thm), theory('equality')], [c_4864, c_20])).
% 10.90/4.70  tff(c_6261, plain, (![B_219, A_220]: (k5_xboole_0(k2_xboole_0(B_219, A_220), k4_xboole_0(A_220, B_219))=B_219)), inference(demodulation, [status(thm), theory('equality')], [c_1857, c_2, c_560, c_4923])).
% 10.90/4.70  tff(c_6357, plain, (k5_xboole_0(k2_xboole_0('#skF_4', k1_tarski('#skF_3')), k1_xboole_0)='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_195, c_6261])).
% 10.90/4.70  tff(c_958, plain, (![A_122, B_123]: (k5_xboole_0(A_122, k5_xboole_0(B_123, A_122))=B_123)), inference(superposition, [status(thm), theory('equality')], [c_2, c_887])).
% 10.90/4.70  tff(c_994, plain, (![A_18, C_112]: (k5_xboole_0(k5_xboole_0(A_18, C_112), C_112)=A_18)), inference(superposition, [status(thm), theory('equality')], [c_831, c_958])).
% 10.90/4.70  tff(c_6412, plain, (k2_xboole_0('#skF_4', k1_tarski('#skF_3'))=k5_xboole_0('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6357, c_994])).
% 10.90/4.70  tff(c_6452, plain, (k2_xboole_0('#skF_4', k1_tarski('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_6412])).
% 10.90/4.70  tff(c_387, plain, (![A_89, B_90]: (k4_xboole_0(k2_xboole_0(A_89, B_90), B_90)=A_89 | ~r1_xboole_0(A_89, B_90))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.90/4.70  tff(c_399, plain, (![A_78, B_79]: (k4_xboole_0(k2_xboole_0(A_78, B_79), A_78)=B_79 | ~r1_xboole_0(B_79, A_78))), inference(superposition, [status(thm), theory('equality')], [c_284, c_387])).
% 10.90/4.70  tff(c_6504, plain, (k4_xboole_0('#skF_4', '#skF_4')=k1_tarski('#skF_3') | ~r1_xboole_0(k1_tarski('#skF_3'), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_6452, c_399])).
% 10.90/4.70  tff(c_6520, plain, (k1_tarski('#skF_3')=k1_xboole_0 | ~r1_xboole_0(k1_tarski('#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_736, c_6504])).
% 10.90/4.70  tff(c_6521, plain, (~r1_xboole_0(k1_tarski('#skF_3'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_834, c_6520])).
% 10.90/4.70  tff(c_6525, plain, (r2_hidden('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_38, c_6521])).
% 10.90/4.70  tff(c_6529, plain, $false, inference(negUnitSimplification, [status(thm)], [c_99, c_6525])).
% 10.90/4.70  tff(c_6530, plain, (r2_hidden('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_54])).
% 10.90/4.70  tff(c_6991, plain, (![A_266, B_267, C_268]: (k5_xboole_0(k5_xboole_0(A_266, B_267), C_268)=k5_xboole_0(A_266, k5_xboole_0(B_267, C_268)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 10.90/4.70  tff(c_12989, plain, (![A_376, B_377]: (k5_xboole_0(A_376, k5_xboole_0(B_377, k2_xboole_0(A_376, B_377)))=k3_xboole_0(A_376, B_377))), inference(superposition, [status(thm), theory('equality')], [c_20, c_6991])).
% 10.90/4.70  tff(c_7068, plain, (![A_18, C_268]: (k5_xboole_0(A_18, k5_xboole_0(A_18, C_268))=k5_xboole_0(k1_xboole_0, C_268))), inference(superposition, [status(thm), theory('equality')], [c_18, c_6991])).
% 10.90/4.70  tff(c_7081, plain, (![A_18, C_268]: (k5_xboole_0(A_18, k5_xboole_0(A_18, C_268))=C_268)), inference(demodulation, [status(thm), theory('equality')], [c_116, c_7068])).
% 10.90/4.70  tff(c_13039, plain, (![B_377, A_376]: (k5_xboole_0(B_377, k2_xboole_0(A_376, B_377))=k5_xboole_0(A_376, k3_xboole_0(A_376, B_377)))), inference(superposition, [status(thm), theory('equality')], [c_12989, c_7081])).
% 10.90/4.70  tff(c_13156, plain, (![B_378, A_379]: (k5_xboole_0(B_378, k2_xboole_0(A_379, B_378))=k4_xboole_0(A_379, B_378))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_13039])).
% 10.90/4.70  tff(c_13215, plain, (![B_378, A_379]: (k5_xboole_0(B_378, k4_xboole_0(A_379, B_378))=k2_xboole_0(A_379, B_378))), inference(superposition, [status(thm), theory('equality')], [c_13156, c_7081])).
% 10.90/4.70  tff(c_6703, plain, (![B_244, A_245]: (k3_xboole_0(B_244, k1_tarski(A_245))=k1_tarski(A_245) | ~r2_hidden(A_245, B_244))), inference(cnfTransformation, [status(thm)], [f_74])).
% 10.90/4.70  tff(c_17271, plain, (![B_428, A_429]: (k5_xboole_0(B_428, k1_tarski(A_429))=k4_xboole_0(B_428, k1_tarski(A_429)) | ~r2_hidden(A_429, B_428))), inference(superposition, [status(thm), theory('equality')], [c_6703, c_8])).
% 10.90/4.70  tff(c_7082, plain, (![A_269, C_270]: (k5_xboole_0(A_269, k5_xboole_0(A_269, C_270))=C_270)), inference(demodulation, [status(thm), theory('equality')], [c_116, c_7068])).
% 10.90/4.70  tff(c_7131, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k5_xboole_0(B_2, A_1))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_7082])).
% 10.90/4.70  tff(c_17378, plain, (![A_429, B_428]: (k5_xboole_0(k1_tarski(A_429), k4_xboole_0(B_428, k1_tarski(A_429)))=B_428 | ~r2_hidden(A_429, B_428))), inference(superposition, [status(thm), theory('equality')], [c_17271, c_7131])).
% 10.90/4.70  tff(c_17546, plain, (![B_430, A_431]: (k2_xboole_0(B_430, k1_tarski(A_431))=B_430 | ~r2_hidden(A_431, B_430))), inference(demodulation, [status(thm), theory('equality')], [c_13215, c_17378])).
% 10.90/4.70  tff(c_6582, plain, (![A_232, B_233]: (k3_tarski(k2_tarski(A_232, B_233))=k2_xboole_0(A_232, B_233))), inference(cnfTransformation, [status(thm)], [f_76])).
% 10.90/4.70  tff(c_6641, plain, (![A_240, B_241]: (k3_tarski(k2_tarski(A_240, B_241))=k2_xboole_0(B_241, A_240))), inference(superposition, [status(thm), theory('equality')], [c_22, c_6582])).
% 10.90/4.70  tff(c_6647, plain, (![B_241, A_240]: (k2_xboole_0(B_241, A_240)=k2_xboole_0(A_240, B_241))), inference(superposition, [status(thm), theory('equality')], [c_6641, c_42])).
% 10.90/4.70  tff(c_13269, plain, (![A_240, B_241]: (k5_xboole_0(A_240, k2_xboole_0(A_240, B_241))=k4_xboole_0(B_241, A_240))), inference(superposition, [status(thm), theory('equality')], [c_6647, c_13156])).
% 10.90/4.70  tff(c_17595, plain, (![B_430, A_431]: (k5_xboole_0(B_430, B_430)=k4_xboole_0(k1_tarski(A_431), B_430) | ~r2_hidden(A_431, B_430))), inference(superposition, [status(thm), theory('equality')], [c_17546, c_13269])).
% 10.90/4.70  tff(c_18282, plain, (![A_439, B_440]: (k4_xboole_0(k1_tarski(A_439), B_440)=k1_xboole_0 | ~r2_hidden(A_439, B_440))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_17595])).
% 10.90/4.70  tff(c_6531, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_54])).
% 10.90/4.70  tff(c_52, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_xboole_0 | k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_86])).
% 10.90/4.70  tff(c_6668, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_6531, c_52])).
% 10.90/4.70  tff(c_18352, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_18282, c_6668])).
% 10.90/4.70  tff(c_18414, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6530, c_18352])).
% 10.90/4.70  tff(c_18415, plain, (r2_hidden('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_50])).
% 10.90/4.70  tff(c_16, plain, (![A_15, B_16, C_17]: (k5_xboole_0(k5_xboole_0(A_15, B_16), C_17)=k5_xboole_0(A_15, k5_xboole_0(B_16, C_17)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 10.90/4.70  tff(c_19244, plain, (![A_490, B_491]: (k5_xboole_0(k5_xboole_0(A_490, B_491), k2_xboole_0(A_490, B_491))=k3_xboole_0(A_490, B_491))), inference(cnfTransformation, [status(thm)], [f_49])).
% 10.90/4.70  tff(c_21013, plain, (![A_556, B_557]: (k5_xboole_0(A_556, k5_xboole_0(B_557, k2_xboole_0(A_556, B_557)))=k3_xboole_0(A_556, B_557))), inference(superposition, [status(thm), theory('equality')], [c_16, c_19244])).
% 10.90/4.70  tff(c_18452, plain, (![B_443, A_444]: (k5_xboole_0(B_443, A_444)=k5_xboole_0(A_444, B_443))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.90/4.70  tff(c_18468, plain, (![A_444]: (k5_xboole_0(k1_xboole_0, A_444)=A_444)), inference(superposition, [status(thm), theory('equality')], [c_18452, c_12])).
% 10.90/4.70  tff(c_18757, plain, (![A_476, B_477, C_478]: (k5_xboole_0(k5_xboole_0(A_476, B_477), C_478)=k5_xboole_0(A_476, k5_xboole_0(B_477, C_478)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 10.90/4.70  tff(c_18821, plain, (![A_18, C_478]: (k5_xboole_0(A_18, k5_xboole_0(A_18, C_478))=k5_xboole_0(k1_xboole_0, C_478))), inference(superposition, [status(thm), theory('equality')], [c_18, c_18757])).
% 10.90/4.70  tff(c_18834, plain, (![A_18, C_478]: (k5_xboole_0(A_18, k5_xboole_0(A_18, C_478))=C_478)), inference(demodulation, [status(thm), theory('equality')], [c_18468, c_18821])).
% 10.90/4.70  tff(c_21038, plain, (![B_557, A_556]: (k5_xboole_0(B_557, k2_xboole_0(A_556, B_557))=k5_xboole_0(A_556, k3_xboole_0(A_556, B_557)))), inference(superposition, [status(thm), theory('equality')], [c_21013, c_18834])).
% 10.90/4.70  tff(c_21130, plain, (![B_558, A_559]: (k5_xboole_0(B_558, k2_xboole_0(A_559, B_558))=k4_xboole_0(A_559, B_558))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_21038])).
% 10.90/4.70  tff(c_21171, plain, (![B_558, A_559]: (k5_xboole_0(B_558, k4_xboole_0(A_559, B_558))=k2_xboole_0(A_559, B_558))), inference(superposition, [status(thm), theory('equality')], [c_21130, c_18834])).
% 10.90/4.70  tff(c_18728, plain, (![B_472, A_473]: (k3_xboole_0(B_472, k1_tarski(A_473))=k1_tarski(A_473) | ~r2_hidden(A_473, B_472))), inference(cnfTransformation, [status(thm)], [f_74])).
% 10.90/4.70  tff(c_29564, plain, (![B_655, A_656]: (k5_xboole_0(B_655, k1_tarski(A_656))=k4_xboole_0(B_655, k1_tarski(A_656)) | ~r2_hidden(A_656, B_655))), inference(superposition, [status(thm), theory('equality')], [c_18728, c_8])).
% 10.90/4.70  tff(c_18835, plain, (![A_479, C_480]: (k5_xboole_0(A_479, k5_xboole_0(A_479, C_480))=C_480)), inference(demodulation, [status(thm), theory('equality')], [c_18468, c_18821])).
% 10.90/4.70  tff(c_18878, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k5_xboole_0(B_2, A_1))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_18835])).
% 10.90/4.70  tff(c_29670, plain, (![A_656, B_655]: (k5_xboole_0(k1_tarski(A_656), k4_xboole_0(B_655, k1_tarski(A_656)))=B_655 | ~r2_hidden(A_656, B_655))), inference(superposition, [status(thm), theory('equality')], [c_29564, c_18878])).
% 10.90/4.70  tff(c_29829, plain, (![B_657, A_658]: (k2_xboole_0(B_657, k1_tarski(A_658))=B_657 | ~r2_hidden(A_658, B_657))), inference(demodulation, [status(thm), theory('equality')], [c_21171, c_29670])).
% 10.90/4.70  tff(c_18551, plain, (![A_449, B_450]: (k3_tarski(k2_tarski(A_449, B_450))=k2_xboole_0(A_449, B_450))), inference(cnfTransformation, [status(thm)], [f_76])).
% 10.90/4.70  tff(c_18593, plain, (![A_456, B_457]: (k3_tarski(k2_tarski(A_456, B_457))=k2_xboole_0(B_457, A_456))), inference(superposition, [status(thm), theory('equality')], [c_22, c_18551])).
% 10.90/4.70  tff(c_18599, plain, (![B_457, A_456]: (k2_xboole_0(B_457, A_456)=k2_xboole_0(A_456, B_457))), inference(superposition, [status(thm), theory('equality')], [c_18593, c_42])).
% 10.90/4.70  tff(c_21219, plain, (![A_456, B_457]: (k5_xboole_0(A_456, k2_xboole_0(A_456, B_457))=k4_xboole_0(B_457, A_456))), inference(superposition, [status(thm), theory('equality')], [c_18599, c_21130])).
% 10.90/4.70  tff(c_29879, plain, (![B_657, A_658]: (k5_xboole_0(B_657, B_657)=k4_xboole_0(k1_tarski(A_658), B_657) | ~r2_hidden(A_658, B_657))), inference(superposition, [status(thm), theory('equality')], [c_29829, c_21219])).
% 10.90/4.70  tff(c_30778, plain, (![A_668, B_669]: (k4_xboole_0(k1_tarski(A_668), B_669)=k1_xboole_0 | ~r2_hidden(A_668, B_669))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_29879])).
% 10.90/4.70  tff(c_18416, plain, (r2_hidden('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_50])).
% 10.90/4.70  tff(c_48, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_xboole_0 | ~r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_86])).
% 10.90/4.70  tff(c_18418, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_18416, c_48])).
% 10.90/4.70  tff(c_30849, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_30778, c_18418])).
% 10.90/4.70  tff(c_30914, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18415, c_30849])).
% 10.90/4.70  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.90/4.70  
% 10.90/4.70  Inference rules
% 10.90/4.70  ----------------------
% 10.90/4.70  #Ref     : 0
% 10.90/4.70  #Sup     : 7539
% 10.90/4.70  #Fact    : 0
% 10.90/4.70  #Define  : 0
% 10.90/4.70  #Split   : 2
% 10.90/4.70  #Chain   : 0
% 10.90/4.70  #Close   : 0
% 10.90/4.70  
% 10.90/4.70  Ordering : KBO
% 10.90/4.70  
% 10.90/4.70  Simplification rules
% 10.90/4.70  ----------------------
% 10.90/4.70  #Subsume      : 538
% 10.90/4.70  #Demod        : 7823
% 10.90/4.70  #Tautology    : 4021
% 10.90/4.70  #SimpNegUnit  : 43
% 10.90/4.70  #BackRed      : 13
% 10.90/4.70  
% 10.90/4.70  #Partial instantiations: 0
% 10.90/4.70  #Strategies tried      : 1
% 10.90/4.70  
% 10.90/4.70  Timing (in seconds)
% 10.90/4.70  ----------------------
% 10.90/4.71  Preprocessing        : 0.31
% 10.90/4.71  Parsing              : 0.16
% 10.90/4.71  CNF conversion       : 0.02
% 10.90/4.71  Main loop            : 3.56
% 10.90/4.71  Inferencing          : 0.77
% 10.90/4.71  Reduction            : 2.00
% 10.90/4.71  Demodulation         : 1.78
% 10.90/4.71  BG Simplification    : 0.11
% 10.90/4.71  Subsumption          : 0.50
% 10.90/4.71  Abstraction          : 0.16
% 10.90/4.71  MUC search           : 0.00
% 10.90/4.71  Cooper               : 0.00
% 10.90/4.71  Total                : 3.92
% 10.90/4.71  Index Insertion      : 0.00
% 10.90/4.71  Index Deletion       : 0.00
% 10.90/4.71  Index Matching       : 0.00
% 10.90/4.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
