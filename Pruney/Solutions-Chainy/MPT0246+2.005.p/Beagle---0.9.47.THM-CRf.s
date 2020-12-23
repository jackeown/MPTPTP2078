%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:00 EST 2020

% Result     : Theorem 17.54s
% Output     : CNFRefutation 17.54s
% Verified   : 
% Statistics : Number of formulae       :  139 (1119 expanded)
%              Number of leaves         :   37 ( 388 expanded)
%              Depth                    :   26
%              Number of atoms          :  199 (1975 expanded)
%              Number of equality atoms :   99 ( 973 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_4 > #skF_3 > #skF_2 > #skF_1

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_123,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( A != k1_tarski(B)
          & A != k1_xboole_0
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & C != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_zfmisc_1)).

tff(f_69,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_79,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_71,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_77,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_81,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_108,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_99,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k4_xboole_0(B,A))
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).

tff(f_103,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k3_xboole_0(B,k1_tarski(A)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l31_zfmisc_1)).

tff(c_54,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_135,plain,(
    ! [A_68] :
      ( r2_hidden('#skF_3'(A_68),A_68)
      | k1_xboole_0 = A_68 ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_52,plain,(
    ! [C_60] :
      ( C_60 = '#skF_5'
      | ~ r2_hidden(C_60,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_139,plain,
    ( '#skF_3'('#skF_4') = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_135,c_52])).

tff(c_142,plain,(
    '#skF_3'('#skF_4') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_139])).

tff(c_16,plain,(
    ! [A_15] :
      ( r2_hidden('#skF_3'(A_15),A_15)
      | k1_xboole_0 = A_15 ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_146,plain,
    ( r2_hidden('#skF_5','#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_16])).

tff(c_149,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_146])).

tff(c_56,plain,(
    k1_tarski('#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_178,plain,(
    ! [A_78,B_79] :
      ( r2_hidden('#skF_1'(A_78,B_79),A_78)
      | r1_xboole_0(A_78,B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_183,plain,(
    ! [B_79] :
      ( '#skF_1'('#skF_4',B_79) = '#skF_5'
      | r1_xboole_0('#skF_4',B_79) ) ),
    inference(resolution,[status(thm)],[c_178,c_52])).

tff(c_426,plain,(
    ! [A_98,B_99,C_100] :
      ( ~ r1_xboole_0(A_98,B_99)
      | ~ r2_hidden(C_100,k3_xboole_0(A_98,B_99)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_478,plain,(
    ! [A_103,B_104] :
      ( ~ r1_xboole_0(A_103,B_104)
      | k3_xboole_0(A_103,B_104) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_16,c_426])).

tff(c_496,plain,(
    ! [B_79] :
      ( k3_xboole_0('#skF_4',B_79) = k1_xboole_0
      | '#skF_1'('#skF_4',B_79) = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_183,c_478])).

tff(c_24,plain,(
    ! [A_23] : k5_xboole_0(A_23,k1_xboole_0) = A_23 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_1'(A_5,B_6),A_5)
      | r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_514,plain,(
    ! [A_105,B_106,B_107] :
      ( ~ r1_xboole_0(A_105,B_106)
      | r1_xboole_0(k3_xboole_0(A_105,B_106),B_107) ) ),
    inference(resolution,[status(thm)],[c_10,c_426])).

tff(c_460,plain,(
    ! [A_98,B_99] :
      ( ~ r1_xboole_0(A_98,B_99)
      | k3_xboole_0(A_98,B_99) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_16,c_426])).

tff(c_2311,plain,(
    ! [A_194,B_195,B_196] :
      ( k3_xboole_0(k3_xboole_0(A_194,B_195),B_196) = k1_xboole_0
      | ~ r1_xboole_0(A_194,B_195) ) ),
    inference(resolution,[status(thm)],[c_514,c_460])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_203,plain,(
    ! [A_83,B_84] : k5_xboole_0(A_83,k3_xboole_0(A_83,B_84)) = k4_xboole_0(A_83,B_84) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_212,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_203])).

tff(c_2344,plain,(
    ! [B_196,A_194,B_195] :
      ( k4_xboole_0(B_196,k3_xboole_0(A_194,B_195)) = k5_xboole_0(B_196,k1_xboole_0)
      | ~ r1_xboole_0(A_194,B_195) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2311,c_212])).

tff(c_3178,plain,(
    ! [B_223,A_224,B_225] :
      ( k4_xboole_0(B_223,k3_xboole_0(A_224,B_225)) = B_223
      | ~ r1_xboole_0(A_224,B_225) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_2344])).

tff(c_185,plain,(
    ! [A_81,B_82] : k4_xboole_0(A_81,k4_xboole_0(A_81,B_82)) = k3_xboole_0(A_81,B_82) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_22,plain,(
    ! [A_21,B_22] : k4_xboole_0(A_21,k4_xboole_0(A_21,B_22)) = k3_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_188,plain,(
    ! [A_81,B_82] : k4_xboole_0(A_81,k3_xboole_0(A_81,B_82)) = k3_xboole_0(A_81,k4_xboole_0(A_81,B_82)) ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_22])).

tff(c_4084,plain,(
    ! [A_250,B_251] :
      ( k3_xboole_0(A_250,k4_xboole_0(A_250,B_251)) = A_250
      | ~ r1_xboole_0(A_250,B_251) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3178,c_188])).

tff(c_4215,plain,(
    ! [B_251] :
      ( k1_xboole_0 = '#skF_4'
      | ~ r1_xboole_0('#skF_4',B_251)
      | '#skF_1'('#skF_4',k4_xboole_0('#skF_4',B_251)) = '#skF_5' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_496,c_4084])).

tff(c_4360,plain,(
    ! [B_253] :
      ( ~ r1_xboole_0('#skF_4',B_253)
      | '#skF_1'('#skF_4',k4_xboole_0('#skF_4',B_253)) = '#skF_5' ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_4215])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_1'(A_5,B_6),B_6)
      | r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_15561,plain,(
    ! [B_383] :
      ( r2_hidden('#skF_5',k4_xboole_0('#skF_4',B_383))
      | r1_xboole_0('#skF_4',k4_xboole_0('#skF_4',B_383))
      | ~ r1_xboole_0('#skF_4',B_383) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4360,c_8])).

tff(c_26,plain,(
    ! [A_24] : k5_xboole_0(A_24,A_24) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_218,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k4_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_203])).

tff(c_221,plain,(
    ! [A_3] : k4_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_218])).

tff(c_48,plain,(
    ! [B_58] : k4_xboole_0(k1_tarski(B_58),k1_tarski(B_58)) != k1_tarski(B_58) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_222,plain,(
    ! [B_58] : k1_tarski(B_58) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_48])).

tff(c_44,plain,(
    ! [A_53,B_54] :
      ( r1_tarski(k1_tarski(A_53),B_54)
      | ~ r2_hidden(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_171,plain,(
    ! [A_75,B_76] :
      ( k1_xboole_0 = A_75
      | ~ r1_tarski(A_75,k4_xboole_0(B_76,A_75)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_176,plain,(
    ! [A_53,B_76] :
      ( k1_tarski(A_53) = k1_xboole_0
      | ~ r2_hidden(A_53,k4_xboole_0(B_76,k1_tarski(A_53))) ) ),
    inference(resolution,[status(thm)],[c_44,c_171])).

tff(c_2288,plain,(
    ! [A_53,B_76] : ~ r2_hidden(A_53,k4_xboole_0(B_76,k1_tarski(A_53))) ),
    inference(negUnitSimplification,[status(thm)],[c_222,c_176])).

tff(c_15627,plain,
    ( r1_xboole_0('#skF_4',k4_xboole_0('#skF_4',k1_tarski('#skF_5')))
    | ~ r1_xboole_0('#skF_4',k1_tarski('#skF_5')) ),
    inference(resolution,[status(thm)],[c_15561,c_2288])).

tff(c_15652,plain,(
    ~ r1_xboole_0('#skF_4',k1_tarski('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_15627])).

tff(c_46,plain,(
    ! [B_56,A_55] :
      ( k3_xboole_0(B_56,k1_tarski(A_55)) = k1_tarski(A_55)
      | ~ r2_hidden(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1654,plain,(
    ! [A_158,B_159] :
      ( r2_hidden('#skF_2'(A_158,B_159),k3_xboole_0(A_158,B_159))
      | r1_xboole_0(A_158,B_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_5289,plain,(
    ! [B_272,A_273] :
      ( r2_hidden('#skF_2'(B_272,k1_tarski(A_273)),k1_tarski(A_273))
      | r1_xboole_0(B_272,k1_tarski(A_273))
      | ~ r2_hidden(A_273,B_272) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_1654])).

tff(c_1200,plain,(
    ! [A_139,B_140] :
      ( k4_xboole_0(k1_tarski(A_139),k1_tarski(B_140)) = k1_tarski(A_139)
      | B_140 = A_139 ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_20,plain,(
    ! [A_19,B_20] :
      ( k1_xboole_0 = A_19
      | ~ r1_tarski(A_19,k4_xboole_0(B_20,A_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1213,plain,(
    ! [B_140,A_139] :
      ( k1_tarski(B_140) = k1_xboole_0
      | ~ r1_tarski(k1_tarski(B_140),k1_tarski(A_139))
      | B_140 = A_139 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1200,c_20])).

tff(c_1229,plain,(
    ! [B_141,A_142] :
      ( ~ r1_tarski(k1_tarski(B_141),k1_tarski(A_142))
      | B_141 = A_142 ) ),
    inference(negUnitSimplification,[status(thm)],[c_222,c_1213])).

tff(c_1234,plain,(
    ! [A_53,A_142] :
      ( A_53 = A_142
      | ~ r2_hidden(A_53,k1_tarski(A_142)) ) ),
    inference(resolution,[status(thm)],[c_44,c_1229])).

tff(c_29647,plain,(
    ! [B_511,A_512] :
      ( '#skF_2'(B_511,k1_tarski(A_512)) = A_512
      | r1_xboole_0(B_511,k1_tarski(A_512))
      | ~ r2_hidden(A_512,B_511) ) ),
    inference(resolution,[status(thm)],[c_5289,c_1234])).

tff(c_29694,plain,
    ( '#skF_2'('#skF_4',k1_tarski('#skF_5')) = '#skF_5'
    | ~ r2_hidden('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_29647,c_15652])).

tff(c_29778,plain,(
    '#skF_2'('#skF_4',k1_tarski('#skF_5')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_29694])).

tff(c_1690,plain,(
    ! [B_2,A_1] :
      ( r2_hidden('#skF_2'(B_2,A_1),k3_xboole_0(A_1,B_2))
      | r1_xboole_0(B_2,A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1654])).

tff(c_29813,plain,
    ( r2_hidden('#skF_5',k3_xboole_0(k1_tarski('#skF_5'),'#skF_4'))
    | r1_xboole_0('#skF_4',k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_29778,c_1690])).

tff(c_29822,plain,
    ( r2_hidden('#skF_5',k3_xboole_0('#skF_4',k1_tarski('#skF_5')))
    | r1_xboole_0('#skF_4',k1_tarski('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_29813])).

tff(c_29823,plain,(
    r2_hidden('#skF_5',k3_xboole_0('#skF_4',k1_tarski('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_15652,c_29822])).

tff(c_1445,plain,(
    ! [B_151,A_152] :
      ( k3_xboole_0(B_151,k1_tarski(A_152)) = k1_tarski(A_152)
      | ~ r2_hidden(A_152,B_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1472,plain,(
    ! [A_152,B_151] :
      ( k5_xboole_0(k1_tarski(A_152),k1_tarski(A_152)) = k4_xboole_0(k1_tarski(A_152),B_151)
      | ~ r2_hidden(A_152,B_151) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1445,c_212])).

tff(c_1533,plain,(
    ! [A_152,B_151] :
      ( k4_xboole_0(k1_tarski(A_152),B_151) = k1_xboole_0
      | ~ r2_hidden(A_152,B_151) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1472])).

tff(c_2811,plain,(
    ! [A_214,B_215] : k4_xboole_0(A_214,k3_xboole_0(A_214,B_215)) = k3_xboole_0(A_214,k4_xboole_0(A_214,B_215)) ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_22])).

tff(c_5120,plain,(
    ! [B_270,A_271] : k4_xboole_0(B_270,k3_xboole_0(A_271,B_270)) = k3_xboole_0(B_270,k4_xboole_0(B_270,A_271)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2811])).

tff(c_47832,plain,(
    ! [A_661,A_662] :
      ( k3_xboole_0(k1_tarski(A_661),k4_xboole_0(k1_tarski(A_661),A_662)) = k1_xboole_0
      | ~ r2_hidden(A_661,k3_xboole_0(A_662,k1_tarski(A_661))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1533,c_5120])).

tff(c_18,plain,(
    ! [A_17,B_18] : k5_xboole_0(A_17,k3_xboole_0(A_17,B_18)) = k4_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_48116,plain,(
    ! [A_661,A_662] :
      ( k4_xboole_0(k1_tarski(A_661),k4_xboole_0(k1_tarski(A_661),A_662)) = k5_xboole_0(k1_tarski(A_661),k1_xboole_0)
      | ~ r2_hidden(A_661,k3_xboole_0(A_662,k1_tarski(A_661))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_47832,c_18])).

tff(c_65517,plain,(
    ! [A_786,A_787] :
      ( k3_xboole_0(k1_tarski(A_786),A_787) = k1_tarski(A_786)
      | ~ r2_hidden(A_786,k3_xboole_0(A_787,k1_tarski(A_786))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_48116])).

tff(c_65593,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),'#skF_4') = k1_tarski('#skF_5') ),
    inference(resolution,[status(thm)],[c_29823,c_65517])).

tff(c_65913,plain,(
    k3_xboole_0('#skF_4',k1_tarski('#skF_5')) = k1_tarski('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_65593,c_2])).

tff(c_223,plain,(
    ! [A_85] : k4_xboole_0(A_85,A_85) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_218])).

tff(c_228,plain,(
    ! [A_85] : k4_xboole_0(A_85,k1_xboole_0) = k3_xboole_0(A_85,A_85) ),
    inference(superposition,[status(thm),theory(equality)],[c_223,c_22])).

tff(c_235,plain,(
    ! [A_85] : k4_xboole_0(A_85,k1_xboole_0) = A_85 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_228])).

tff(c_13853,plain,(
    ! [A_355,B_356] : k4_xboole_0(A_355,k3_xboole_0(A_355,k4_xboole_0(A_355,B_356))) = k3_xboole_0(A_355,k3_xboole_0(A_355,B_356)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2811,c_22])).

tff(c_14112,plain,(
    ! [B_356] :
      ( k3_xboole_0('#skF_4',k3_xboole_0('#skF_4',B_356)) = k4_xboole_0('#skF_4',k1_xboole_0)
      | '#skF_1'('#skF_4',k4_xboole_0('#skF_4',B_356)) = '#skF_5' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_496,c_13853])).

tff(c_14164,plain,(
    ! [B_356] :
      ( k3_xboole_0('#skF_4',k3_xboole_0('#skF_4',B_356)) = '#skF_4'
      | '#skF_1'('#skF_4',k4_xboole_0('#skF_4',B_356)) = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_235,c_14112])).

tff(c_66678,plain,
    ( k3_xboole_0('#skF_4',k1_tarski('#skF_5')) = '#skF_4'
    | '#skF_1'('#skF_4',k4_xboole_0('#skF_4',k1_tarski('#skF_5'))) = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_65913,c_14164])).

tff(c_66937,plain,
    ( k1_tarski('#skF_5') = '#skF_4'
    | '#skF_1'('#skF_4',k4_xboole_0('#skF_4',k1_tarski('#skF_5'))) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_65913,c_66678])).

tff(c_66938,plain,(
    '#skF_1'('#skF_4',k4_xboole_0('#skF_4',k1_tarski('#skF_5'))) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_66937])).

tff(c_67160,plain,
    ( r2_hidden('#skF_5',k4_xboole_0('#skF_4',k1_tarski('#skF_5')))
    | r1_xboole_0('#skF_4',k4_xboole_0('#skF_4',k1_tarski('#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_66938,c_8])).

tff(c_67231,plain,(
    r1_xboole_0('#skF_4',k4_xboole_0('#skF_4',k1_tarski('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_2288,c_67160])).

tff(c_22986,plain,(
    ! [B_462,A_463] : k4_xboole_0(B_462,k3_xboole_0(B_462,k4_xboole_0(B_462,A_463))) = k3_xboole_0(B_462,k3_xboole_0(A_463,B_462)) ),
    inference(superposition,[status(thm),theory(equality)],[c_5120,c_22])).

tff(c_2448,plain,(
    ! [B_196,A_194,B_195] :
      ( k4_xboole_0(B_196,k3_xboole_0(A_194,B_195)) = B_196
      | ~ r1_xboole_0(A_194,B_195) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_2344])).

tff(c_23167,plain,(
    ! [B_462,A_463] :
      ( k3_xboole_0(B_462,k3_xboole_0(A_463,B_462)) = B_462
      | ~ r1_xboole_0(B_462,k4_xboole_0(B_462,A_463)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22986,c_2448])).

tff(c_67287,plain,(
    k3_xboole_0('#skF_4',k3_xboole_0(k1_tarski('#skF_5'),'#skF_4')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_67231,c_23167])).

tff(c_67341,plain,(
    k1_tarski('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_65913,c_65913,c_2,c_67287])).

tff(c_67343,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_67341])).

tff(c_67345,plain,(
    r1_xboole_0('#skF_4',k1_tarski('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_15627])).

tff(c_238,plain,(
    ! [A_87] : k4_xboole_0(A_87,k1_xboole_0) = A_87 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_228])).

tff(c_248,plain,(
    ! [A_87] : k4_xboole_0(A_87,A_87) = k3_xboole_0(A_87,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_238,c_22])).

tff(c_261,plain,(
    ! [A_87] : k3_xboole_0(A_87,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_248])).

tff(c_576,plain,(
    ! [A_113,B_114,C_115] :
      ( ~ r1_xboole_0(A_113,B_114)
      | ~ r2_hidden(C_115,k3_xboole_0(B_114,A_113)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_426])).

tff(c_806,plain,(
    ! [A_126,B_127,A_128] :
      ( ~ r1_xboole_0(A_126,B_127)
      | r1_xboole_0(A_128,k3_xboole_0(B_127,A_126)) ) ),
    inference(resolution,[status(thm)],[c_8,c_576])).

tff(c_3433,plain,(
    ! [A_230,B_231,A_232] :
      ( k3_xboole_0(A_230,k3_xboole_0(B_231,A_232)) = k1_xboole_0
      | ~ r1_xboole_0(A_232,B_231) ) ),
    inference(resolution,[status(thm)],[c_806,c_460])).

tff(c_3508,plain,(
    ! [A_230,B_231,A_232] :
      ( k4_xboole_0(A_230,k3_xboole_0(B_231,A_232)) = k5_xboole_0(A_230,k1_xboole_0)
      | ~ r1_xboole_0(A_232,B_231) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3433,c_18])).

tff(c_3724,plain,(
    ! [A_238,B_239,A_240] :
      ( k4_xboole_0(A_238,k3_xboole_0(B_239,A_240)) = A_238
      | ~ r1_xboole_0(A_240,B_239) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_3508])).

tff(c_4722,plain,(
    ! [B_264,A_265] :
      ( k3_xboole_0(B_264,k4_xboole_0(B_264,A_265)) = B_264
      | ~ r1_xboole_0(A_265,B_264) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3724,c_188])).

tff(c_4842,plain,(
    ! [A_152,B_151] :
      ( k3_xboole_0(k1_tarski(A_152),k1_xboole_0) = k1_tarski(A_152)
      | ~ r1_xboole_0(B_151,k1_tarski(A_152))
      | ~ r2_hidden(A_152,B_151) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1533,c_4722])).

tff(c_4894,plain,(
    ! [A_152,B_151] :
      ( k1_tarski(A_152) = k1_xboole_0
      | ~ r1_xboole_0(B_151,k1_tarski(A_152))
      | ~ r2_hidden(A_152,B_151) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_261,c_4842])).

tff(c_4895,plain,(
    ! [B_151,A_152] :
      ( ~ r1_xboole_0(B_151,k1_tarski(A_152))
      | ~ r2_hidden(A_152,B_151) ) ),
    inference(negUnitSimplification,[status(thm)],[c_222,c_4894])).

tff(c_67348,plain,(
    ~ r2_hidden('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_67345,c_4895])).

tff(c_67362,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_67348])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:12:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 17.54/9.14  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.54/9.15  
% 17.54/9.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.54/9.15  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 17.54/9.15  
% 17.54/9.15  %Foreground sorts:
% 17.54/9.15  
% 17.54/9.15  
% 17.54/9.15  %Background operators:
% 17.54/9.15  
% 17.54/9.15  
% 17.54/9.15  %Foreground operators:
% 17.54/9.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 17.54/9.15  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 17.54/9.15  tff(k1_tarski, type, k1_tarski: $i > $i).
% 17.54/9.15  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 17.54/9.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 17.54/9.15  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 17.54/9.15  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 17.54/9.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 17.54/9.15  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 17.54/9.15  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 17.54/9.15  tff('#skF_5', type, '#skF_5': $i).
% 17.54/9.15  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 17.54/9.15  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 17.54/9.15  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 17.54/9.15  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 17.54/9.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 17.54/9.15  tff('#skF_4', type, '#skF_4': $i).
% 17.54/9.15  tff('#skF_3', type, '#skF_3': $i > $i).
% 17.54/9.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 17.54/9.15  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 17.54/9.15  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 17.54/9.15  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 17.54/9.15  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 17.54/9.15  
% 17.54/9.17  tff(f_123, negated_conjecture, ~(![A, B]: ~((~(A = k1_tarski(B)) & ~(A = k1_xboole_0)) & (![C]: ~(r2_hidden(C, A) & ~(C = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_zfmisc_1)).
% 17.54/9.17  tff(f_69, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 17.54/9.17  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 17.54/9.17  tff(f_61, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 17.54/9.17  tff(f_79, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 17.54/9.17  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 17.54/9.17  tff(f_71, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 17.54/9.17  tff(f_77, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 17.54/9.17  tff(f_81, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 17.54/9.17  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 17.54/9.17  tff(f_108, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 17.54/9.17  tff(f_99, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 17.54/9.17  tff(f_75, axiom, (![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_xboole_1)).
% 17.54/9.17  tff(f_103, axiom, (![A, B]: (r2_hidden(A, B) => (k3_xboole_0(B, k1_tarski(A)) = k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l31_zfmisc_1)).
% 17.54/9.17  tff(c_54, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_123])).
% 17.54/9.17  tff(c_135, plain, (![A_68]: (r2_hidden('#skF_3'(A_68), A_68) | k1_xboole_0=A_68)), inference(cnfTransformation, [status(thm)], [f_69])).
% 17.54/9.17  tff(c_52, plain, (![C_60]: (C_60='#skF_5' | ~r2_hidden(C_60, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_123])).
% 17.54/9.17  tff(c_139, plain, ('#skF_3'('#skF_4')='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_135, c_52])).
% 17.54/9.17  tff(c_142, plain, ('#skF_3'('#skF_4')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_54, c_139])).
% 17.54/9.17  tff(c_16, plain, (![A_15]: (r2_hidden('#skF_3'(A_15), A_15) | k1_xboole_0=A_15)), inference(cnfTransformation, [status(thm)], [f_69])).
% 17.54/9.17  tff(c_146, plain, (r2_hidden('#skF_5', '#skF_4') | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_142, c_16])).
% 17.54/9.17  tff(c_149, plain, (r2_hidden('#skF_5', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_54, c_146])).
% 17.54/9.17  tff(c_56, plain, (k1_tarski('#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_123])).
% 17.54/9.17  tff(c_178, plain, (![A_78, B_79]: (r2_hidden('#skF_1'(A_78, B_79), A_78) | r1_xboole_0(A_78, B_79))), inference(cnfTransformation, [status(thm)], [f_47])).
% 17.54/9.17  tff(c_183, plain, (![B_79]: ('#skF_1'('#skF_4', B_79)='#skF_5' | r1_xboole_0('#skF_4', B_79))), inference(resolution, [status(thm)], [c_178, c_52])).
% 17.54/9.17  tff(c_426, plain, (![A_98, B_99, C_100]: (~r1_xboole_0(A_98, B_99) | ~r2_hidden(C_100, k3_xboole_0(A_98, B_99)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 17.54/9.17  tff(c_478, plain, (![A_103, B_104]: (~r1_xboole_0(A_103, B_104) | k3_xboole_0(A_103, B_104)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_426])).
% 17.54/9.17  tff(c_496, plain, (![B_79]: (k3_xboole_0('#skF_4', B_79)=k1_xboole_0 | '#skF_1'('#skF_4', B_79)='#skF_5')), inference(resolution, [status(thm)], [c_183, c_478])).
% 17.54/9.17  tff(c_24, plain, (![A_23]: (k5_xboole_0(A_23, k1_xboole_0)=A_23)), inference(cnfTransformation, [status(thm)], [f_79])).
% 17.54/9.17  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_1'(A_5, B_6), A_5) | r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_47])).
% 17.54/9.17  tff(c_514, plain, (![A_105, B_106, B_107]: (~r1_xboole_0(A_105, B_106) | r1_xboole_0(k3_xboole_0(A_105, B_106), B_107))), inference(resolution, [status(thm)], [c_10, c_426])).
% 17.54/9.17  tff(c_460, plain, (![A_98, B_99]: (~r1_xboole_0(A_98, B_99) | k3_xboole_0(A_98, B_99)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_426])).
% 17.54/9.17  tff(c_2311, plain, (![A_194, B_195, B_196]: (k3_xboole_0(k3_xboole_0(A_194, B_195), B_196)=k1_xboole_0 | ~r1_xboole_0(A_194, B_195))), inference(resolution, [status(thm)], [c_514, c_460])).
% 17.54/9.17  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 17.54/9.17  tff(c_203, plain, (![A_83, B_84]: (k5_xboole_0(A_83, k3_xboole_0(A_83, B_84))=k4_xboole_0(A_83, B_84))), inference(cnfTransformation, [status(thm)], [f_71])).
% 17.54/9.17  tff(c_212, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_203])).
% 17.54/9.17  tff(c_2344, plain, (![B_196, A_194, B_195]: (k4_xboole_0(B_196, k3_xboole_0(A_194, B_195))=k5_xboole_0(B_196, k1_xboole_0) | ~r1_xboole_0(A_194, B_195))), inference(superposition, [status(thm), theory('equality')], [c_2311, c_212])).
% 17.54/9.17  tff(c_3178, plain, (![B_223, A_224, B_225]: (k4_xboole_0(B_223, k3_xboole_0(A_224, B_225))=B_223 | ~r1_xboole_0(A_224, B_225))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_2344])).
% 17.54/9.17  tff(c_185, plain, (![A_81, B_82]: (k4_xboole_0(A_81, k4_xboole_0(A_81, B_82))=k3_xboole_0(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_77])).
% 17.54/9.17  tff(c_22, plain, (![A_21, B_22]: (k4_xboole_0(A_21, k4_xboole_0(A_21, B_22))=k3_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_77])).
% 17.54/9.17  tff(c_188, plain, (![A_81, B_82]: (k4_xboole_0(A_81, k3_xboole_0(A_81, B_82))=k3_xboole_0(A_81, k4_xboole_0(A_81, B_82)))), inference(superposition, [status(thm), theory('equality')], [c_185, c_22])).
% 17.54/9.17  tff(c_4084, plain, (![A_250, B_251]: (k3_xboole_0(A_250, k4_xboole_0(A_250, B_251))=A_250 | ~r1_xboole_0(A_250, B_251))), inference(superposition, [status(thm), theory('equality')], [c_3178, c_188])).
% 17.54/9.17  tff(c_4215, plain, (![B_251]: (k1_xboole_0='#skF_4' | ~r1_xboole_0('#skF_4', B_251) | '#skF_1'('#skF_4', k4_xboole_0('#skF_4', B_251))='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_496, c_4084])).
% 17.54/9.17  tff(c_4360, plain, (![B_253]: (~r1_xboole_0('#skF_4', B_253) | '#skF_1'('#skF_4', k4_xboole_0('#skF_4', B_253))='#skF_5')), inference(negUnitSimplification, [status(thm)], [c_54, c_4215])).
% 17.54/9.17  tff(c_8, plain, (![A_5, B_6]: (r2_hidden('#skF_1'(A_5, B_6), B_6) | r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_47])).
% 17.54/9.17  tff(c_15561, plain, (![B_383]: (r2_hidden('#skF_5', k4_xboole_0('#skF_4', B_383)) | r1_xboole_0('#skF_4', k4_xboole_0('#skF_4', B_383)) | ~r1_xboole_0('#skF_4', B_383))), inference(superposition, [status(thm), theory('equality')], [c_4360, c_8])).
% 17.54/9.17  tff(c_26, plain, (![A_24]: (k5_xboole_0(A_24, A_24)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_81])).
% 17.54/9.17  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 17.54/9.17  tff(c_218, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k4_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_203])).
% 17.54/9.17  tff(c_221, plain, (![A_3]: (k4_xboole_0(A_3, A_3)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_218])).
% 17.54/9.17  tff(c_48, plain, (![B_58]: (k4_xboole_0(k1_tarski(B_58), k1_tarski(B_58))!=k1_tarski(B_58))), inference(cnfTransformation, [status(thm)], [f_108])).
% 17.54/9.17  tff(c_222, plain, (![B_58]: (k1_tarski(B_58)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_221, c_48])).
% 17.54/9.17  tff(c_44, plain, (![A_53, B_54]: (r1_tarski(k1_tarski(A_53), B_54) | ~r2_hidden(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_99])).
% 17.54/9.17  tff(c_171, plain, (![A_75, B_76]: (k1_xboole_0=A_75 | ~r1_tarski(A_75, k4_xboole_0(B_76, A_75)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 17.54/9.17  tff(c_176, plain, (![A_53, B_76]: (k1_tarski(A_53)=k1_xboole_0 | ~r2_hidden(A_53, k4_xboole_0(B_76, k1_tarski(A_53))))), inference(resolution, [status(thm)], [c_44, c_171])).
% 17.54/9.17  tff(c_2288, plain, (![A_53, B_76]: (~r2_hidden(A_53, k4_xboole_0(B_76, k1_tarski(A_53))))), inference(negUnitSimplification, [status(thm)], [c_222, c_176])).
% 17.54/9.17  tff(c_15627, plain, (r1_xboole_0('#skF_4', k4_xboole_0('#skF_4', k1_tarski('#skF_5'))) | ~r1_xboole_0('#skF_4', k1_tarski('#skF_5'))), inference(resolution, [status(thm)], [c_15561, c_2288])).
% 17.54/9.17  tff(c_15652, plain, (~r1_xboole_0('#skF_4', k1_tarski('#skF_5'))), inference(splitLeft, [status(thm)], [c_15627])).
% 17.54/9.17  tff(c_46, plain, (![B_56, A_55]: (k3_xboole_0(B_56, k1_tarski(A_55))=k1_tarski(A_55) | ~r2_hidden(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_103])).
% 17.54/9.17  tff(c_1654, plain, (![A_158, B_159]: (r2_hidden('#skF_2'(A_158, B_159), k3_xboole_0(A_158, B_159)) | r1_xboole_0(A_158, B_159))), inference(cnfTransformation, [status(thm)], [f_61])).
% 17.54/9.17  tff(c_5289, plain, (![B_272, A_273]: (r2_hidden('#skF_2'(B_272, k1_tarski(A_273)), k1_tarski(A_273)) | r1_xboole_0(B_272, k1_tarski(A_273)) | ~r2_hidden(A_273, B_272))), inference(superposition, [status(thm), theory('equality')], [c_46, c_1654])).
% 17.54/9.17  tff(c_1200, plain, (![A_139, B_140]: (k4_xboole_0(k1_tarski(A_139), k1_tarski(B_140))=k1_tarski(A_139) | B_140=A_139)), inference(cnfTransformation, [status(thm)], [f_108])).
% 17.54/9.17  tff(c_20, plain, (![A_19, B_20]: (k1_xboole_0=A_19 | ~r1_tarski(A_19, k4_xboole_0(B_20, A_19)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 17.54/9.17  tff(c_1213, plain, (![B_140, A_139]: (k1_tarski(B_140)=k1_xboole_0 | ~r1_tarski(k1_tarski(B_140), k1_tarski(A_139)) | B_140=A_139)), inference(superposition, [status(thm), theory('equality')], [c_1200, c_20])).
% 17.54/9.17  tff(c_1229, plain, (![B_141, A_142]: (~r1_tarski(k1_tarski(B_141), k1_tarski(A_142)) | B_141=A_142)), inference(negUnitSimplification, [status(thm)], [c_222, c_1213])).
% 17.54/9.17  tff(c_1234, plain, (![A_53, A_142]: (A_53=A_142 | ~r2_hidden(A_53, k1_tarski(A_142)))), inference(resolution, [status(thm)], [c_44, c_1229])).
% 17.54/9.17  tff(c_29647, plain, (![B_511, A_512]: ('#skF_2'(B_511, k1_tarski(A_512))=A_512 | r1_xboole_0(B_511, k1_tarski(A_512)) | ~r2_hidden(A_512, B_511))), inference(resolution, [status(thm)], [c_5289, c_1234])).
% 17.54/9.17  tff(c_29694, plain, ('#skF_2'('#skF_4', k1_tarski('#skF_5'))='#skF_5' | ~r2_hidden('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_29647, c_15652])).
% 17.54/9.17  tff(c_29778, plain, ('#skF_2'('#skF_4', k1_tarski('#skF_5'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_149, c_29694])).
% 17.54/9.17  tff(c_1690, plain, (![B_2, A_1]: (r2_hidden('#skF_2'(B_2, A_1), k3_xboole_0(A_1, B_2)) | r1_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1654])).
% 17.54/9.17  tff(c_29813, plain, (r2_hidden('#skF_5', k3_xboole_0(k1_tarski('#skF_5'), '#skF_4')) | r1_xboole_0('#skF_4', k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_29778, c_1690])).
% 17.54/9.17  tff(c_29822, plain, (r2_hidden('#skF_5', k3_xboole_0('#skF_4', k1_tarski('#skF_5'))) | r1_xboole_0('#skF_4', k1_tarski('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_29813])).
% 17.54/9.17  tff(c_29823, plain, (r2_hidden('#skF_5', k3_xboole_0('#skF_4', k1_tarski('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_15652, c_29822])).
% 17.54/9.17  tff(c_1445, plain, (![B_151, A_152]: (k3_xboole_0(B_151, k1_tarski(A_152))=k1_tarski(A_152) | ~r2_hidden(A_152, B_151))), inference(cnfTransformation, [status(thm)], [f_103])).
% 17.54/9.17  tff(c_1472, plain, (![A_152, B_151]: (k5_xboole_0(k1_tarski(A_152), k1_tarski(A_152))=k4_xboole_0(k1_tarski(A_152), B_151) | ~r2_hidden(A_152, B_151))), inference(superposition, [status(thm), theory('equality')], [c_1445, c_212])).
% 17.54/9.17  tff(c_1533, plain, (![A_152, B_151]: (k4_xboole_0(k1_tarski(A_152), B_151)=k1_xboole_0 | ~r2_hidden(A_152, B_151))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1472])).
% 17.54/9.17  tff(c_2811, plain, (![A_214, B_215]: (k4_xboole_0(A_214, k3_xboole_0(A_214, B_215))=k3_xboole_0(A_214, k4_xboole_0(A_214, B_215)))), inference(superposition, [status(thm), theory('equality')], [c_185, c_22])).
% 17.54/9.17  tff(c_5120, plain, (![B_270, A_271]: (k4_xboole_0(B_270, k3_xboole_0(A_271, B_270))=k3_xboole_0(B_270, k4_xboole_0(B_270, A_271)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_2811])).
% 17.54/9.17  tff(c_47832, plain, (![A_661, A_662]: (k3_xboole_0(k1_tarski(A_661), k4_xboole_0(k1_tarski(A_661), A_662))=k1_xboole_0 | ~r2_hidden(A_661, k3_xboole_0(A_662, k1_tarski(A_661))))), inference(superposition, [status(thm), theory('equality')], [c_1533, c_5120])).
% 17.54/9.17  tff(c_18, plain, (![A_17, B_18]: (k5_xboole_0(A_17, k3_xboole_0(A_17, B_18))=k4_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_71])).
% 17.54/9.17  tff(c_48116, plain, (![A_661, A_662]: (k4_xboole_0(k1_tarski(A_661), k4_xboole_0(k1_tarski(A_661), A_662))=k5_xboole_0(k1_tarski(A_661), k1_xboole_0) | ~r2_hidden(A_661, k3_xboole_0(A_662, k1_tarski(A_661))))), inference(superposition, [status(thm), theory('equality')], [c_47832, c_18])).
% 17.54/9.17  tff(c_65517, plain, (![A_786, A_787]: (k3_xboole_0(k1_tarski(A_786), A_787)=k1_tarski(A_786) | ~r2_hidden(A_786, k3_xboole_0(A_787, k1_tarski(A_786))))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_48116])).
% 17.54/9.17  tff(c_65593, plain, (k3_xboole_0(k1_tarski('#skF_5'), '#skF_4')=k1_tarski('#skF_5')), inference(resolution, [status(thm)], [c_29823, c_65517])).
% 17.54/9.17  tff(c_65913, plain, (k3_xboole_0('#skF_4', k1_tarski('#skF_5'))=k1_tarski('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_65593, c_2])).
% 17.54/9.17  tff(c_223, plain, (![A_85]: (k4_xboole_0(A_85, A_85)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_218])).
% 17.54/9.17  tff(c_228, plain, (![A_85]: (k4_xboole_0(A_85, k1_xboole_0)=k3_xboole_0(A_85, A_85))), inference(superposition, [status(thm), theory('equality')], [c_223, c_22])).
% 17.54/9.17  tff(c_235, plain, (![A_85]: (k4_xboole_0(A_85, k1_xboole_0)=A_85)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_228])).
% 17.54/9.17  tff(c_13853, plain, (![A_355, B_356]: (k4_xboole_0(A_355, k3_xboole_0(A_355, k4_xboole_0(A_355, B_356)))=k3_xboole_0(A_355, k3_xboole_0(A_355, B_356)))), inference(superposition, [status(thm), theory('equality')], [c_2811, c_22])).
% 17.54/9.17  tff(c_14112, plain, (![B_356]: (k3_xboole_0('#skF_4', k3_xboole_0('#skF_4', B_356))=k4_xboole_0('#skF_4', k1_xboole_0) | '#skF_1'('#skF_4', k4_xboole_0('#skF_4', B_356))='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_496, c_13853])).
% 17.54/9.17  tff(c_14164, plain, (![B_356]: (k3_xboole_0('#skF_4', k3_xboole_0('#skF_4', B_356))='#skF_4' | '#skF_1'('#skF_4', k4_xboole_0('#skF_4', B_356))='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_235, c_14112])).
% 17.54/9.17  tff(c_66678, plain, (k3_xboole_0('#skF_4', k1_tarski('#skF_5'))='#skF_4' | '#skF_1'('#skF_4', k4_xboole_0('#skF_4', k1_tarski('#skF_5')))='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_65913, c_14164])).
% 17.54/9.17  tff(c_66937, plain, (k1_tarski('#skF_5')='#skF_4' | '#skF_1'('#skF_4', k4_xboole_0('#skF_4', k1_tarski('#skF_5')))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_65913, c_66678])).
% 17.54/9.17  tff(c_66938, plain, ('#skF_1'('#skF_4', k4_xboole_0('#skF_4', k1_tarski('#skF_5')))='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_56, c_66937])).
% 17.54/9.17  tff(c_67160, plain, (r2_hidden('#skF_5', k4_xboole_0('#skF_4', k1_tarski('#skF_5'))) | r1_xboole_0('#skF_4', k4_xboole_0('#skF_4', k1_tarski('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_66938, c_8])).
% 17.54/9.17  tff(c_67231, plain, (r1_xboole_0('#skF_4', k4_xboole_0('#skF_4', k1_tarski('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_2288, c_67160])).
% 17.54/9.17  tff(c_22986, plain, (![B_462, A_463]: (k4_xboole_0(B_462, k3_xboole_0(B_462, k4_xboole_0(B_462, A_463)))=k3_xboole_0(B_462, k3_xboole_0(A_463, B_462)))), inference(superposition, [status(thm), theory('equality')], [c_5120, c_22])).
% 17.54/9.17  tff(c_2448, plain, (![B_196, A_194, B_195]: (k4_xboole_0(B_196, k3_xboole_0(A_194, B_195))=B_196 | ~r1_xboole_0(A_194, B_195))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_2344])).
% 17.54/9.17  tff(c_23167, plain, (![B_462, A_463]: (k3_xboole_0(B_462, k3_xboole_0(A_463, B_462))=B_462 | ~r1_xboole_0(B_462, k4_xboole_0(B_462, A_463)))), inference(superposition, [status(thm), theory('equality')], [c_22986, c_2448])).
% 17.54/9.17  tff(c_67287, plain, (k3_xboole_0('#skF_4', k3_xboole_0(k1_tarski('#skF_5'), '#skF_4'))='#skF_4'), inference(resolution, [status(thm)], [c_67231, c_23167])).
% 17.54/9.17  tff(c_67341, plain, (k1_tarski('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_65913, c_65913, c_2, c_67287])).
% 17.54/9.17  tff(c_67343, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_67341])).
% 17.54/9.17  tff(c_67345, plain, (r1_xboole_0('#skF_4', k1_tarski('#skF_5'))), inference(splitRight, [status(thm)], [c_15627])).
% 17.54/9.17  tff(c_238, plain, (![A_87]: (k4_xboole_0(A_87, k1_xboole_0)=A_87)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_228])).
% 17.54/9.17  tff(c_248, plain, (![A_87]: (k4_xboole_0(A_87, A_87)=k3_xboole_0(A_87, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_238, c_22])).
% 17.54/9.17  tff(c_261, plain, (![A_87]: (k3_xboole_0(A_87, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_221, c_248])).
% 17.54/9.17  tff(c_576, plain, (![A_113, B_114, C_115]: (~r1_xboole_0(A_113, B_114) | ~r2_hidden(C_115, k3_xboole_0(B_114, A_113)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_426])).
% 17.54/9.17  tff(c_806, plain, (![A_126, B_127, A_128]: (~r1_xboole_0(A_126, B_127) | r1_xboole_0(A_128, k3_xboole_0(B_127, A_126)))), inference(resolution, [status(thm)], [c_8, c_576])).
% 17.54/9.17  tff(c_3433, plain, (![A_230, B_231, A_232]: (k3_xboole_0(A_230, k3_xboole_0(B_231, A_232))=k1_xboole_0 | ~r1_xboole_0(A_232, B_231))), inference(resolution, [status(thm)], [c_806, c_460])).
% 17.54/9.17  tff(c_3508, plain, (![A_230, B_231, A_232]: (k4_xboole_0(A_230, k3_xboole_0(B_231, A_232))=k5_xboole_0(A_230, k1_xboole_0) | ~r1_xboole_0(A_232, B_231))), inference(superposition, [status(thm), theory('equality')], [c_3433, c_18])).
% 17.54/9.17  tff(c_3724, plain, (![A_238, B_239, A_240]: (k4_xboole_0(A_238, k3_xboole_0(B_239, A_240))=A_238 | ~r1_xboole_0(A_240, B_239))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_3508])).
% 17.54/9.17  tff(c_4722, plain, (![B_264, A_265]: (k3_xboole_0(B_264, k4_xboole_0(B_264, A_265))=B_264 | ~r1_xboole_0(A_265, B_264))), inference(superposition, [status(thm), theory('equality')], [c_3724, c_188])).
% 17.54/9.17  tff(c_4842, plain, (![A_152, B_151]: (k3_xboole_0(k1_tarski(A_152), k1_xboole_0)=k1_tarski(A_152) | ~r1_xboole_0(B_151, k1_tarski(A_152)) | ~r2_hidden(A_152, B_151))), inference(superposition, [status(thm), theory('equality')], [c_1533, c_4722])).
% 17.54/9.17  tff(c_4894, plain, (![A_152, B_151]: (k1_tarski(A_152)=k1_xboole_0 | ~r1_xboole_0(B_151, k1_tarski(A_152)) | ~r2_hidden(A_152, B_151))), inference(demodulation, [status(thm), theory('equality')], [c_261, c_4842])).
% 17.54/9.17  tff(c_4895, plain, (![B_151, A_152]: (~r1_xboole_0(B_151, k1_tarski(A_152)) | ~r2_hidden(A_152, B_151))), inference(negUnitSimplification, [status(thm)], [c_222, c_4894])).
% 17.54/9.17  tff(c_67348, plain, (~r2_hidden('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_67345, c_4895])).
% 17.54/9.17  tff(c_67362, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_149, c_67348])).
% 17.54/9.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.54/9.17  
% 17.54/9.17  Inference rules
% 17.54/9.17  ----------------------
% 17.54/9.17  #Ref     : 0
% 17.54/9.17  #Sup     : 16471
% 17.54/9.17  #Fact    : 0
% 17.54/9.17  #Define  : 0
% 17.54/9.17  #Split   : 3
% 17.54/9.17  #Chain   : 0
% 17.54/9.17  #Close   : 0
% 17.54/9.17  
% 17.54/9.17  Ordering : KBO
% 17.54/9.17  
% 17.54/9.17  Simplification rules
% 17.54/9.17  ----------------------
% 17.54/9.17  #Subsume      : 6861
% 17.54/9.17  #Demod        : 11818
% 17.54/9.17  #Tautology    : 5808
% 17.54/9.17  #SimpNegUnit  : 1274
% 17.54/9.17  #BackRed      : 5
% 17.54/9.17  
% 17.54/9.17  #Partial instantiations: 0
% 17.54/9.17  #Strategies tried      : 1
% 17.54/9.17  
% 17.54/9.17  Timing (in seconds)
% 17.54/9.17  ----------------------
% 17.54/9.17  Preprocessing        : 0.32
% 17.54/9.17  Parsing              : 0.17
% 17.54/9.17  CNF conversion       : 0.02
% 17.54/9.17  Main loop            : 7.98
% 17.54/9.17  Inferencing          : 1.44
% 17.54/9.18  Reduction            : 2.94
% 17.54/9.18  Demodulation         : 2.29
% 17.54/9.18  BG Simplification    : 0.14
% 17.54/9.18  Subsumption          : 3.11
% 17.54/9.18  Abstraction          : 0.24
% 17.54/9.18  MUC search           : 0.00
% 17.54/9.18  Cooper               : 0.00
% 17.54/9.18  Total                : 8.35
% 17.54/9.18  Index Insertion      : 0.00
% 17.54/9.18  Index Deletion       : 0.00
% 17.54/9.18  Index Matching       : 0.00
% 17.54/9.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
