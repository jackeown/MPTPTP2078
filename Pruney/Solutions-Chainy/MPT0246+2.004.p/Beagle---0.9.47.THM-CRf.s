%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:00 EST 2020

% Result     : Theorem 15.68s
% Output     : CNFRefutation 15.75s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 998 expanded)
%              Number of leaves         :   28 ( 347 expanded)
%              Depth                    :   24
%              Number of atoms          :  207 (1954 expanded)
%              Number of equality atoms :  104 ( 777 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_5 > #skF_6 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_105,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( A != k1_tarski(B)
          & A != k1_xboole_0
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & C != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_69,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_55,axiom,(
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

tff(f_67,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_75,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_71,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(c_58,plain,(
    k1_tarski('#skF_6') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_34,plain,(
    ! [A_18] : k4_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_26,plain,(
    ! [A_9,B_10] :
      ( r2_hidden('#skF_3'(A_9,B_10),A_9)
      | r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_164,plain,(
    ! [A_55,B_56] :
      ( r1_tarski(A_55,B_56)
      | k4_xboole_0(A_55,B_56) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_48,plain,(
    ! [A_29,B_30] :
      ( r2_hidden(A_29,B_30)
      | ~ r1_tarski(k1_tarski(A_29),B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_334,plain,(
    ! [A_78,B_79] :
      ( r2_hidden(A_78,B_79)
      | k4_xboole_0(k1_tarski(A_78),B_79) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_164,c_48])).

tff(c_346,plain,(
    ! [A_78] :
      ( r2_hidden(A_78,k1_xboole_0)
      | k1_tarski(A_78) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_334])).

tff(c_348,plain,(
    ! [A_80] :
      ( r2_hidden(A_80,k1_xboole_0)
      | k1_tarski(A_80) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_334])).

tff(c_220,plain,(
    ! [D_66,B_67,A_68] :
      ( ~ r2_hidden(D_66,B_67)
      | ~ r2_hidden(D_66,k4_xboole_0(A_68,B_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_235,plain,(
    ! [D_66,A_18] :
      ( ~ r2_hidden(D_66,k1_xboole_0)
      | ~ r2_hidden(D_66,A_18) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_220])).

tff(c_352,plain,(
    ! [A_81,A_82] :
      ( ~ r2_hidden(A_81,A_82)
      | k1_tarski(A_81) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_348,c_235])).

tff(c_368,plain,(
    ! [A_78] : k1_tarski(A_78) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_346,c_352])).

tff(c_50,plain,(
    ! [A_29,B_30] :
      ( r1_tarski(k1_tarski(A_29),B_30)
      | ~ r2_hidden(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_143,plain,(
    ! [A_47,B_48] :
      ( k4_xboole_0(A_47,B_48) = k1_xboole_0
      | ~ r1_tarski(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_383,plain,(
    ! [A_87,B_88] :
      ( k4_xboole_0(k1_tarski(A_87),B_88) = k1_xboole_0
      | ~ r2_hidden(A_87,B_88) ) ),
    inference(resolution,[status(thm)],[c_50,c_143])).

tff(c_410,plain,(
    ! [A_87] :
      ( k1_tarski(A_87) = k1_xboole_0
      | ~ r2_hidden(A_87,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_383,c_34])).

tff(c_434,plain,(
    ! [A_89] : ~ r2_hidden(A_89,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_368,c_410])).

tff(c_507,plain,(
    ! [B_92] : r1_xboole_0(k1_xboole_0,B_92) ),
    inference(resolution,[status(thm)],[c_26,c_434])).

tff(c_38,plain,(
    ! [A_21,B_22] :
      ( k4_xboole_0(A_21,B_22) = A_21
      | ~ r1_xboole_0(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_515,plain,(
    ! [B_93] : k4_xboole_0(k1_xboole_0,B_93) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_507,c_38])).

tff(c_36,plain,(
    ! [A_19,B_20] : k4_xboole_0(A_19,k4_xboole_0(A_19,B_20)) = k3_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_528,plain,(
    ! [B_93] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k3_xboole_0(k1_xboole_0,B_93) ),
    inference(superposition,[status(thm),theory(equality)],[c_515,c_36])).

tff(c_572,plain,(
    ! [B_94] : k3_xboole_0(k1_xboole_0,B_94) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_528])).

tff(c_590,plain,(
    ! [A_1] : k3_xboole_0(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_572])).

tff(c_253,plain,(
    ! [A_71,B_72] : k4_xboole_0(A_71,k4_xboole_0(A_71,B_72)) = k3_xboole_0(A_71,B_72) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_274,plain,(
    ! [A_18] : k4_xboole_0(A_18,A_18) = k3_xboole_0(A_18,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_253])).

tff(c_625,plain,(
    ! [A_18] : k4_xboole_0(A_18,A_18) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_590,c_274])).

tff(c_40,plain,(
    ! [A_21,B_22] :
      ( r1_xboole_0(A_21,B_22)
      | k4_xboole_0(A_21,B_22) != A_21 ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_277,plain,(
    ! [A_73,B_74,C_75] :
      ( ~ r1_xboole_0(A_73,B_74)
      | ~ r2_hidden(C_75,B_74)
      | ~ r2_hidden(C_75,A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1892,plain,(
    ! [C_152,B_153,A_154] :
      ( ~ r2_hidden(C_152,B_153)
      | ~ r2_hidden(C_152,A_154)
      | k4_xboole_0(A_154,B_153) != A_154 ) ),
    inference(resolution,[status(thm)],[c_40,c_277])).

tff(c_34032,plain,(
    ! [A_636,B_637,A_638] :
      ( ~ r2_hidden('#skF_3'(A_636,B_637),A_638)
      | k4_xboole_0(A_638,A_636) != A_638
      | r1_xboole_0(A_636,B_637) ) ),
    inference(resolution,[status(thm)],[c_26,c_1892])).

tff(c_34102,plain,(
    ! [A_9,B_10] :
      ( k4_xboole_0(A_9,A_9) != A_9
      | r1_xboole_0(A_9,B_10) ) ),
    inference(resolution,[status(thm)],[c_26,c_34032])).

tff(c_34123,plain,(
    ! [A_639,B_640] :
      ( k1_xboole_0 != A_639
      | r1_xboole_0(A_639,B_640) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_625,c_34102])).

tff(c_34138,plain,(
    ! [A_641,B_642] :
      ( k4_xboole_0(A_641,B_642) = A_641
      | k1_xboole_0 != A_641 ) ),
    inference(resolution,[status(thm)],[c_34123,c_38])).

tff(c_24,plain,(
    ! [A_9,B_10] :
      ( r2_hidden('#skF_3'(A_9,B_10),B_10)
      | r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_3345,plain,(
    ! [A_191,A_192,B_193] :
      ( ~ r2_hidden('#skF_3'(A_191,k4_xboole_0(A_192,B_193)),B_193)
      | r1_xboole_0(A_191,k4_xboole_0(A_192,B_193)) ) ),
    inference(resolution,[status(thm)],[c_24,c_220])).

tff(c_3395,plain,(
    ! [A_194,A_195] : r1_xboole_0(A_194,k4_xboole_0(A_195,A_194)) ),
    inference(resolution,[status(thm)],[c_26,c_3345])).

tff(c_3439,plain,(
    ! [A_194,A_195] : k4_xboole_0(A_194,k4_xboole_0(A_195,A_194)) = A_194 ),
    inference(resolution,[status(thm)],[c_3395,c_38])).

tff(c_36599,plain,(
    ! [B_642] : k4_xboole_0(B_642,k1_xboole_0) = B_642 ),
    inference(superposition,[status(thm),theory(equality)],[c_34138,c_3439])).

tff(c_709,plain,(
    ! [A_100] : k4_xboole_0(A_100,A_100) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_590,c_274])).

tff(c_172,plain,(
    ! [A_29,B_56] :
      ( r2_hidden(A_29,B_56)
      | k4_xboole_0(k1_tarski(A_29),B_56) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_164,c_48])).

tff(c_774,plain,(
    ! [A_29] : r2_hidden(A_29,k1_tarski(A_29)) ),
    inference(superposition,[status(thm),theory(equality)],[c_709,c_172])).

tff(c_593,plain,(
    ! [D_95,A_96,B_97] :
      ( r2_hidden(D_95,k4_xboole_0(A_96,B_97))
      | r2_hidden(D_95,B_97)
      | ~ r2_hidden(D_95,A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_5251,plain,(
    ! [D_245,A_246,B_247] :
      ( r2_hidden(D_245,k3_xboole_0(A_246,B_247))
      | r2_hidden(D_245,k4_xboole_0(A_246,B_247))
      | ~ r2_hidden(D_245,A_246) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_593])).

tff(c_56,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_430,plain,(
    ! [A_87] : ~ r2_hidden(A_87,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_368,c_410])).

tff(c_3447,plain,(
    ! [A_196,A_197] : k4_xboole_0(A_196,k4_xboole_0(A_197,A_196)) = A_196 ),
    inference(resolution,[status(thm)],[c_3395,c_38])).

tff(c_893,plain,(
    ! [A_109,B_110,C_111] :
      ( r2_hidden('#skF_1'(A_109,B_110,C_111),A_109)
      | r2_hidden('#skF_2'(A_109,B_110,C_111),C_111)
      | k4_xboole_0(A_109,B_110) = C_111 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_54,plain,(
    ! [C_34] :
      ( C_34 = '#skF_6'
      | ~ r2_hidden(C_34,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_983,plain,(
    ! [B_115,C_116] :
      ( '#skF_1'('#skF_5',B_115,C_116) = '#skF_6'
      | r2_hidden('#skF_2'('#skF_5',B_115,C_116),C_116)
      | k4_xboole_0('#skF_5',B_115) = C_116 ) ),
    inference(resolution,[status(thm)],[c_893,c_54])).

tff(c_1009,plain,(
    ! [B_115] :
      ( '#skF_1'('#skF_5',B_115,k1_xboole_0) = '#skF_6'
      | k4_xboole_0('#skF_5',B_115) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_983,c_430])).

tff(c_3498,plain,(
    ! [A_197] :
      ( '#skF_1'('#skF_5',k4_xboole_0(A_197,'#skF_5'),k1_xboole_0) = '#skF_6'
      | k1_xboole_0 = '#skF_5' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3447,c_1009])).

tff(c_3635,plain,(
    ! [A_198] : '#skF_1'('#skF_5',k4_xboole_0(A_198,'#skF_5'),k1_xboole_0) = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_3498])).

tff(c_18,plain,(
    ! [A_3,B_4,C_5] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4,C_5),B_4)
      | r2_hidden('#skF_2'(A_3,B_4,C_5),C_5)
      | k4_xboole_0(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_3656,plain,(
    ! [A_198] :
      ( ~ r2_hidden('#skF_6',k4_xboole_0(A_198,'#skF_5'))
      | r2_hidden('#skF_2'('#skF_5',k4_xboole_0(A_198,'#skF_5'),k1_xboole_0),k1_xboole_0)
      | k4_xboole_0('#skF_5',k4_xboole_0(A_198,'#skF_5')) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3635,c_18])).

tff(c_3704,plain,(
    ! [A_198] :
      ( ~ r2_hidden('#skF_6',k4_xboole_0(A_198,'#skF_5'))
      | r2_hidden('#skF_2'('#skF_5',k4_xboole_0(A_198,'#skF_5'),k1_xboole_0),k1_xboole_0)
      | k1_xboole_0 = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3439,c_3656])).

tff(c_3705,plain,(
    ! [A_198] : ~ r2_hidden('#skF_6',k4_xboole_0(A_198,'#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_430,c_3704])).

tff(c_5340,plain,(
    ! [A_246] :
      ( r2_hidden('#skF_6',k3_xboole_0(A_246,'#skF_5'))
      | ~ r2_hidden('#skF_6',A_246) ) ),
    inference(resolution,[status(thm)],[c_5251,c_3705])).

tff(c_8,plain,(
    ! [D_8,A_3,B_4] :
      ( r2_hidden(D_8,A_3)
      | ~ r2_hidden(D_8,k4_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_9150,plain,(
    ! [A_309,B_310,B_311,C_312] :
      ( r2_hidden('#skF_1'(k4_xboole_0(A_309,B_310),B_311,C_312),A_309)
      | r2_hidden('#skF_2'(k4_xboole_0(A_309,B_310),B_311,C_312),C_312)
      | k4_xboole_0(k4_xboole_0(A_309,B_310),B_311) = C_312 ) ),
    inference(resolution,[status(thm)],[c_893,c_8])).

tff(c_42037,plain,(
    ! [A_711,B_712,C_713] :
      ( r2_hidden('#skF_2'(k4_xboole_0(A_711,B_712),A_711,C_713),C_713)
      | k4_xboole_0(k4_xboole_0(A_711,B_712),A_711) = C_713 ) ),
    inference(resolution,[status(thm)],[c_9150,c_18])).

tff(c_42244,plain,(
    ! [A_711,B_712] : k4_xboole_0(k4_xboole_0(A_711,B_712),A_711) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42037,c_430])).

tff(c_20,plain,(
    ! [A_3,B_4,C_5] :
      ( r2_hidden('#skF_1'(A_3,B_4,C_5),A_3)
      | r2_hidden('#skF_2'(A_3,B_4,C_5),C_5)
      | k4_xboole_0(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1063,plain,(
    ! [A_120,B_121,C_122] :
      ( ~ r2_hidden('#skF_1'(A_120,B_121,C_122),C_122)
      | r2_hidden('#skF_2'(A_120,B_121,C_122),C_122)
      | k4_xboole_0(A_120,B_121) = C_122 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1072,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_2'(A_3,B_4,A_3),A_3)
      | k4_xboole_0(A_3,B_4) = A_3 ) ),
    inference(resolution,[status(thm)],[c_20,c_1063])).

tff(c_1475,plain,(
    ! [A_138,B_139,C_140] :
      ( r2_hidden('#skF_1'(A_138,B_139,C_140),A_138)
      | r2_hidden('#skF_2'(A_138,B_139,C_140),B_139)
      | ~ r2_hidden('#skF_2'(A_138,B_139,C_140),A_138)
      | k4_xboole_0(A_138,B_139) = C_140 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [A_3,B_4,C_5] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4,C_5),C_5)
      | r2_hidden('#skF_2'(A_3,B_4,C_5),B_4)
      | ~ r2_hidden('#skF_2'(A_3,B_4,C_5),A_3)
      | k4_xboole_0(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_5592,plain,(
    ! [A_255,B_256] :
      ( r2_hidden('#skF_2'(A_255,B_256,A_255),B_256)
      | ~ r2_hidden('#skF_2'(A_255,B_256,A_255),A_255)
      | k4_xboole_0(A_255,B_256) = A_255 ) ),
    inference(resolution,[status(thm)],[c_1475,c_10])).

tff(c_5620,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_2'(A_3,B_4,A_3),B_4)
      | k4_xboole_0(A_3,B_4) = A_3 ) ),
    inference(resolution,[status(thm)],[c_1072,c_5592])).

tff(c_2153,plain,(
    ! [A_163,B_164] :
      ( r2_hidden('#skF_2'(A_163,B_164,A_163),A_163)
      | k4_xboole_0(A_163,B_164) = A_163 ) ),
    inference(resolution,[status(thm)],[c_20,c_1063])).

tff(c_286,plain,(
    ! [C_75,B_22,A_21] :
      ( ~ r2_hidden(C_75,B_22)
      | ~ r2_hidden(C_75,A_21)
      | k4_xboole_0(A_21,B_22) != A_21 ) ),
    inference(resolution,[status(thm)],[c_40,c_277])).

tff(c_45052,plain,(
    ! [A_732,B_733,A_734] :
      ( ~ r2_hidden('#skF_2'(A_732,B_733,A_732),A_734)
      | k4_xboole_0(A_734,A_732) != A_734
      | k4_xboole_0(A_732,B_733) = A_732 ) ),
    inference(resolution,[status(thm)],[c_2153,c_286])).

tff(c_46049,plain,(
    ! [B_744,A_745] :
      ( k4_xboole_0(B_744,A_745) != B_744
      | k4_xboole_0(A_745,B_744) = A_745 ) ),
    inference(resolution,[status(thm)],[c_5620,c_45052])).

tff(c_46055,plain,(
    ! [A_711,B_712] :
      ( k4_xboole_0(A_711,B_712) != k1_xboole_0
      | k4_xboole_0(A_711,k4_xboole_0(A_711,B_712)) = A_711 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42244,c_46049])).

tff(c_46446,plain,(
    ! [A_749,B_750] :
      ( k4_xboole_0(A_749,B_750) != k1_xboole_0
      | k3_xboole_0(A_749,B_750) = A_749 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_46055])).

tff(c_46768,plain,(
    ! [A_753,B_754] : k3_xboole_0(k4_xboole_0(A_753,B_754),A_753) = k4_xboole_0(A_753,B_754) ),
    inference(superposition,[status(thm),theory(equality)],[c_42244,c_46446])).

tff(c_47128,plain,(
    ! [A_753,B_754] : k3_xboole_0(A_753,k4_xboole_0(A_753,B_754)) = k4_xboole_0(A_753,B_754) ),
    inference(superposition,[status(thm),theory(equality)],[c_46768,c_2])).

tff(c_147,plain,(
    ! [A_29,B_30] :
      ( k4_xboole_0(k1_tarski(A_29),B_30) = k1_xboole_0
      | ~ r2_hidden(A_29,B_30) ) ),
    inference(resolution,[status(thm)],[c_50,c_143])).

tff(c_2043,plain,(
    ! [A_161,B_162] : k4_xboole_0(A_161,k3_xboole_0(A_161,B_162)) = k3_xboole_0(A_161,k4_xboole_0(A_161,B_162)) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_253])).

tff(c_2136,plain,(
    ! [A_29,B_162] :
      ( k3_xboole_0(k1_tarski(A_29),k4_xboole_0(k1_tarski(A_29),B_162)) = k1_xboole_0
      | ~ r2_hidden(A_29,k3_xboole_0(k1_tarski(A_29),B_162)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_2043])).

tff(c_53733,plain,(
    ! [A_779,B_780] :
      ( k4_xboole_0(k1_tarski(A_779),B_780) = k1_xboole_0
      | ~ r2_hidden(A_779,k3_xboole_0(k1_tarski(A_779),B_780)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47128,c_2136])).

tff(c_53804,plain,
    ( k4_xboole_0(k1_tarski('#skF_6'),'#skF_5') = k1_xboole_0
    | ~ r2_hidden('#skF_6',k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_5340,c_53733])).

tff(c_53856,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),'#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_774,c_53804])).

tff(c_54236,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),k1_xboole_0) = k3_xboole_0(k1_tarski('#skF_6'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_53856,c_36])).

tff(c_54408,plain,(
    k3_xboole_0('#skF_5',k1_tarski('#skF_6')) = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36599,c_2,c_54236])).

tff(c_46108,plain,(
    ! [A_711,B_712] :
      ( k4_xboole_0(A_711,B_712) != k1_xboole_0
      | k3_xboole_0(A_711,B_712) = A_711 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_46055])).

tff(c_54272,plain,(
    k3_xboole_0(k1_tarski('#skF_6'),'#skF_5') = k1_tarski('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_53856,c_46108])).

tff(c_1373,plain,(
    ! [B_137] :
      ( '#skF_1'('#skF_5',B_137,k1_xboole_0) = '#skF_6'
      | k4_xboole_0('#skF_5',B_137) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_983,c_430])).

tff(c_1396,plain,(
    ! [B_137] :
      ( k4_xboole_0('#skF_5',k1_xboole_0) = k3_xboole_0('#skF_5',B_137)
      | '#skF_1'('#skF_5',B_137,k1_xboole_0) = '#skF_6' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1373,c_36])).

tff(c_1657,plain,(
    ! [B_144] :
      ( k3_xboole_0('#skF_5',B_144) = '#skF_5'
      | '#skF_1'('#skF_5',B_144,k1_xboole_0) = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1396])).

tff(c_1681,plain,(
    ! [B_144] :
      ( k3_xboole_0(B_144,'#skF_5') = '#skF_5'
      | '#skF_1'('#skF_5',B_144,k1_xboole_0) = '#skF_6' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1657,c_2])).

tff(c_54661,plain,
    ( k1_tarski('#skF_6') = '#skF_5'
    | '#skF_1'('#skF_5',k1_tarski('#skF_6'),k1_xboole_0) = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_54272,c_1681])).

tff(c_54790,plain,(
    '#skF_1'('#skF_5',k1_tarski('#skF_6'),k1_xboole_0) = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_54661])).

tff(c_55217,plain,
    ( ~ r2_hidden('#skF_6',k1_tarski('#skF_6'))
    | r2_hidden('#skF_2'('#skF_5',k1_tarski('#skF_6'),k1_xboole_0),k1_xboole_0)
    | k4_xboole_0('#skF_5',k1_tarski('#skF_6')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_54790,c_18])).

tff(c_55250,plain,
    ( r2_hidden('#skF_2'('#skF_5',k1_tarski('#skF_6'),k1_xboole_0),k1_xboole_0)
    | k4_xboole_0('#skF_5',k1_tarski('#skF_6')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_774,c_55217])).

tff(c_55251,plain,(
    k4_xboole_0('#skF_5',k1_tarski('#skF_6')) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_430,c_55250])).

tff(c_55649,plain,(
    k3_xboole_0('#skF_5',k1_tarski('#skF_6')) = k4_xboole_0('#skF_5',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_55251,c_36])).

tff(c_55821,plain,(
    k1_tarski('#skF_6') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36599,c_54408,c_55649])).

tff(c_55823,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_55821])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:35:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 15.68/8.57  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.75/8.59  
% 15.75/8.59  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.75/8.59  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_5 > #skF_6 > #skF_2
% 15.75/8.59  
% 15.75/8.59  %Foreground sorts:
% 15.75/8.59  
% 15.75/8.59  
% 15.75/8.59  %Background operators:
% 15.75/8.59  
% 15.75/8.59  
% 15.75/8.59  %Foreground operators:
% 15.75/8.59  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 15.75/8.59  tff('#skF_4', type, '#skF_4': $i > $i).
% 15.75/8.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 15.75/8.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 15.75/8.59  tff(k1_tarski, type, k1_tarski: $i > $i).
% 15.75/8.59  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 15.75/8.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 15.75/8.59  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 15.75/8.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 15.75/8.59  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 15.75/8.59  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 15.75/8.59  tff('#skF_5', type, '#skF_5': $i).
% 15.75/8.59  tff('#skF_6', type, '#skF_6': $i).
% 15.75/8.59  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 15.75/8.59  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 15.75/8.59  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 15.75/8.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 15.75/8.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 15.75/8.59  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 15.75/8.59  
% 15.75/8.62  tff(f_105, negated_conjecture, ~(![A, B]: ~((~(A = k1_tarski(B)) & ~(A = k1_xboole_0)) & (![C]: ~(r2_hidden(C, A) & ~(C = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_zfmisc_1)).
% 15.75/8.62  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 15.75/8.62  tff(f_69, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 15.75/8.62  tff(f_55, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 15.75/8.62  tff(f_67, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 15.75/8.62  tff(f_85, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 15.75/8.62  tff(f_37, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 15.75/8.62  tff(f_75, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 15.75/8.62  tff(f_71, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 15.75/8.62  tff(c_58, plain, (k1_tarski('#skF_6')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_105])).
% 15.75/8.62  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 15.75/8.62  tff(c_34, plain, (![A_18]: (k4_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_69])).
% 15.75/8.62  tff(c_26, plain, (![A_9, B_10]: (r2_hidden('#skF_3'(A_9, B_10), A_9) | r1_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_55])).
% 15.75/8.62  tff(c_164, plain, (![A_55, B_56]: (r1_tarski(A_55, B_56) | k4_xboole_0(A_55, B_56)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_67])).
% 15.75/8.62  tff(c_48, plain, (![A_29, B_30]: (r2_hidden(A_29, B_30) | ~r1_tarski(k1_tarski(A_29), B_30))), inference(cnfTransformation, [status(thm)], [f_85])).
% 15.75/8.62  tff(c_334, plain, (![A_78, B_79]: (r2_hidden(A_78, B_79) | k4_xboole_0(k1_tarski(A_78), B_79)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_164, c_48])).
% 15.75/8.62  tff(c_346, plain, (![A_78]: (r2_hidden(A_78, k1_xboole_0) | k1_tarski(A_78)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_34, c_334])).
% 15.75/8.62  tff(c_348, plain, (![A_80]: (r2_hidden(A_80, k1_xboole_0) | k1_tarski(A_80)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_34, c_334])).
% 15.75/8.62  tff(c_220, plain, (![D_66, B_67, A_68]: (~r2_hidden(D_66, B_67) | ~r2_hidden(D_66, k4_xboole_0(A_68, B_67)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 15.75/8.62  tff(c_235, plain, (![D_66, A_18]: (~r2_hidden(D_66, k1_xboole_0) | ~r2_hidden(D_66, A_18))), inference(superposition, [status(thm), theory('equality')], [c_34, c_220])).
% 15.75/8.62  tff(c_352, plain, (![A_81, A_82]: (~r2_hidden(A_81, A_82) | k1_tarski(A_81)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_348, c_235])).
% 15.75/8.62  tff(c_368, plain, (![A_78]: (k1_tarski(A_78)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_346, c_352])).
% 15.75/8.62  tff(c_50, plain, (![A_29, B_30]: (r1_tarski(k1_tarski(A_29), B_30) | ~r2_hidden(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_85])).
% 15.75/8.62  tff(c_143, plain, (![A_47, B_48]: (k4_xboole_0(A_47, B_48)=k1_xboole_0 | ~r1_tarski(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_67])).
% 15.75/8.62  tff(c_383, plain, (![A_87, B_88]: (k4_xboole_0(k1_tarski(A_87), B_88)=k1_xboole_0 | ~r2_hidden(A_87, B_88))), inference(resolution, [status(thm)], [c_50, c_143])).
% 15.75/8.62  tff(c_410, plain, (![A_87]: (k1_tarski(A_87)=k1_xboole_0 | ~r2_hidden(A_87, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_383, c_34])).
% 15.75/8.62  tff(c_434, plain, (![A_89]: (~r2_hidden(A_89, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_368, c_410])).
% 15.75/8.62  tff(c_507, plain, (![B_92]: (r1_xboole_0(k1_xboole_0, B_92))), inference(resolution, [status(thm)], [c_26, c_434])).
% 15.75/8.62  tff(c_38, plain, (![A_21, B_22]: (k4_xboole_0(A_21, B_22)=A_21 | ~r1_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_75])).
% 15.75/8.62  tff(c_515, plain, (![B_93]: (k4_xboole_0(k1_xboole_0, B_93)=k1_xboole_0)), inference(resolution, [status(thm)], [c_507, c_38])).
% 15.75/8.62  tff(c_36, plain, (![A_19, B_20]: (k4_xboole_0(A_19, k4_xboole_0(A_19, B_20))=k3_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_71])).
% 15.75/8.62  tff(c_528, plain, (![B_93]: (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k3_xboole_0(k1_xboole_0, B_93))), inference(superposition, [status(thm), theory('equality')], [c_515, c_36])).
% 15.75/8.62  tff(c_572, plain, (![B_94]: (k3_xboole_0(k1_xboole_0, B_94)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_528])).
% 15.75/8.62  tff(c_590, plain, (![A_1]: (k3_xboole_0(A_1, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_572])).
% 15.75/8.62  tff(c_253, plain, (![A_71, B_72]: (k4_xboole_0(A_71, k4_xboole_0(A_71, B_72))=k3_xboole_0(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_71])).
% 15.75/8.62  tff(c_274, plain, (![A_18]: (k4_xboole_0(A_18, A_18)=k3_xboole_0(A_18, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_34, c_253])).
% 15.75/8.62  tff(c_625, plain, (![A_18]: (k4_xboole_0(A_18, A_18)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_590, c_274])).
% 15.75/8.62  tff(c_40, plain, (![A_21, B_22]: (r1_xboole_0(A_21, B_22) | k4_xboole_0(A_21, B_22)!=A_21)), inference(cnfTransformation, [status(thm)], [f_75])).
% 15.75/8.62  tff(c_277, plain, (![A_73, B_74, C_75]: (~r1_xboole_0(A_73, B_74) | ~r2_hidden(C_75, B_74) | ~r2_hidden(C_75, A_73))), inference(cnfTransformation, [status(thm)], [f_55])).
% 15.75/8.62  tff(c_1892, plain, (![C_152, B_153, A_154]: (~r2_hidden(C_152, B_153) | ~r2_hidden(C_152, A_154) | k4_xboole_0(A_154, B_153)!=A_154)), inference(resolution, [status(thm)], [c_40, c_277])).
% 15.75/8.62  tff(c_34032, plain, (![A_636, B_637, A_638]: (~r2_hidden('#skF_3'(A_636, B_637), A_638) | k4_xboole_0(A_638, A_636)!=A_638 | r1_xboole_0(A_636, B_637))), inference(resolution, [status(thm)], [c_26, c_1892])).
% 15.75/8.62  tff(c_34102, plain, (![A_9, B_10]: (k4_xboole_0(A_9, A_9)!=A_9 | r1_xboole_0(A_9, B_10))), inference(resolution, [status(thm)], [c_26, c_34032])).
% 15.75/8.62  tff(c_34123, plain, (![A_639, B_640]: (k1_xboole_0!=A_639 | r1_xboole_0(A_639, B_640))), inference(demodulation, [status(thm), theory('equality')], [c_625, c_34102])).
% 15.75/8.62  tff(c_34138, plain, (![A_641, B_642]: (k4_xboole_0(A_641, B_642)=A_641 | k1_xboole_0!=A_641)), inference(resolution, [status(thm)], [c_34123, c_38])).
% 15.75/8.62  tff(c_24, plain, (![A_9, B_10]: (r2_hidden('#skF_3'(A_9, B_10), B_10) | r1_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_55])).
% 15.75/8.62  tff(c_3345, plain, (![A_191, A_192, B_193]: (~r2_hidden('#skF_3'(A_191, k4_xboole_0(A_192, B_193)), B_193) | r1_xboole_0(A_191, k4_xboole_0(A_192, B_193)))), inference(resolution, [status(thm)], [c_24, c_220])).
% 15.75/8.62  tff(c_3395, plain, (![A_194, A_195]: (r1_xboole_0(A_194, k4_xboole_0(A_195, A_194)))), inference(resolution, [status(thm)], [c_26, c_3345])).
% 15.75/8.62  tff(c_3439, plain, (![A_194, A_195]: (k4_xboole_0(A_194, k4_xboole_0(A_195, A_194))=A_194)), inference(resolution, [status(thm)], [c_3395, c_38])).
% 15.75/8.62  tff(c_36599, plain, (![B_642]: (k4_xboole_0(B_642, k1_xboole_0)=B_642)), inference(superposition, [status(thm), theory('equality')], [c_34138, c_3439])).
% 15.75/8.62  tff(c_709, plain, (![A_100]: (k4_xboole_0(A_100, A_100)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_590, c_274])).
% 15.75/8.62  tff(c_172, plain, (![A_29, B_56]: (r2_hidden(A_29, B_56) | k4_xboole_0(k1_tarski(A_29), B_56)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_164, c_48])).
% 15.75/8.62  tff(c_774, plain, (![A_29]: (r2_hidden(A_29, k1_tarski(A_29)))), inference(superposition, [status(thm), theory('equality')], [c_709, c_172])).
% 15.75/8.62  tff(c_593, plain, (![D_95, A_96, B_97]: (r2_hidden(D_95, k4_xboole_0(A_96, B_97)) | r2_hidden(D_95, B_97) | ~r2_hidden(D_95, A_96))), inference(cnfTransformation, [status(thm)], [f_37])).
% 15.75/8.62  tff(c_5251, plain, (![D_245, A_246, B_247]: (r2_hidden(D_245, k3_xboole_0(A_246, B_247)) | r2_hidden(D_245, k4_xboole_0(A_246, B_247)) | ~r2_hidden(D_245, A_246))), inference(superposition, [status(thm), theory('equality')], [c_36, c_593])).
% 15.75/8.62  tff(c_56, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_105])).
% 15.75/8.62  tff(c_430, plain, (![A_87]: (~r2_hidden(A_87, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_368, c_410])).
% 15.75/8.62  tff(c_3447, plain, (![A_196, A_197]: (k4_xboole_0(A_196, k4_xboole_0(A_197, A_196))=A_196)), inference(resolution, [status(thm)], [c_3395, c_38])).
% 15.75/8.62  tff(c_893, plain, (![A_109, B_110, C_111]: (r2_hidden('#skF_1'(A_109, B_110, C_111), A_109) | r2_hidden('#skF_2'(A_109, B_110, C_111), C_111) | k4_xboole_0(A_109, B_110)=C_111)), inference(cnfTransformation, [status(thm)], [f_37])).
% 15.75/8.62  tff(c_54, plain, (![C_34]: (C_34='#skF_6' | ~r2_hidden(C_34, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_105])).
% 15.75/8.62  tff(c_983, plain, (![B_115, C_116]: ('#skF_1'('#skF_5', B_115, C_116)='#skF_6' | r2_hidden('#skF_2'('#skF_5', B_115, C_116), C_116) | k4_xboole_0('#skF_5', B_115)=C_116)), inference(resolution, [status(thm)], [c_893, c_54])).
% 15.75/8.62  tff(c_1009, plain, (![B_115]: ('#skF_1'('#skF_5', B_115, k1_xboole_0)='#skF_6' | k4_xboole_0('#skF_5', B_115)=k1_xboole_0)), inference(resolution, [status(thm)], [c_983, c_430])).
% 15.75/8.62  tff(c_3498, plain, (![A_197]: ('#skF_1'('#skF_5', k4_xboole_0(A_197, '#skF_5'), k1_xboole_0)='#skF_6' | k1_xboole_0='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_3447, c_1009])).
% 15.75/8.62  tff(c_3635, plain, (![A_198]: ('#skF_1'('#skF_5', k4_xboole_0(A_198, '#skF_5'), k1_xboole_0)='#skF_6')), inference(negUnitSimplification, [status(thm)], [c_56, c_3498])).
% 15.75/8.62  tff(c_18, plain, (![A_3, B_4, C_5]: (~r2_hidden('#skF_1'(A_3, B_4, C_5), B_4) | r2_hidden('#skF_2'(A_3, B_4, C_5), C_5) | k4_xboole_0(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_37])).
% 15.75/8.62  tff(c_3656, plain, (![A_198]: (~r2_hidden('#skF_6', k4_xboole_0(A_198, '#skF_5')) | r2_hidden('#skF_2'('#skF_5', k4_xboole_0(A_198, '#skF_5'), k1_xboole_0), k1_xboole_0) | k4_xboole_0('#skF_5', k4_xboole_0(A_198, '#skF_5'))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3635, c_18])).
% 15.75/8.62  tff(c_3704, plain, (![A_198]: (~r2_hidden('#skF_6', k4_xboole_0(A_198, '#skF_5')) | r2_hidden('#skF_2'('#skF_5', k4_xboole_0(A_198, '#skF_5'), k1_xboole_0), k1_xboole_0) | k1_xboole_0='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3439, c_3656])).
% 15.75/8.62  tff(c_3705, plain, (![A_198]: (~r2_hidden('#skF_6', k4_xboole_0(A_198, '#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_56, c_430, c_3704])).
% 15.75/8.62  tff(c_5340, plain, (![A_246]: (r2_hidden('#skF_6', k3_xboole_0(A_246, '#skF_5')) | ~r2_hidden('#skF_6', A_246))), inference(resolution, [status(thm)], [c_5251, c_3705])).
% 15.75/8.62  tff(c_8, plain, (![D_8, A_3, B_4]: (r2_hidden(D_8, A_3) | ~r2_hidden(D_8, k4_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 15.75/8.62  tff(c_9150, plain, (![A_309, B_310, B_311, C_312]: (r2_hidden('#skF_1'(k4_xboole_0(A_309, B_310), B_311, C_312), A_309) | r2_hidden('#skF_2'(k4_xboole_0(A_309, B_310), B_311, C_312), C_312) | k4_xboole_0(k4_xboole_0(A_309, B_310), B_311)=C_312)), inference(resolution, [status(thm)], [c_893, c_8])).
% 15.75/8.62  tff(c_42037, plain, (![A_711, B_712, C_713]: (r2_hidden('#skF_2'(k4_xboole_0(A_711, B_712), A_711, C_713), C_713) | k4_xboole_0(k4_xboole_0(A_711, B_712), A_711)=C_713)), inference(resolution, [status(thm)], [c_9150, c_18])).
% 15.75/8.62  tff(c_42244, plain, (![A_711, B_712]: (k4_xboole_0(k4_xboole_0(A_711, B_712), A_711)=k1_xboole_0)), inference(resolution, [status(thm)], [c_42037, c_430])).
% 15.75/8.62  tff(c_20, plain, (![A_3, B_4, C_5]: (r2_hidden('#skF_1'(A_3, B_4, C_5), A_3) | r2_hidden('#skF_2'(A_3, B_4, C_5), C_5) | k4_xboole_0(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_37])).
% 15.75/8.62  tff(c_1063, plain, (![A_120, B_121, C_122]: (~r2_hidden('#skF_1'(A_120, B_121, C_122), C_122) | r2_hidden('#skF_2'(A_120, B_121, C_122), C_122) | k4_xboole_0(A_120, B_121)=C_122)), inference(cnfTransformation, [status(thm)], [f_37])).
% 15.75/8.62  tff(c_1072, plain, (![A_3, B_4]: (r2_hidden('#skF_2'(A_3, B_4, A_3), A_3) | k4_xboole_0(A_3, B_4)=A_3)), inference(resolution, [status(thm)], [c_20, c_1063])).
% 15.75/8.62  tff(c_1475, plain, (![A_138, B_139, C_140]: (r2_hidden('#skF_1'(A_138, B_139, C_140), A_138) | r2_hidden('#skF_2'(A_138, B_139, C_140), B_139) | ~r2_hidden('#skF_2'(A_138, B_139, C_140), A_138) | k4_xboole_0(A_138, B_139)=C_140)), inference(cnfTransformation, [status(thm)], [f_37])).
% 15.75/8.62  tff(c_10, plain, (![A_3, B_4, C_5]: (~r2_hidden('#skF_1'(A_3, B_4, C_5), C_5) | r2_hidden('#skF_2'(A_3, B_4, C_5), B_4) | ~r2_hidden('#skF_2'(A_3, B_4, C_5), A_3) | k4_xboole_0(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_37])).
% 15.75/8.62  tff(c_5592, plain, (![A_255, B_256]: (r2_hidden('#skF_2'(A_255, B_256, A_255), B_256) | ~r2_hidden('#skF_2'(A_255, B_256, A_255), A_255) | k4_xboole_0(A_255, B_256)=A_255)), inference(resolution, [status(thm)], [c_1475, c_10])).
% 15.75/8.62  tff(c_5620, plain, (![A_3, B_4]: (r2_hidden('#skF_2'(A_3, B_4, A_3), B_4) | k4_xboole_0(A_3, B_4)=A_3)), inference(resolution, [status(thm)], [c_1072, c_5592])).
% 15.75/8.62  tff(c_2153, plain, (![A_163, B_164]: (r2_hidden('#skF_2'(A_163, B_164, A_163), A_163) | k4_xboole_0(A_163, B_164)=A_163)), inference(resolution, [status(thm)], [c_20, c_1063])).
% 15.75/8.62  tff(c_286, plain, (![C_75, B_22, A_21]: (~r2_hidden(C_75, B_22) | ~r2_hidden(C_75, A_21) | k4_xboole_0(A_21, B_22)!=A_21)), inference(resolution, [status(thm)], [c_40, c_277])).
% 15.75/8.62  tff(c_45052, plain, (![A_732, B_733, A_734]: (~r2_hidden('#skF_2'(A_732, B_733, A_732), A_734) | k4_xboole_0(A_734, A_732)!=A_734 | k4_xboole_0(A_732, B_733)=A_732)), inference(resolution, [status(thm)], [c_2153, c_286])).
% 15.75/8.62  tff(c_46049, plain, (![B_744, A_745]: (k4_xboole_0(B_744, A_745)!=B_744 | k4_xboole_0(A_745, B_744)=A_745)), inference(resolution, [status(thm)], [c_5620, c_45052])).
% 15.75/8.62  tff(c_46055, plain, (![A_711, B_712]: (k4_xboole_0(A_711, B_712)!=k1_xboole_0 | k4_xboole_0(A_711, k4_xboole_0(A_711, B_712))=A_711)), inference(superposition, [status(thm), theory('equality')], [c_42244, c_46049])).
% 15.75/8.62  tff(c_46446, plain, (![A_749, B_750]: (k4_xboole_0(A_749, B_750)!=k1_xboole_0 | k3_xboole_0(A_749, B_750)=A_749)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_46055])).
% 15.75/8.62  tff(c_46768, plain, (![A_753, B_754]: (k3_xboole_0(k4_xboole_0(A_753, B_754), A_753)=k4_xboole_0(A_753, B_754))), inference(superposition, [status(thm), theory('equality')], [c_42244, c_46446])).
% 15.75/8.62  tff(c_47128, plain, (![A_753, B_754]: (k3_xboole_0(A_753, k4_xboole_0(A_753, B_754))=k4_xboole_0(A_753, B_754))), inference(superposition, [status(thm), theory('equality')], [c_46768, c_2])).
% 15.75/8.62  tff(c_147, plain, (![A_29, B_30]: (k4_xboole_0(k1_tarski(A_29), B_30)=k1_xboole_0 | ~r2_hidden(A_29, B_30))), inference(resolution, [status(thm)], [c_50, c_143])).
% 15.75/8.62  tff(c_2043, plain, (![A_161, B_162]: (k4_xboole_0(A_161, k3_xboole_0(A_161, B_162))=k3_xboole_0(A_161, k4_xboole_0(A_161, B_162)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_253])).
% 15.75/8.62  tff(c_2136, plain, (![A_29, B_162]: (k3_xboole_0(k1_tarski(A_29), k4_xboole_0(k1_tarski(A_29), B_162))=k1_xboole_0 | ~r2_hidden(A_29, k3_xboole_0(k1_tarski(A_29), B_162)))), inference(superposition, [status(thm), theory('equality')], [c_147, c_2043])).
% 15.75/8.62  tff(c_53733, plain, (![A_779, B_780]: (k4_xboole_0(k1_tarski(A_779), B_780)=k1_xboole_0 | ~r2_hidden(A_779, k3_xboole_0(k1_tarski(A_779), B_780)))), inference(demodulation, [status(thm), theory('equality')], [c_47128, c_2136])).
% 15.75/8.62  tff(c_53804, plain, (k4_xboole_0(k1_tarski('#skF_6'), '#skF_5')=k1_xboole_0 | ~r2_hidden('#skF_6', k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_5340, c_53733])).
% 15.75/8.62  tff(c_53856, plain, (k4_xboole_0(k1_tarski('#skF_6'), '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_774, c_53804])).
% 15.75/8.62  tff(c_54236, plain, (k4_xboole_0(k1_tarski('#skF_6'), k1_xboole_0)=k3_xboole_0(k1_tarski('#skF_6'), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_53856, c_36])).
% 15.75/8.62  tff(c_54408, plain, (k3_xboole_0('#skF_5', k1_tarski('#skF_6'))=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_36599, c_2, c_54236])).
% 15.75/8.62  tff(c_46108, plain, (![A_711, B_712]: (k4_xboole_0(A_711, B_712)!=k1_xboole_0 | k3_xboole_0(A_711, B_712)=A_711)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_46055])).
% 15.75/8.62  tff(c_54272, plain, (k3_xboole_0(k1_tarski('#skF_6'), '#skF_5')=k1_tarski('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_53856, c_46108])).
% 15.75/8.62  tff(c_1373, plain, (![B_137]: ('#skF_1'('#skF_5', B_137, k1_xboole_0)='#skF_6' | k4_xboole_0('#skF_5', B_137)=k1_xboole_0)), inference(resolution, [status(thm)], [c_983, c_430])).
% 15.75/8.62  tff(c_1396, plain, (![B_137]: (k4_xboole_0('#skF_5', k1_xboole_0)=k3_xboole_0('#skF_5', B_137) | '#skF_1'('#skF_5', B_137, k1_xboole_0)='#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1373, c_36])).
% 15.75/8.62  tff(c_1657, plain, (![B_144]: (k3_xboole_0('#skF_5', B_144)='#skF_5' | '#skF_1'('#skF_5', B_144, k1_xboole_0)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1396])).
% 15.75/8.62  tff(c_1681, plain, (![B_144]: (k3_xboole_0(B_144, '#skF_5')='#skF_5' | '#skF_1'('#skF_5', B_144, k1_xboole_0)='#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1657, c_2])).
% 15.75/8.62  tff(c_54661, plain, (k1_tarski('#skF_6')='#skF_5' | '#skF_1'('#skF_5', k1_tarski('#skF_6'), k1_xboole_0)='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_54272, c_1681])).
% 15.75/8.62  tff(c_54790, plain, ('#skF_1'('#skF_5', k1_tarski('#skF_6'), k1_xboole_0)='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_58, c_54661])).
% 15.75/8.62  tff(c_55217, plain, (~r2_hidden('#skF_6', k1_tarski('#skF_6')) | r2_hidden('#skF_2'('#skF_5', k1_tarski('#skF_6'), k1_xboole_0), k1_xboole_0) | k4_xboole_0('#skF_5', k1_tarski('#skF_6'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_54790, c_18])).
% 15.75/8.62  tff(c_55250, plain, (r2_hidden('#skF_2'('#skF_5', k1_tarski('#skF_6'), k1_xboole_0), k1_xboole_0) | k4_xboole_0('#skF_5', k1_tarski('#skF_6'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_774, c_55217])).
% 15.75/8.62  tff(c_55251, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_430, c_55250])).
% 15.75/8.62  tff(c_55649, plain, (k3_xboole_0('#skF_5', k1_tarski('#skF_6'))=k4_xboole_0('#skF_5', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_55251, c_36])).
% 15.75/8.62  tff(c_55821, plain, (k1_tarski('#skF_6')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_36599, c_54408, c_55649])).
% 15.75/8.62  tff(c_55823, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_55821])).
% 15.75/8.62  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.75/8.62  
% 15.75/8.62  Inference rules
% 15.75/8.62  ----------------------
% 15.75/8.62  #Ref     : 1
% 15.75/8.62  #Sup     : 13930
% 15.75/8.62  #Fact    : 0
% 15.75/8.62  #Define  : 0
% 15.75/8.62  #Split   : 0
% 15.75/8.62  #Chain   : 0
% 15.75/8.62  #Close   : 0
% 15.75/8.62  
% 15.75/8.62  Ordering : KBO
% 15.75/8.62  
% 15.75/8.62  Simplification rules
% 15.75/8.62  ----------------------
% 15.75/8.62  #Subsume      : 3255
% 15.75/8.62  #Demod        : 10293
% 15.75/8.62  #Tautology    : 6346
% 15.75/8.62  #SimpNegUnit  : 675
% 15.75/8.62  #BackRed      : 15
% 15.75/8.62  
% 15.75/8.62  #Partial instantiations: 0
% 15.75/8.62  #Strategies tried      : 1
% 15.75/8.62  
% 15.75/8.62  Timing (in seconds)
% 15.75/8.62  ----------------------
% 15.75/8.62  Preprocessing        : 0.32
% 15.75/8.62  Parsing              : 0.17
% 15.75/8.62  CNF conversion       : 0.02
% 15.75/8.62  Main loop            : 7.50
% 15.75/8.62  Inferencing          : 1.28
% 15.75/8.62  Reduction            : 3.71
% 15.75/8.62  Demodulation         : 3.04
% 15.75/8.62  BG Simplification    : 0.14
% 15.75/8.62  Subsumption          : 1.99
% 15.75/8.62  Abstraction          : 0.21
% 15.75/8.62  MUC search           : 0.00
% 15.75/8.62  Cooper               : 0.00
% 15.75/8.62  Total                : 7.88
% 15.75/8.62  Index Insertion      : 0.00
% 15.75/8.62  Index Deletion       : 0.00
% 15.75/8.62  Index Matching       : 0.00
% 15.75/8.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
