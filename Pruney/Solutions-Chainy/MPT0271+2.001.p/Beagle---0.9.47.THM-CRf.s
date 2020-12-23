%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:01 EST 2020

% Result     : Theorem 6.76s
% Output     : CNFRefutation 6.90s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 217 expanded)
%              Number of leaves         :   40 (  90 expanded)
%              Depth                    :   12
%              Number of atoms          :  119 ( 229 expanded)
%              Number of equality atoms :   78 ( 167 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1

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

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_107,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
      <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_57,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_61,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_59,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_51,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_55,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_100,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_98,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(c_92,plain,
    ( r2_hidden('#skF_4','#skF_5')
    | ~ r2_hidden('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_194,plain,(
    ~ r2_hidden('#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_92])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_197,plain,(
    ! [B_90,A_91] : k5_xboole_0(B_90,A_91) = k5_xboole_0(A_91,B_90) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_34,plain,(
    ! [A_22] : k5_xboole_0(A_22,k1_xboole_0) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_213,plain,(
    ! [A_91] : k5_xboole_0(k1_xboole_0,A_91) = A_91 ),
    inference(superposition,[status(thm),theory(equality)],[c_197,c_34])).

tff(c_38,plain,(
    ! [A_26] : k5_xboole_0(A_26,A_26) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_920,plain,(
    ! [A_144,B_145,C_146] : k5_xboole_0(k5_xboole_0(A_144,B_145),C_146) = k5_xboole_0(A_144,k5_xboole_0(B_145,C_146)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_977,plain,(
    ! [A_26,C_146] : k5_xboole_0(A_26,k5_xboole_0(A_26,C_146)) = k5_xboole_0(k1_xboole_0,C_146) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_920])).

tff(c_998,plain,(
    ! [A_147,C_148] : k5_xboole_0(A_147,k5_xboole_0(A_147,C_148)) = C_148 ),
    inference(demodulation,[status(thm),theory(equality)],[c_213,c_977])).

tff(c_1063,plain,(
    ! [A_149,B_150] : k5_xboole_0(A_149,k5_xboole_0(B_150,A_149)) = B_150 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_998])).

tff(c_1041,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k5_xboole_0(B_2,A_1)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_998])).

tff(c_1066,plain,(
    ! [B_150,A_149] : k5_xboole_0(k5_xboole_0(B_150,A_149),B_150) = A_149 ),
    inference(superposition,[status(thm),theory(equality)],[c_1063,c_1041])).

tff(c_28,plain,(
    ! [A_17] : k2_xboole_0(A_17,k1_xboole_0) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_96,plain,
    ( r2_hidden('#skF_4','#skF_5')
    | k4_xboole_0(k1_tarski('#skF_6'),'#skF_7') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_402,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),'#skF_7') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_96])).

tff(c_710,plain,(
    ! [A_129,B_130] : k2_xboole_0(A_129,k4_xboole_0(B_130,A_129)) = k2_xboole_0(A_129,B_130) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_738,plain,(
    k2_xboole_0('#skF_7',k1_tarski('#skF_6')) = k2_xboole_0('#skF_7',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_402,c_710])).

tff(c_749,plain,(
    k2_xboole_0('#skF_7',k1_tarski('#skF_6')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_738])).

tff(c_1239,plain,(
    ! [A_153,B_154] : k5_xboole_0(k5_xboole_0(A_153,B_154),k2_xboole_0(A_153,B_154)) = k3_xboole_0(A_153,B_154) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1294,plain,(
    k5_xboole_0(k5_xboole_0('#skF_7',k1_tarski('#skF_6')),'#skF_7') = k3_xboole_0('#skF_7',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_749,c_1239])).

tff(c_1349,plain,(
    k3_xboole_0('#skF_7',k1_tarski('#skF_6')) = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1066,c_1294])).

tff(c_24,plain,(
    ! [A_13,B_14] : k5_xboole_0(A_13,k3_xboole_0(A_13,B_14)) = k4_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1031,plain,(
    ! [A_13,B_14] : k5_xboole_0(A_13,k4_xboole_0(A_13,B_14)) = k3_xboole_0(A_13,B_14) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_998])).

tff(c_42,plain,(
    ! [B_30,A_29] : k2_tarski(B_30,A_29) = k2_tarski(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_346,plain,(
    ! [A_102,B_103] : k3_tarski(k2_tarski(A_102,B_103)) = k2_xboole_0(A_102,B_103) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_569,plain,(
    ! [B_123,A_124] : k3_tarski(k2_tarski(B_123,A_124)) = k2_xboole_0(A_124,B_123) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_346])).

tff(c_86,plain,(
    ! [A_68,B_69] : k3_tarski(k2_tarski(A_68,B_69)) = k2_xboole_0(A_68,B_69) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_596,plain,(
    ! [B_125,A_126] : k2_xboole_0(B_125,A_126) = k2_xboole_0(A_126,B_125) ),
    inference(superposition,[status(thm),theory(equality)],[c_569,c_86])).

tff(c_30,plain,(
    ! [A_18,B_19] : r1_tarski(k4_xboole_0(A_18,B_19),A_18) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_291,plain,(
    ! [A_93,B_94] :
      ( k2_xboole_0(A_93,B_94) = B_94
      | ~ r1_tarski(A_93,B_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_295,plain,(
    ! [A_18,B_19] : k2_xboole_0(k4_xboole_0(A_18,B_19),A_18) = A_18 ),
    inference(resolution,[status(thm)],[c_30,c_291])).

tff(c_620,plain,(
    ! [B_125,B_19] : k2_xboole_0(B_125,k4_xboole_0(B_125,B_19)) = B_125 ),
    inference(superposition,[status(thm),theory(equality)],[c_596,c_295])).

tff(c_1709,plain,(
    ! [A_168,B_169] : k5_xboole_0(A_168,k4_xboole_0(A_168,B_169)) = k3_xboole_0(A_168,B_169) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_998])).

tff(c_40,plain,(
    ! [A_27,B_28] : k5_xboole_0(k5_xboole_0(A_27,B_28),k2_xboole_0(A_27,B_28)) = k3_xboole_0(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1721,plain,(
    ! [A_168,B_169] : k5_xboole_0(k3_xboole_0(A_168,B_169),k2_xboole_0(A_168,k4_xboole_0(A_168,B_169))) = k3_xboole_0(A_168,k4_xboole_0(A_168,B_169)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1709,c_40])).

tff(c_2001,plain,(
    ! [A_177,B_178] : k3_xboole_0(A_177,k4_xboole_0(A_177,B_178)) = k4_xboole_0(A_177,B_178) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_2,c_620,c_1721])).

tff(c_2014,plain,(
    ! [A_177,B_178] : k5_xboole_0(A_177,k4_xboole_0(A_177,B_178)) = k4_xboole_0(A_177,k4_xboole_0(A_177,B_178)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2001,c_24])).

tff(c_2267,plain,(
    ! [A_187,B_188] : k4_xboole_0(A_187,k4_xboole_0(A_187,B_188)) = k3_xboole_0(A_187,B_188) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1031,c_2014])).

tff(c_2384,plain,(
    ! [A_189,B_190] : r1_tarski(k3_xboole_0(A_189,B_190),A_189) ),
    inference(superposition,[status(thm),theory(equality)],[c_2267,c_30])).

tff(c_2399,plain,(
    r1_tarski(k1_tarski('#skF_6'),'#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_1349,c_2384])).

tff(c_82,plain,(
    ! [A_66,B_67] :
      ( r2_hidden(A_66,B_67)
      | ~ r1_tarski(k1_tarski(A_66),B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_2418,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_2399,c_82])).

tff(c_2425,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_194,c_2418])).

tff(c_2426,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_3019,plain,(
    ! [A_236,B_237,C_238] : k5_xboole_0(k5_xboole_0(A_236,B_237),C_238) = k5_xboole_0(A_236,k5_xboole_0(B_237,C_238)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_3076,plain,(
    ! [A_26,C_238] : k5_xboole_0(A_26,k5_xboole_0(A_26,C_238)) = k5_xboole_0(k1_xboole_0,C_238) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_3019])).

tff(c_3097,plain,(
    ! [A_239,C_240] : k5_xboole_0(A_239,k5_xboole_0(A_239,C_240)) = C_240 ),
    inference(demodulation,[status(thm),theory(equality)],[c_213,c_3076])).

tff(c_3140,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k5_xboole_0(B_2,A_1)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_3097])).

tff(c_336,plain,(
    ! [A_98,B_99] :
      ( r1_tarski(k1_tarski(A_98),B_99)
      | ~ r2_hidden(A_98,B_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_26,plain,(
    ! [A_15,B_16] :
      ( k2_xboole_0(A_15,B_16) = B_16
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_340,plain,(
    ! [A_98,B_99] :
      ( k2_xboole_0(k1_tarski(A_98),B_99) = B_99
      | ~ r2_hidden(A_98,B_99) ) ),
    inference(resolution,[status(thm)],[c_336,c_26])).

tff(c_3465,plain,(
    ! [A_249,B_250] : k5_xboole_0(k5_xboole_0(A_249,B_250),k2_xboole_0(A_249,B_250)) = k3_xboole_0(A_249,B_250) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_3526,plain,(
    ! [A_98,B_99] :
      ( k5_xboole_0(k5_xboole_0(k1_tarski(A_98),B_99),B_99) = k3_xboole_0(k1_tarski(A_98),B_99)
      | ~ r2_hidden(A_98,B_99) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_340,c_3465])).

tff(c_5772,plain,(
    ! [A_365,B_366] :
      ( k3_xboole_0(k1_tarski(A_365),B_366) = k1_tarski(A_365)
      | ~ r2_hidden(A_365,B_366) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3140,c_2,c_3526])).

tff(c_5835,plain,(
    ! [A_365,B_366] :
      ( k5_xboole_0(k1_tarski(A_365),k1_tarski(A_365)) = k4_xboole_0(k1_tarski(A_365),B_366)
      | ~ r2_hidden(A_365,B_366) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5772,c_24])).

tff(c_5882,plain,(
    ! [A_367,B_368] :
      ( k4_xboole_0(k1_tarski(A_367),B_368) = k1_xboole_0
      | ~ r2_hidden(A_367,B_368) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_5835])).

tff(c_2427,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),'#skF_7') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_94,plain,
    ( k4_xboole_0(k1_tarski('#skF_4'),'#skF_5') != k1_xboole_0
    | k4_xboole_0(k1_tarski('#skF_6'),'#skF_7') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_2489,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),'#skF_5') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_2427,c_94])).

tff(c_5945,plain,(
    ~ r2_hidden('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_5882,c_2489])).

tff(c_5996,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2426,c_5945])).

tff(c_5997,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_5999,plain,(
    ! [B_369,A_370] : k5_xboole_0(B_369,A_370) = k5_xboole_0(A_370,B_369) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6015,plain,(
    ! [A_370] : k5_xboole_0(k1_xboole_0,A_370) = A_370 ),
    inference(superposition,[status(thm),theory(equality)],[c_5999,c_34])).

tff(c_6825,plain,(
    ! [A_440,B_441,C_442] : k5_xboole_0(k5_xboole_0(A_440,B_441),C_442) = k5_xboole_0(A_440,k5_xboole_0(B_441,C_442)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_6882,plain,(
    ! [A_26,C_442] : k5_xboole_0(A_26,k5_xboole_0(A_26,C_442)) = k5_xboole_0(k1_xboole_0,C_442) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_6825])).

tff(c_6903,plain,(
    ! [A_443,C_444] : k5_xboole_0(A_443,k5_xboole_0(A_443,C_444)) = C_444 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6015,c_6882])).

tff(c_6946,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k5_xboole_0(B_2,A_1)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_6903])).

tff(c_84,plain,(
    ! [A_66,B_67] :
      ( r1_tarski(k1_tarski(A_66),B_67)
      | ~ r2_hidden(A_66,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_6106,plain,(
    ! [A_382,B_383] :
      ( k2_xboole_0(A_382,B_383) = B_383
      | ~ r1_tarski(A_382,B_383) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_6113,plain,(
    ! [A_66,B_67] :
      ( k2_xboole_0(k1_tarski(A_66),B_67) = B_67
      | ~ r2_hidden(A_66,B_67) ) ),
    inference(resolution,[status(thm)],[c_84,c_6106])).

tff(c_7271,plain,(
    ! [A_453,B_454] : k5_xboole_0(k5_xboole_0(A_453,B_454),k2_xboole_0(A_453,B_454)) = k3_xboole_0(A_453,B_454) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_7332,plain,(
    ! [A_66,B_67] :
      ( k5_xboole_0(k5_xboole_0(k1_tarski(A_66),B_67),B_67) = k3_xboole_0(k1_tarski(A_66),B_67)
      | ~ r2_hidden(A_66,B_67) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6113,c_7271])).

tff(c_9700,plain,(
    ! [A_577,B_578] :
      ( k3_xboole_0(k1_tarski(A_577),B_578) = k1_tarski(A_577)
      | ~ r2_hidden(A_577,B_578) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6946,c_2,c_7332])).

tff(c_9766,plain,(
    ! [A_577,B_578] :
      ( k5_xboole_0(k1_tarski(A_577),k1_tarski(A_577)) = k4_xboole_0(k1_tarski(A_577),B_578)
      | ~ r2_hidden(A_577,B_578) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9700,c_24])).

tff(c_9813,plain,(
    ! [A_579,B_580] :
      ( k4_xboole_0(k1_tarski(A_579),B_580) = k1_xboole_0
      | ~ r2_hidden(A_579,B_580) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_9766])).

tff(c_5998,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_90,plain,
    ( k4_xboole_0(k1_tarski('#skF_4'),'#skF_5') != k1_xboole_0
    | ~ r2_hidden('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_6095,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),'#skF_5') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_5998,c_90])).

tff(c_9886,plain,(
    ~ r2_hidden('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_9813,c_6095])).

tff(c_9931,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5997,c_9886])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:52:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.76/2.51  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.76/2.51  
% 6.76/2.51  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.76/2.52  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 6.76/2.52  
% 6.76/2.52  %Foreground sorts:
% 6.76/2.52  
% 6.76/2.52  
% 6.76/2.52  %Background operators:
% 6.76/2.52  
% 6.76/2.52  
% 6.76/2.52  %Foreground operators:
% 6.76/2.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.76/2.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.76/2.52  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.76/2.52  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.76/2.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.76/2.52  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.76/2.52  tff('#skF_7', type, '#skF_7': $i).
% 6.76/2.52  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.76/2.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.76/2.52  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.76/2.52  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.76/2.52  tff('#skF_5', type, '#skF_5': $i).
% 6.76/2.52  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 6.76/2.52  tff('#skF_6', type, '#skF_6': $i).
% 6.76/2.52  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.76/2.52  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.76/2.52  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.76/2.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.76/2.52  tff(k3_tarski, type, k3_tarski: $i > $i).
% 6.76/2.52  tff('#skF_4', type, '#skF_4': $i).
% 6.76/2.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.76/2.52  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.76/2.52  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 6.76/2.52  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.76/2.52  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.76/2.52  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.76/2.52  
% 6.90/2.54  tff(f_107, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_zfmisc_1)).
% 6.90/2.54  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 6.90/2.54  tff(f_57, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 6.90/2.54  tff(f_61, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 6.90/2.54  tff(f_59, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 6.90/2.54  tff(f_51, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 6.90/2.54  tff(f_55, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 6.90/2.54  tff(f_63, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 6.90/2.54  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 6.90/2.54  tff(f_65, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 6.90/2.54  tff(f_100, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 6.90/2.54  tff(f_53, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 6.90/2.54  tff(f_49, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 6.90/2.54  tff(f_98, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 6.90/2.54  tff(c_92, plain, (r2_hidden('#skF_4', '#skF_5') | ~r2_hidden('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_107])).
% 6.90/2.54  tff(c_194, plain, (~r2_hidden('#skF_6', '#skF_7')), inference(splitLeft, [status(thm)], [c_92])).
% 6.90/2.54  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.90/2.54  tff(c_197, plain, (![B_90, A_91]: (k5_xboole_0(B_90, A_91)=k5_xboole_0(A_91, B_90))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.90/2.54  tff(c_34, plain, (![A_22]: (k5_xboole_0(A_22, k1_xboole_0)=A_22)), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.90/2.54  tff(c_213, plain, (![A_91]: (k5_xboole_0(k1_xboole_0, A_91)=A_91)), inference(superposition, [status(thm), theory('equality')], [c_197, c_34])).
% 6.90/2.54  tff(c_38, plain, (![A_26]: (k5_xboole_0(A_26, A_26)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.90/2.54  tff(c_920, plain, (![A_144, B_145, C_146]: (k5_xboole_0(k5_xboole_0(A_144, B_145), C_146)=k5_xboole_0(A_144, k5_xboole_0(B_145, C_146)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.90/2.54  tff(c_977, plain, (![A_26, C_146]: (k5_xboole_0(A_26, k5_xboole_0(A_26, C_146))=k5_xboole_0(k1_xboole_0, C_146))), inference(superposition, [status(thm), theory('equality')], [c_38, c_920])).
% 6.90/2.54  tff(c_998, plain, (![A_147, C_148]: (k5_xboole_0(A_147, k5_xboole_0(A_147, C_148))=C_148)), inference(demodulation, [status(thm), theory('equality')], [c_213, c_977])).
% 6.90/2.54  tff(c_1063, plain, (![A_149, B_150]: (k5_xboole_0(A_149, k5_xboole_0(B_150, A_149))=B_150)), inference(superposition, [status(thm), theory('equality')], [c_2, c_998])).
% 6.90/2.54  tff(c_1041, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k5_xboole_0(B_2, A_1))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_998])).
% 6.90/2.54  tff(c_1066, plain, (![B_150, A_149]: (k5_xboole_0(k5_xboole_0(B_150, A_149), B_150)=A_149)), inference(superposition, [status(thm), theory('equality')], [c_1063, c_1041])).
% 6.90/2.54  tff(c_28, plain, (![A_17]: (k2_xboole_0(A_17, k1_xboole_0)=A_17)), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.90/2.54  tff(c_96, plain, (r2_hidden('#skF_4', '#skF_5') | k4_xboole_0(k1_tarski('#skF_6'), '#skF_7')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_107])).
% 6.90/2.54  tff(c_402, plain, (k4_xboole_0(k1_tarski('#skF_6'), '#skF_7')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_96])).
% 6.90/2.54  tff(c_710, plain, (![A_129, B_130]: (k2_xboole_0(A_129, k4_xboole_0(B_130, A_129))=k2_xboole_0(A_129, B_130))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.90/2.54  tff(c_738, plain, (k2_xboole_0('#skF_7', k1_tarski('#skF_6'))=k2_xboole_0('#skF_7', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_402, c_710])).
% 6.90/2.54  tff(c_749, plain, (k2_xboole_0('#skF_7', k1_tarski('#skF_6'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_738])).
% 6.90/2.54  tff(c_1239, plain, (![A_153, B_154]: (k5_xboole_0(k5_xboole_0(A_153, B_154), k2_xboole_0(A_153, B_154))=k3_xboole_0(A_153, B_154))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.90/2.54  tff(c_1294, plain, (k5_xboole_0(k5_xboole_0('#skF_7', k1_tarski('#skF_6')), '#skF_7')=k3_xboole_0('#skF_7', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_749, c_1239])).
% 6.90/2.54  tff(c_1349, plain, (k3_xboole_0('#skF_7', k1_tarski('#skF_6'))=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1066, c_1294])).
% 6.90/2.54  tff(c_24, plain, (![A_13, B_14]: (k5_xboole_0(A_13, k3_xboole_0(A_13, B_14))=k4_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.90/2.54  tff(c_1031, plain, (![A_13, B_14]: (k5_xboole_0(A_13, k4_xboole_0(A_13, B_14))=k3_xboole_0(A_13, B_14))), inference(superposition, [status(thm), theory('equality')], [c_24, c_998])).
% 6.90/2.54  tff(c_42, plain, (![B_30, A_29]: (k2_tarski(B_30, A_29)=k2_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.90/2.54  tff(c_346, plain, (![A_102, B_103]: (k3_tarski(k2_tarski(A_102, B_103))=k2_xboole_0(A_102, B_103))), inference(cnfTransformation, [status(thm)], [f_100])).
% 6.90/2.54  tff(c_569, plain, (![B_123, A_124]: (k3_tarski(k2_tarski(B_123, A_124))=k2_xboole_0(A_124, B_123))), inference(superposition, [status(thm), theory('equality')], [c_42, c_346])).
% 6.90/2.54  tff(c_86, plain, (![A_68, B_69]: (k3_tarski(k2_tarski(A_68, B_69))=k2_xboole_0(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_100])).
% 6.90/2.54  tff(c_596, plain, (![B_125, A_126]: (k2_xboole_0(B_125, A_126)=k2_xboole_0(A_126, B_125))), inference(superposition, [status(thm), theory('equality')], [c_569, c_86])).
% 6.90/2.54  tff(c_30, plain, (![A_18, B_19]: (r1_tarski(k4_xboole_0(A_18, B_19), A_18))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.90/2.54  tff(c_291, plain, (![A_93, B_94]: (k2_xboole_0(A_93, B_94)=B_94 | ~r1_tarski(A_93, B_94))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.90/2.54  tff(c_295, plain, (![A_18, B_19]: (k2_xboole_0(k4_xboole_0(A_18, B_19), A_18)=A_18)), inference(resolution, [status(thm)], [c_30, c_291])).
% 6.90/2.54  tff(c_620, plain, (![B_125, B_19]: (k2_xboole_0(B_125, k4_xboole_0(B_125, B_19))=B_125)), inference(superposition, [status(thm), theory('equality')], [c_596, c_295])).
% 6.90/2.54  tff(c_1709, plain, (![A_168, B_169]: (k5_xboole_0(A_168, k4_xboole_0(A_168, B_169))=k3_xboole_0(A_168, B_169))), inference(superposition, [status(thm), theory('equality')], [c_24, c_998])).
% 6.90/2.54  tff(c_40, plain, (![A_27, B_28]: (k5_xboole_0(k5_xboole_0(A_27, B_28), k2_xboole_0(A_27, B_28))=k3_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.90/2.54  tff(c_1721, plain, (![A_168, B_169]: (k5_xboole_0(k3_xboole_0(A_168, B_169), k2_xboole_0(A_168, k4_xboole_0(A_168, B_169)))=k3_xboole_0(A_168, k4_xboole_0(A_168, B_169)))), inference(superposition, [status(thm), theory('equality')], [c_1709, c_40])).
% 6.90/2.54  tff(c_2001, plain, (![A_177, B_178]: (k3_xboole_0(A_177, k4_xboole_0(A_177, B_178))=k4_xboole_0(A_177, B_178))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_2, c_620, c_1721])).
% 6.90/2.54  tff(c_2014, plain, (![A_177, B_178]: (k5_xboole_0(A_177, k4_xboole_0(A_177, B_178))=k4_xboole_0(A_177, k4_xboole_0(A_177, B_178)))), inference(superposition, [status(thm), theory('equality')], [c_2001, c_24])).
% 6.90/2.54  tff(c_2267, plain, (![A_187, B_188]: (k4_xboole_0(A_187, k4_xboole_0(A_187, B_188))=k3_xboole_0(A_187, B_188))), inference(demodulation, [status(thm), theory('equality')], [c_1031, c_2014])).
% 6.90/2.54  tff(c_2384, plain, (![A_189, B_190]: (r1_tarski(k3_xboole_0(A_189, B_190), A_189))), inference(superposition, [status(thm), theory('equality')], [c_2267, c_30])).
% 6.90/2.54  tff(c_2399, plain, (r1_tarski(k1_tarski('#skF_6'), '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_1349, c_2384])).
% 6.90/2.54  tff(c_82, plain, (![A_66, B_67]: (r2_hidden(A_66, B_67) | ~r1_tarski(k1_tarski(A_66), B_67))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.90/2.54  tff(c_2418, plain, (r2_hidden('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_2399, c_82])).
% 6.90/2.54  tff(c_2425, plain, $false, inference(negUnitSimplification, [status(thm)], [c_194, c_2418])).
% 6.90/2.54  tff(c_2426, plain, (r2_hidden('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_96])).
% 6.90/2.54  tff(c_3019, plain, (![A_236, B_237, C_238]: (k5_xboole_0(k5_xboole_0(A_236, B_237), C_238)=k5_xboole_0(A_236, k5_xboole_0(B_237, C_238)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.90/2.54  tff(c_3076, plain, (![A_26, C_238]: (k5_xboole_0(A_26, k5_xboole_0(A_26, C_238))=k5_xboole_0(k1_xboole_0, C_238))), inference(superposition, [status(thm), theory('equality')], [c_38, c_3019])).
% 6.90/2.54  tff(c_3097, plain, (![A_239, C_240]: (k5_xboole_0(A_239, k5_xboole_0(A_239, C_240))=C_240)), inference(demodulation, [status(thm), theory('equality')], [c_213, c_3076])).
% 6.90/2.54  tff(c_3140, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k5_xboole_0(B_2, A_1))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_3097])).
% 6.90/2.54  tff(c_336, plain, (![A_98, B_99]: (r1_tarski(k1_tarski(A_98), B_99) | ~r2_hidden(A_98, B_99))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.90/2.54  tff(c_26, plain, (![A_15, B_16]: (k2_xboole_0(A_15, B_16)=B_16 | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.90/2.54  tff(c_340, plain, (![A_98, B_99]: (k2_xboole_0(k1_tarski(A_98), B_99)=B_99 | ~r2_hidden(A_98, B_99))), inference(resolution, [status(thm)], [c_336, c_26])).
% 6.90/2.54  tff(c_3465, plain, (![A_249, B_250]: (k5_xboole_0(k5_xboole_0(A_249, B_250), k2_xboole_0(A_249, B_250))=k3_xboole_0(A_249, B_250))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.90/2.54  tff(c_3526, plain, (![A_98, B_99]: (k5_xboole_0(k5_xboole_0(k1_tarski(A_98), B_99), B_99)=k3_xboole_0(k1_tarski(A_98), B_99) | ~r2_hidden(A_98, B_99))), inference(superposition, [status(thm), theory('equality')], [c_340, c_3465])).
% 6.90/2.54  tff(c_5772, plain, (![A_365, B_366]: (k3_xboole_0(k1_tarski(A_365), B_366)=k1_tarski(A_365) | ~r2_hidden(A_365, B_366))), inference(demodulation, [status(thm), theory('equality')], [c_3140, c_2, c_3526])).
% 6.90/2.54  tff(c_5835, plain, (![A_365, B_366]: (k5_xboole_0(k1_tarski(A_365), k1_tarski(A_365))=k4_xboole_0(k1_tarski(A_365), B_366) | ~r2_hidden(A_365, B_366))), inference(superposition, [status(thm), theory('equality')], [c_5772, c_24])).
% 6.90/2.54  tff(c_5882, plain, (![A_367, B_368]: (k4_xboole_0(k1_tarski(A_367), B_368)=k1_xboole_0 | ~r2_hidden(A_367, B_368))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_5835])).
% 6.90/2.54  tff(c_2427, plain, (k4_xboole_0(k1_tarski('#skF_6'), '#skF_7')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_96])).
% 6.90/2.54  tff(c_94, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_5')!=k1_xboole_0 | k4_xboole_0(k1_tarski('#skF_6'), '#skF_7')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_107])).
% 6.90/2.54  tff(c_2489, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_5')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_2427, c_94])).
% 6.90/2.54  tff(c_5945, plain, (~r2_hidden('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_5882, c_2489])).
% 6.90/2.54  tff(c_5996, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2426, c_5945])).
% 6.90/2.54  tff(c_5997, plain, (r2_hidden('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_92])).
% 6.90/2.54  tff(c_5999, plain, (![B_369, A_370]: (k5_xboole_0(B_369, A_370)=k5_xboole_0(A_370, B_369))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.90/2.54  tff(c_6015, plain, (![A_370]: (k5_xboole_0(k1_xboole_0, A_370)=A_370)), inference(superposition, [status(thm), theory('equality')], [c_5999, c_34])).
% 6.90/2.54  tff(c_6825, plain, (![A_440, B_441, C_442]: (k5_xboole_0(k5_xboole_0(A_440, B_441), C_442)=k5_xboole_0(A_440, k5_xboole_0(B_441, C_442)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.90/2.54  tff(c_6882, plain, (![A_26, C_442]: (k5_xboole_0(A_26, k5_xboole_0(A_26, C_442))=k5_xboole_0(k1_xboole_0, C_442))), inference(superposition, [status(thm), theory('equality')], [c_38, c_6825])).
% 6.90/2.54  tff(c_6903, plain, (![A_443, C_444]: (k5_xboole_0(A_443, k5_xboole_0(A_443, C_444))=C_444)), inference(demodulation, [status(thm), theory('equality')], [c_6015, c_6882])).
% 6.90/2.54  tff(c_6946, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k5_xboole_0(B_2, A_1))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_6903])).
% 6.90/2.54  tff(c_84, plain, (![A_66, B_67]: (r1_tarski(k1_tarski(A_66), B_67) | ~r2_hidden(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.90/2.54  tff(c_6106, plain, (![A_382, B_383]: (k2_xboole_0(A_382, B_383)=B_383 | ~r1_tarski(A_382, B_383))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.90/2.54  tff(c_6113, plain, (![A_66, B_67]: (k2_xboole_0(k1_tarski(A_66), B_67)=B_67 | ~r2_hidden(A_66, B_67))), inference(resolution, [status(thm)], [c_84, c_6106])).
% 6.90/2.54  tff(c_7271, plain, (![A_453, B_454]: (k5_xboole_0(k5_xboole_0(A_453, B_454), k2_xboole_0(A_453, B_454))=k3_xboole_0(A_453, B_454))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.90/2.54  tff(c_7332, plain, (![A_66, B_67]: (k5_xboole_0(k5_xboole_0(k1_tarski(A_66), B_67), B_67)=k3_xboole_0(k1_tarski(A_66), B_67) | ~r2_hidden(A_66, B_67))), inference(superposition, [status(thm), theory('equality')], [c_6113, c_7271])).
% 6.90/2.54  tff(c_9700, plain, (![A_577, B_578]: (k3_xboole_0(k1_tarski(A_577), B_578)=k1_tarski(A_577) | ~r2_hidden(A_577, B_578))), inference(demodulation, [status(thm), theory('equality')], [c_6946, c_2, c_7332])).
% 6.90/2.54  tff(c_9766, plain, (![A_577, B_578]: (k5_xboole_0(k1_tarski(A_577), k1_tarski(A_577))=k4_xboole_0(k1_tarski(A_577), B_578) | ~r2_hidden(A_577, B_578))), inference(superposition, [status(thm), theory('equality')], [c_9700, c_24])).
% 6.90/2.54  tff(c_9813, plain, (![A_579, B_580]: (k4_xboole_0(k1_tarski(A_579), B_580)=k1_xboole_0 | ~r2_hidden(A_579, B_580))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_9766])).
% 6.90/2.54  tff(c_5998, plain, (r2_hidden('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_92])).
% 6.90/2.54  tff(c_90, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_5')!=k1_xboole_0 | ~r2_hidden('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_107])).
% 6.90/2.54  tff(c_6095, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_5')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_5998, c_90])).
% 6.90/2.54  tff(c_9886, plain, (~r2_hidden('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_9813, c_6095])).
% 6.90/2.54  tff(c_9931, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5997, c_9886])).
% 6.90/2.54  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.90/2.54  
% 6.90/2.54  Inference rules
% 6.90/2.54  ----------------------
% 6.90/2.54  #Ref     : 0
% 6.90/2.54  #Sup     : 2476
% 6.90/2.54  #Fact    : 0
% 6.90/2.54  #Define  : 0
% 6.90/2.54  #Split   : 6
% 6.90/2.54  #Chain   : 0
% 6.90/2.54  #Close   : 0
% 6.90/2.54  
% 6.90/2.54  Ordering : KBO
% 6.90/2.54  
% 6.90/2.54  Simplification rules
% 6.90/2.54  ----------------------
% 6.90/2.54  #Subsume      : 246
% 6.90/2.54  #Demod        : 1696
% 6.90/2.54  #Tautology    : 1484
% 6.90/2.54  #SimpNegUnit  : 6
% 6.90/2.54  #BackRed      : 0
% 6.90/2.54  
% 6.90/2.54  #Partial instantiations: 0
% 6.90/2.54  #Strategies tried      : 1
% 6.90/2.54  
% 6.90/2.54  Timing (in seconds)
% 6.90/2.54  ----------------------
% 6.90/2.54  Preprocessing        : 0.36
% 6.90/2.54  Parsing              : 0.18
% 6.90/2.54  CNF conversion       : 0.03
% 6.90/2.54  Main loop            : 1.40
% 6.90/2.54  Inferencing          : 0.44
% 6.90/2.54  Reduction            : 0.60
% 6.90/2.54  Demodulation         : 0.47
% 6.90/2.54  BG Simplification    : 0.05
% 6.90/2.54  Subsumption          : 0.21
% 6.90/2.54  Abstraction          : 0.07
% 6.90/2.54  MUC search           : 0.00
% 6.90/2.54  Cooper               : 0.00
% 6.90/2.54  Total                : 1.81
% 6.90/2.54  Index Insertion      : 0.00
% 6.90/2.54  Index Deletion       : 0.00
% 6.90/2.54  Index Matching       : 0.00
% 6.90/2.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
