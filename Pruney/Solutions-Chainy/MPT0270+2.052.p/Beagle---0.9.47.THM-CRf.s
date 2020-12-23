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
% DateTime   : Thu Dec  3 09:52:59 EST 2020

% Result     : Theorem 4.82s
% Output     : CNFRefutation 4.82s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 224 expanded)
%              Number of leaves         :   37 (  88 expanded)
%              Depth                    :   13
%              Number of atoms          :  109 ( 287 expanded)
%              Number of equality atoms :   61 ( 162 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_103,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
      <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_zfmisc_1)).

tff(f_67,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k1_tarski(A)
    <=> ( ~ r2_hidden(A,C)
        & ( r2_hidden(B,C)
          | A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l38_zfmisc_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k3_xboole_0(B,k1_tarski(A)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l31_zfmisc_1)).

tff(f_59,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_63,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_53,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_51,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_52,plain,
    ( ~ r2_hidden('#skF_3','#skF_4')
    | r2_hidden('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_87,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_24,plain,(
    ! [A_22] : k2_tarski(A_22,A_22) = k1_tarski(A_22) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_46,plain,(
    ! [B_55,C_56] :
      ( k4_xboole_0(k2_tarski(B_55,B_55),C_56) = k1_tarski(B_55)
      | r2_hidden(B_55,C_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_740,plain,(
    ! [B_108,C_109] :
      ( k4_xboole_0(k1_tarski(B_108),C_109) = k1_tarski(B_108)
      | r2_hidden(B_108,C_109) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_46])).

tff(c_50,plain,
    ( k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') != k1_tarski('#skF_3')
    | r2_hidden('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_240,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') != k1_tarski('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_779,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_740,c_240])).

tff(c_812,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_779])).

tff(c_813,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_1401,plain,(
    ! [B_138,A_139] :
      ( k3_xboole_0(B_138,k1_tarski(A_139)) = k1_tarski(A_139)
      | ~ r2_hidden(A_139,B_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_16,plain,(
    ! [A_16] : r1_tarski(k1_xboole_0,A_16) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_123,plain,(
    ! [A_68,B_69] :
      ( k3_xboole_0(A_68,B_69) = A_68
      | ~ r1_tarski(A_68,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_128,plain,(
    ! [A_70] : k3_xboole_0(k1_xboole_0,A_70) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_123])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_133,plain,(
    ! [A_70] : k3_xboole_0(A_70,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_2])).

tff(c_20,plain,(
    ! [A_19] : k5_xboole_0(A_19,k1_xboole_0) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_214,plain,(
    ! [A_74,B_75] : k5_xboole_0(A_74,k3_xboole_0(A_74,B_75)) = k4_xboole_0(A_74,B_75) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_223,plain,(
    ! [A_70] : k5_xboole_0(A_70,k1_xboole_0) = k4_xboole_0(A_70,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_214])).

tff(c_238,plain,(
    ! [A_70] : k4_xboole_0(A_70,k1_xboole_0) = A_70 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_223])).

tff(c_918,plain,(
    ! [A_117,B_118] : k4_xboole_0(A_117,k4_xboole_0(A_117,B_118)) = k3_xboole_0(A_117,B_118) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_943,plain,(
    ! [A_70] : k4_xboole_0(A_70,A_70) = k3_xboole_0(A_70,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_238,c_918])).

tff(c_958,plain,(
    ! [A_70] : k4_xboole_0(A_70,A_70) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_943])).

tff(c_814,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_tarski('#skF_3') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_54,plain,
    ( k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') != k1_tarski('#skF_3')
    | k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_826,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') != k1_tarski('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_858,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_814,c_826])).

tff(c_859,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') = k1_tarski('#skF_5') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_940,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_5')) = k3_xboole_0(k1_tarski('#skF_5'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_859,c_918])).

tff(c_957,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_5')) = k3_xboole_0('#skF_6',k1_tarski('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_940])).

tff(c_1045,plain,(
    k3_xboole_0('#skF_6',k1_tarski('#skF_5')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_958,c_957])).

tff(c_1414,plain,
    ( k1_tarski('#skF_5') = k1_xboole_0
    | ~ r2_hidden('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1401,c_1045])).

tff(c_1466,plain,(
    k1_tarski('#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_813,c_1414])).

tff(c_127,plain,(
    ! [A_16] : k3_xboole_0(k1_xboole_0,A_16) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_123])).

tff(c_226,plain,(
    ! [A_16] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_214])).

tff(c_239,plain,(
    ! [A_16] : k4_xboole_0(k1_xboole_0,A_16) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_226])).

tff(c_1820,plain,(
    ! [A_150,C_151,B_152] :
      ( ~ r2_hidden(A_150,C_151)
      | k4_xboole_0(k2_tarski(A_150,B_152),C_151) != k1_tarski(A_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_3788,plain,(
    ! [A_225,C_226] :
      ( ~ r2_hidden(A_225,C_226)
      | k4_xboole_0(k1_tarski(A_225),C_226) != k1_tarski(A_225) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1820])).

tff(c_3802,plain,(
    ! [C_226] :
      ( ~ r2_hidden('#skF_5',C_226)
      | k4_xboole_0(k1_xboole_0,C_226) != k1_tarski('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1466,c_3788])).

tff(c_3824,plain,(
    ! [C_226] : ~ r2_hidden('#skF_5',C_226) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1466,c_239,c_3802])).

tff(c_3829,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3824,c_813])).

tff(c_3830,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_4688,plain,(
    ! [B_274,A_275] :
      ( k3_xboole_0(B_274,k1_tarski(A_275)) = k1_tarski(A_275)
      | ~ r2_hidden(A_275,B_274) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_3831,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_56,plain,
    ( ~ r2_hidden('#skF_3','#skF_4')
    | k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_4040,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') = k1_tarski('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3831,c_56])).

tff(c_22,plain,(
    ! [A_20,B_21] : r1_xboole_0(k4_xboole_0(A_20,B_21),B_21) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_4044,plain,(
    r1_xboole_0(k1_tarski('#skF_5'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_4040,c_22])).

tff(c_10,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_2'(A_10),A_10)
      | k1_xboole_0 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_3985,plain,(
    ! [A_240,B_241,C_242] :
      ( ~ r1_xboole_0(A_240,B_241)
      | ~ r2_hidden(C_242,k3_xboole_0(A_240,B_241)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_4203,plain,(
    ! [A_256,B_257] :
      ( ~ r1_xboole_0(A_256,B_257)
      | k3_xboole_0(A_256,B_257) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_3985])).

tff(c_4223,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),'#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4044,c_4203])).

tff(c_4242,plain,(
    k3_xboole_0('#skF_6',k1_tarski('#skF_5')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4223,c_2])).

tff(c_4701,plain,
    ( k1_tarski('#skF_5') = k1_xboole_0
    | ~ r2_hidden('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_4688,c_4242])).

tff(c_4753,plain,(
    k1_tarski('#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3830,c_4701])).

tff(c_3867,plain,(
    ! [A_232,B_233] :
      ( k3_xboole_0(A_232,B_233) = A_232
      | ~ r1_tarski(A_232,B_233) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_3871,plain,(
    ! [A_16] : k3_xboole_0(k1_xboole_0,A_16) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_3867])).

tff(c_3959,plain,(
    ! [A_238,B_239] : k5_xboole_0(A_238,k3_xboole_0(A_238,B_239)) = k4_xboole_0(A_238,B_239) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_3971,plain,(
    ! [A_16] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_3871,c_3959])).

tff(c_3984,plain,(
    ! [A_16] : k4_xboole_0(k1_xboole_0,A_16) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_3971])).

tff(c_4851,plain,(
    ! [A_278,C_279,B_280] :
      ( ~ r2_hidden(A_278,C_279)
      | k4_xboole_0(k2_tarski(A_278,B_280),C_279) != k1_tarski(A_278) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_6613,plain,(
    ! [A_352,C_353] :
      ( ~ r2_hidden(A_352,C_353)
      | k4_xboole_0(k1_tarski(A_352),C_353) != k1_tarski(A_352) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_4851])).

tff(c_6623,plain,(
    ! [C_353] :
      ( ~ r2_hidden('#skF_5',C_353)
      | k4_xboole_0(k1_xboole_0,C_353) != k1_tarski('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4753,c_6613])).

tff(c_6645,plain,(
    ! [C_353] : ~ r2_hidden('#skF_5',C_353) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4753,c_3984,c_6623])).

tff(c_6650,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6645,c_3830])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:21:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.82/1.95  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.82/1.96  
% 4.82/1.96  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.82/1.96  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 4.82/1.96  
% 4.82/1.96  %Foreground sorts:
% 4.82/1.96  
% 4.82/1.96  
% 4.82/1.96  %Background operators:
% 4.82/1.96  
% 4.82/1.96  
% 4.82/1.96  %Foreground operators:
% 4.82/1.96  tff('#skF_2', type, '#skF_2': $i > $i).
% 4.82/1.96  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.82/1.96  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.82/1.96  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.82/1.96  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.82/1.96  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.82/1.96  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.82/1.96  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.82/1.96  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.82/1.96  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.82/1.96  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.82/1.96  tff('#skF_5', type, '#skF_5': $i).
% 4.82/1.96  tff('#skF_6', type, '#skF_6': $i).
% 4.82/1.96  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.82/1.96  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.82/1.96  tff('#skF_3', type, '#skF_3': $i).
% 4.82/1.96  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.82/1.96  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.82/1.96  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.82/1.96  tff('#skF_4', type, '#skF_4': $i).
% 4.82/1.96  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.82/1.96  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.82/1.96  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.82/1.96  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.82/1.96  
% 4.82/1.98  tff(f_103, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_zfmisc_1)).
% 4.82/1.98  tff(f_67, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 4.82/1.98  tff(f_97, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k1_tarski(A)) <=> (~r2_hidden(A, C) & (r2_hidden(B, C) | (A = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l38_zfmisc_1)).
% 4.82/1.98  tff(f_88, axiom, (![A, B]: (r2_hidden(A, B) => (k3_xboole_0(B, k1_tarski(A)) = k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l31_zfmisc_1)).
% 4.82/1.98  tff(f_59, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.82/1.98  tff(f_57, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.82/1.98  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.82/1.98  tff(f_63, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 4.82/1.98  tff(f_53, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.82/1.98  tff(f_61, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.82/1.98  tff(f_65, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 4.82/1.98  tff(f_51, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 4.82/1.98  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 4.82/1.98  tff(c_52, plain, (~r2_hidden('#skF_3', '#skF_4') | r2_hidden('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.82/1.98  tff(c_87, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_52])).
% 4.82/1.98  tff(c_24, plain, (![A_22]: (k2_tarski(A_22, A_22)=k1_tarski(A_22))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.82/1.98  tff(c_46, plain, (![B_55, C_56]: (k4_xboole_0(k2_tarski(B_55, B_55), C_56)=k1_tarski(B_55) | r2_hidden(B_55, C_56))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.82/1.98  tff(c_740, plain, (![B_108, C_109]: (k4_xboole_0(k1_tarski(B_108), C_109)=k1_tarski(B_108) | r2_hidden(B_108, C_109))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_46])).
% 4.82/1.98  tff(c_50, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')!=k1_tarski('#skF_3') | r2_hidden('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.82/1.98  tff(c_240, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')!=k1_tarski('#skF_3')), inference(splitLeft, [status(thm)], [c_50])).
% 4.82/1.98  tff(c_779, plain, (r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_740, c_240])).
% 4.82/1.98  tff(c_812, plain, $false, inference(negUnitSimplification, [status(thm)], [c_87, c_779])).
% 4.82/1.98  tff(c_813, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_50])).
% 4.82/1.98  tff(c_1401, plain, (![B_138, A_139]: (k3_xboole_0(B_138, k1_tarski(A_139))=k1_tarski(A_139) | ~r2_hidden(A_139, B_138))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.82/1.98  tff(c_16, plain, (![A_16]: (r1_tarski(k1_xboole_0, A_16))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.82/1.98  tff(c_123, plain, (![A_68, B_69]: (k3_xboole_0(A_68, B_69)=A_68 | ~r1_tarski(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.82/1.98  tff(c_128, plain, (![A_70]: (k3_xboole_0(k1_xboole_0, A_70)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_123])).
% 4.82/1.98  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.82/1.98  tff(c_133, plain, (![A_70]: (k3_xboole_0(A_70, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_128, c_2])).
% 4.82/1.98  tff(c_20, plain, (![A_19]: (k5_xboole_0(A_19, k1_xboole_0)=A_19)), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.82/1.98  tff(c_214, plain, (![A_74, B_75]: (k5_xboole_0(A_74, k3_xboole_0(A_74, B_75))=k4_xboole_0(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.82/1.98  tff(c_223, plain, (![A_70]: (k5_xboole_0(A_70, k1_xboole_0)=k4_xboole_0(A_70, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_133, c_214])).
% 4.82/1.98  tff(c_238, plain, (![A_70]: (k4_xboole_0(A_70, k1_xboole_0)=A_70)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_223])).
% 4.82/1.98  tff(c_918, plain, (![A_117, B_118]: (k4_xboole_0(A_117, k4_xboole_0(A_117, B_118))=k3_xboole_0(A_117, B_118))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.82/1.98  tff(c_943, plain, (![A_70]: (k4_xboole_0(A_70, A_70)=k3_xboole_0(A_70, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_238, c_918])).
% 4.82/1.98  tff(c_958, plain, (![A_70]: (k4_xboole_0(A_70, A_70)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_133, c_943])).
% 4.82/1.98  tff(c_814, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_tarski('#skF_3')), inference(splitRight, [status(thm)], [c_50])).
% 4.82/1.98  tff(c_54, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')!=k1_tarski('#skF_3') | k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.82/1.98  tff(c_826, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')!=k1_tarski('#skF_3')), inference(splitLeft, [status(thm)], [c_54])).
% 4.82/1.98  tff(c_858, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_814, c_826])).
% 4.82/1.98  tff(c_859, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')=k1_tarski('#skF_5')), inference(splitRight, [status(thm)], [c_54])).
% 4.82/1.98  tff(c_940, plain, (k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_5'))=k3_xboole_0(k1_tarski('#skF_5'), '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_859, c_918])).
% 4.82/1.98  tff(c_957, plain, (k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_5'))=k3_xboole_0('#skF_6', k1_tarski('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_940])).
% 4.82/1.98  tff(c_1045, plain, (k3_xboole_0('#skF_6', k1_tarski('#skF_5'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_958, c_957])).
% 4.82/1.98  tff(c_1414, plain, (k1_tarski('#skF_5')=k1_xboole_0 | ~r2_hidden('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1401, c_1045])).
% 4.82/1.98  tff(c_1466, plain, (k1_tarski('#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_813, c_1414])).
% 4.82/1.98  tff(c_127, plain, (![A_16]: (k3_xboole_0(k1_xboole_0, A_16)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_123])).
% 4.82/1.98  tff(c_226, plain, (![A_16]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_16))), inference(superposition, [status(thm), theory('equality')], [c_127, c_214])).
% 4.82/1.98  tff(c_239, plain, (![A_16]: (k4_xboole_0(k1_xboole_0, A_16)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_226])).
% 4.82/1.98  tff(c_1820, plain, (![A_150, C_151, B_152]: (~r2_hidden(A_150, C_151) | k4_xboole_0(k2_tarski(A_150, B_152), C_151)!=k1_tarski(A_150))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.82/1.98  tff(c_3788, plain, (![A_225, C_226]: (~r2_hidden(A_225, C_226) | k4_xboole_0(k1_tarski(A_225), C_226)!=k1_tarski(A_225))), inference(superposition, [status(thm), theory('equality')], [c_24, c_1820])).
% 4.82/1.98  tff(c_3802, plain, (![C_226]: (~r2_hidden('#skF_5', C_226) | k4_xboole_0(k1_xboole_0, C_226)!=k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1466, c_3788])).
% 4.82/1.98  tff(c_3824, plain, (![C_226]: (~r2_hidden('#skF_5', C_226))), inference(demodulation, [status(thm), theory('equality')], [c_1466, c_239, c_3802])).
% 4.82/1.98  tff(c_3829, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3824, c_813])).
% 4.82/1.98  tff(c_3830, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_52])).
% 4.82/1.98  tff(c_4688, plain, (![B_274, A_275]: (k3_xboole_0(B_274, k1_tarski(A_275))=k1_tarski(A_275) | ~r2_hidden(A_275, B_274))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.82/1.98  tff(c_3831, plain, (r2_hidden('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_52])).
% 4.82/1.98  tff(c_56, plain, (~r2_hidden('#skF_3', '#skF_4') | k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.82/1.98  tff(c_4040, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')=k1_tarski('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3831, c_56])).
% 4.82/1.98  tff(c_22, plain, (![A_20, B_21]: (r1_xboole_0(k4_xboole_0(A_20, B_21), B_21))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.82/1.98  tff(c_4044, plain, (r1_xboole_0(k1_tarski('#skF_5'), '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_4040, c_22])).
% 4.82/1.98  tff(c_10, plain, (![A_10]: (r2_hidden('#skF_2'(A_10), A_10) | k1_xboole_0=A_10)), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.82/1.98  tff(c_3985, plain, (![A_240, B_241, C_242]: (~r1_xboole_0(A_240, B_241) | ~r2_hidden(C_242, k3_xboole_0(A_240, B_241)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.82/1.98  tff(c_4203, plain, (![A_256, B_257]: (~r1_xboole_0(A_256, B_257) | k3_xboole_0(A_256, B_257)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_3985])).
% 4.82/1.98  tff(c_4223, plain, (k3_xboole_0(k1_tarski('#skF_5'), '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_4044, c_4203])).
% 4.82/1.98  tff(c_4242, plain, (k3_xboole_0('#skF_6', k1_tarski('#skF_5'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_4223, c_2])).
% 4.82/1.98  tff(c_4701, plain, (k1_tarski('#skF_5')=k1_xboole_0 | ~r2_hidden('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_4688, c_4242])).
% 4.82/1.98  tff(c_4753, plain, (k1_tarski('#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3830, c_4701])).
% 4.82/1.98  tff(c_3867, plain, (![A_232, B_233]: (k3_xboole_0(A_232, B_233)=A_232 | ~r1_tarski(A_232, B_233))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.82/1.98  tff(c_3871, plain, (![A_16]: (k3_xboole_0(k1_xboole_0, A_16)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_3867])).
% 4.82/1.98  tff(c_3959, plain, (![A_238, B_239]: (k5_xboole_0(A_238, k3_xboole_0(A_238, B_239))=k4_xboole_0(A_238, B_239))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.82/1.98  tff(c_3971, plain, (![A_16]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_16))), inference(superposition, [status(thm), theory('equality')], [c_3871, c_3959])).
% 4.82/1.98  tff(c_3984, plain, (![A_16]: (k4_xboole_0(k1_xboole_0, A_16)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_3971])).
% 4.82/1.98  tff(c_4851, plain, (![A_278, C_279, B_280]: (~r2_hidden(A_278, C_279) | k4_xboole_0(k2_tarski(A_278, B_280), C_279)!=k1_tarski(A_278))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.82/1.98  tff(c_6613, plain, (![A_352, C_353]: (~r2_hidden(A_352, C_353) | k4_xboole_0(k1_tarski(A_352), C_353)!=k1_tarski(A_352))), inference(superposition, [status(thm), theory('equality')], [c_24, c_4851])).
% 4.82/1.98  tff(c_6623, plain, (![C_353]: (~r2_hidden('#skF_5', C_353) | k4_xboole_0(k1_xboole_0, C_353)!=k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_4753, c_6613])).
% 4.82/1.98  tff(c_6645, plain, (![C_353]: (~r2_hidden('#skF_5', C_353))), inference(demodulation, [status(thm), theory('equality')], [c_4753, c_3984, c_6623])).
% 4.82/1.98  tff(c_6650, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6645, c_3830])).
% 4.82/1.98  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.82/1.98  
% 4.82/1.98  Inference rules
% 4.82/1.98  ----------------------
% 4.82/1.98  #Ref     : 0
% 4.82/1.98  #Sup     : 1619
% 4.82/1.98  #Fact    : 0
% 4.82/1.98  #Define  : 0
% 4.82/1.98  #Split   : 3
% 4.82/1.98  #Chain   : 0
% 4.82/1.98  #Close   : 0
% 4.82/1.98  
% 4.82/1.98  Ordering : KBO
% 4.82/1.98  
% 4.82/1.98  Simplification rules
% 4.82/1.98  ----------------------
% 4.82/1.98  #Subsume      : 199
% 4.82/1.98  #Demod        : 1096
% 4.82/1.98  #Tautology    : 1066
% 4.82/1.98  #SimpNegUnit  : 59
% 4.82/1.98  #BackRed      : 16
% 4.82/1.98  
% 4.82/1.98  #Partial instantiations: 0
% 4.82/1.98  #Strategies tried      : 1
% 4.82/1.98  
% 4.82/1.98  Timing (in seconds)
% 4.82/1.98  ----------------------
% 4.82/1.98  Preprocessing        : 0.33
% 4.82/1.98  Parsing              : 0.18
% 4.82/1.98  CNF conversion       : 0.02
% 4.82/1.98  Main loop            : 0.87
% 4.82/1.98  Inferencing          : 0.29
% 4.82/1.98  Reduction            : 0.36
% 4.82/1.98  Demodulation         : 0.28
% 4.82/1.98  BG Simplification    : 0.03
% 4.82/1.98  Subsumption          : 0.13
% 4.82/1.98  Abstraction          : 0.04
% 4.82/1.98  MUC search           : 0.00
% 4.82/1.98  Cooper               : 0.00
% 4.82/1.98  Total                : 1.24
% 4.82/1.98  Index Insertion      : 0.00
% 4.82/1.98  Index Deletion       : 0.00
% 4.82/1.98  Index Matching       : 0.00
% 4.82/1.98  BG Taut test         : 0.00
%------------------------------------------------------------------------------
