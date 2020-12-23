%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:59 EST 2020

% Result     : Theorem 4.58s
% Output     : CNFRefutation 4.89s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 234 expanded)
%              Number of leaves         :   34 (  92 expanded)
%              Depth                    :   13
%              Number of atoms          :  106 ( 271 expanded)
%              Number of equality atoms :   66 ( 172 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_41,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_45,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_83,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
      <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_zfmisc_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(c_3864,plain,(
    ! [B_231,A_232] : k3_xboole_0(B_231,A_232) = k3_xboole_0(A_232,B_231) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_81,plain,(
    ! [A_55,B_56] : r1_tarski(k3_xboole_0(A_55,B_56),A_55) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12,plain,(
    ! [A_11] :
      ( k1_xboole_0 = A_11
      | ~ r1_tarski(A_11,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_89,plain,(
    ! [B_56] : k3_xboole_0(k1_xboole_0,B_56) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_81,c_12])).

tff(c_3880,plain,(
    ! [B_231] : k3_xboole_0(B_231,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_3864,c_89])).

tff(c_16,plain,(
    ! [A_14] : k5_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_4065,plain,(
    ! [A_254,B_255] : k5_xboole_0(A_254,k3_xboole_0(A_254,B_255)) = k4_xboole_0(A_254,B_255) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4074,plain,(
    ! [B_231] : k5_xboole_0(B_231,k1_xboole_0) = k4_xboole_0(B_231,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_3880,c_4065])).

tff(c_4089,plain,(
    ! [B_231] : k4_xboole_0(B_231,k1_xboole_0) = B_231 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_4074])).

tff(c_4136,plain,(
    ! [A_259,B_260] : k4_xboole_0(A_259,k4_xboole_0(A_259,B_260)) = k3_xboole_0(A_259,B_260) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_4155,plain,(
    ! [B_231] : k4_xboole_0(B_231,B_231) = k3_xboole_0(B_231,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4089,c_4136])).

tff(c_4169,plain,(
    ! [B_231] : k4_xboole_0(B_231,B_231) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3880,c_4155])).

tff(c_42,plain,(
    ! [B_50] : k4_xboole_0(k1_tarski(B_50),k1_tarski(B_50)) != k1_tarski(B_50) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_4174,plain,(
    ! [B_50] : k1_tarski(B_50) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4169,c_42])).

tff(c_119,plain,(
    ! [B_59,A_60] : k3_xboole_0(B_59,A_60) = k3_xboole_0(A_60,B_59) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_135,plain,(
    ! [B_59] : k3_xboole_0(B_59,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_89])).

tff(c_1996,plain,(
    ! [A_166,B_167] : k5_xboole_0(A_166,k3_xboole_0(A_166,B_167)) = k4_xboole_0(A_166,B_167) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2005,plain,(
    ! [B_59] : k5_xboole_0(B_59,k1_xboole_0) = k4_xboole_0(B_59,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_1996])).

tff(c_2043,plain,(
    ! [B_169] : k4_xboole_0(B_169,k1_xboole_0) = B_169 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_2005])).

tff(c_14,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k4_xboole_0(A_12,B_13)) = k3_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2053,plain,(
    ! [B_169] : k4_xboole_0(B_169,B_169) = k3_xboole_0(B_169,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2043,c_14])).

tff(c_2063,plain,(
    ! [B_169] : k4_xboole_0(B_169,B_169) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_2053])).

tff(c_2067,plain,(
    ! [B_50] : k1_tarski(B_50) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2063,c_42])).

tff(c_48,plain,
    ( ~ r2_hidden('#skF_1','#skF_2')
    | r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_90,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_40,plain,(
    ! [A_47,B_48] :
      ( r1_xboole_0(k1_tarski(A_47),B_48)
      | r2_hidden(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_310,plain,(
    ! [A_80,B_81] :
      ( k4_xboole_0(A_80,B_81) = A_80
      | ~ r1_xboole_0(A_80,B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1836,plain,(
    ! [A_147,B_148] :
      ( k4_xboole_0(k1_tarski(A_147),B_148) = k1_tarski(A_147)
      | r2_hidden(A_147,B_148) ) ),
    inference(resolution,[status(thm)],[c_40,c_310])).

tff(c_46,plain,
    ( k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_tarski('#skF_1')
    | r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_275,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_tarski('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_1869,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1836,c_275])).

tff(c_1906,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_1869])).

tff(c_1907,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_1929,plain,(
    ! [A_153,B_154] :
      ( r1_tarski(k1_tarski(A_153),B_154)
      | ~ r2_hidden(A_153,B_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_10,plain,(
    ! [A_9,B_10] :
      ( k3_xboole_0(A_9,B_10) = A_9
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_3699,plain,(
    ! [A_227,B_228] :
      ( k3_xboole_0(k1_tarski(A_227),B_228) = k1_tarski(A_227)
      | ~ r2_hidden(A_227,B_228) ) ),
    inference(resolution,[status(thm)],[c_1929,c_10])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1908,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') = k1_tarski('#skF_1') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_50,plain,
    ( k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_tarski('#skF_1')
    | k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1923,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_tarski('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1908,c_50])).

tff(c_1962,plain,(
    ! [A_164,B_165] : k4_xboole_0(A_164,k4_xboole_0(A_164,B_165)) = k3_xboole_0(A_164,B_165) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1977,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_3')) = k3_xboole_0(k1_tarski('#skF_3'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1923,c_1962])).

tff(c_1983,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_3')) = k3_xboole_0('#skF_4',k1_tarski('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1977])).

tff(c_2066,plain,(
    k3_xboole_0('#skF_4',k1_tarski('#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2063,c_1983])).

tff(c_8,plain,(
    ! [A_7,B_8] : r1_tarski(k3_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_243,plain,(
    ! [B_65,A_66] : r1_tarski(k3_xboole_0(B_65,A_66),A_66) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_8])).

tff(c_2753,plain,(
    ! [B_202,A_203] : k3_xboole_0(k3_xboole_0(B_202,A_203),A_203) = k3_xboole_0(B_202,A_203) ),
    inference(resolution,[status(thm)],[c_243,c_10])).

tff(c_3339,plain,(
    ! [B_225,A_226] : k3_xboole_0(k3_xboole_0(B_225,A_226),B_225) = k3_xboole_0(A_226,B_225) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2753])).

tff(c_3455,plain,(
    k3_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k3_xboole_0(k1_xboole_0,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2066,c_3339])).

tff(c_3514,plain,(
    k3_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_2,c_3455])).

tff(c_3705,plain,
    ( k1_tarski('#skF_3') = k1_xboole_0
    | ~ r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3699,c_3514])).

tff(c_3825,plain,(
    k1_tarski('#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1907,c_3705])).

tff(c_3827,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2067,c_3825])).

tff(c_3828,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_38,plain,(
    ! [A_45,B_46] :
      ( r1_tarski(k1_tarski(A_45),B_46)
      | ~ r2_hidden(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_4036,plain,(
    ! [A_250,B_251] :
      ( k3_xboole_0(A_250,B_251) = A_250
      | ~ r1_tarski(A_250,B_251) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_5728,plain,(
    ! [A_320,B_321] :
      ( k3_xboole_0(k1_tarski(A_320),B_321) = k1_tarski(A_320)
      | ~ r2_hidden(A_320,B_321) ) ),
    inference(resolution,[status(thm)],[c_38,c_4036])).

tff(c_3829,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_52,plain,
    ( ~ r2_hidden('#skF_1','#skF_2')
    | k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_3838,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_tarski('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3829,c_52])).

tff(c_4165,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_3')) = k3_xboole_0(k1_tarski('#skF_3'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3838,c_4136])).

tff(c_4172,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_3')) = k3_xboole_0('#skF_4',k1_tarski('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4165])).

tff(c_4207,plain,(
    k3_xboole_0('#skF_4',k1_tarski('#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4169,c_4172])).

tff(c_3887,plain,(
    ! [B_231,A_232] : r1_tarski(k3_xboole_0(B_231,A_232),A_232) ),
    inference(superposition,[status(thm),theory(equality)],[c_3864,c_8])).

tff(c_4794,plain,(
    ! [B_288,A_289] : k3_xboole_0(k3_xboole_0(B_288,A_289),A_289) = k3_xboole_0(B_288,A_289) ),
    inference(resolution,[status(thm)],[c_3887,c_4036])).

tff(c_5372,plain,(
    ! [A_316,B_317] : k3_xboole_0(k3_xboole_0(A_316,B_317),A_316) = k3_xboole_0(B_317,A_316) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_4794])).

tff(c_5485,plain,(
    k3_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k3_xboole_0(k1_xboole_0,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4207,c_5372])).

tff(c_5543,plain,(
    k3_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_5485])).

tff(c_5734,plain,
    ( k1_tarski('#skF_3') = k1_xboole_0
    | ~ r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_5728,c_5543])).

tff(c_5848,plain,(
    k1_tarski('#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3828,c_5734])).

tff(c_5850,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4174,c_5848])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:55:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.58/1.93  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.89/1.94  
% 4.89/1.94  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.89/1.94  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.89/1.94  
% 4.89/1.94  %Foreground sorts:
% 4.89/1.94  
% 4.89/1.94  
% 4.89/1.94  %Background operators:
% 4.89/1.94  
% 4.89/1.94  
% 4.89/1.94  %Foreground operators:
% 4.89/1.94  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.89/1.94  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.89/1.94  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.89/1.94  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.89/1.94  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.89/1.94  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.89/1.94  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.89/1.94  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.89/1.94  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.89/1.94  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.89/1.94  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.89/1.94  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.89/1.94  tff('#skF_2', type, '#skF_2': $i).
% 4.89/1.94  tff('#skF_3', type, '#skF_3': $i).
% 4.89/1.94  tff('#skF_1', type, '#skF_1': $i).
% 4.89/1.94  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.89/1.94  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.89/1.94  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.89/1.94  tff('#skF_4', type, '#skF_4': $i).
% 4.89/1.94  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.89/1.94  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.89/1.94  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.89/1.94  
% 4.89/1.96  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.89/1.96  tff(f_33, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 4.89/1.96  tff(f_41, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 4.89/1.96  tff(f_45, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 4.89/1.96  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.89/1.96  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.89/1.96  tff(f_77, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 4.89/1.96  tff(f_83, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_zfmisc_1)).
% 4.89/1.96  tff(f_72, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 4.89/1.96  tff(f_49, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 4.89/1.96  tff(f_67, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 4.89/1.96  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.89/1.96  tff(c_3864, plain, (![B_231, A_232]: (k3_xboole_0(B_231, A_232)=k3_xboole_0(A_232, B_231))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.89/1.96  tff(c_81, plain, (![A_55, B_56]: (r1_tarski(k3_xboole_0(A_55, B_56), A_55))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.89/1.96  tff(c_12, plain, (![A_11]: (k1_xboole_0=A_11 | ~r1_tarski(A_11, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.89/1.96  tff(c_89, plain, (![B_56]: (k3_xboole_0(k1_xboole_0, B_56)=k1_xboole_0)), inference(resolution, [status(thm)], [c_81, c_12])).
% 4.89/1.96  tff(c_3880, plain, (![B_231]: (k3_xboole_0(B_231, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3864, c_89])).
% 4.89/1.96  tff(c_16, plain, (![A_14]: (k5_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.89/1.96  tff(c_4065, plain, (![A_254, B_255]: (k5_xboole_0(A_254, k3_xboole_0(A_254, B_255))=k4_xboole_0(A_254, B_255))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.89/1.96  tff(c_4074, plain, (![B_231]: (k5_xboole_0(B_231, k1_xboole_0)=k4_xboole_0(B_231, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_3880, c_4065])).
% 4.89/1.96  tff(c_4089, plain, (![B_231]: (k4_xboole_0(B_231, k1_xboole_0)=B_231)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_4074])).
% 4.89/1.96  tff(c_4136, plain, (![A_259, B_260]: (k4_xboole_0(A_259, k4_xboole_0(A_259, B_260))=k3_xboole_0(A_259, B_260))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.89/1.96  tff(c_4155, plain, (![B_231]: (k4_xboole_0(B_231, B_231)=k3_xboole_0(B_231, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4089, c_4136])).
% 4.89/1.96  tff(c_4169, plain, (![B_231]: (k4_xboole_0(B_231, B_231)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_3880, c_4155])).
% 4.89/1.96  tff(c_42, plain, (![B_50]: (k4_xboole_0(k1_tarski(B_50), k1_tarski(B_50))!=k1_tarski(B_50))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.89/1.96  tff(c_4174, plain, (![B_50]: (k1_tarski(B_50)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4169, c_42])).
% 4.89/1.96  tff(c_119, plain, (![B_59, A_60]: (k3_xboole_0(B_59, A_60)=k3_xboole_0(A_60, B_59))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.89/1.96  tff(c_135, plain, (![B_59]: (k3_xboole_0(B_59, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_119, c_89])).
% 4.89/1.96  tff(c_1996, plain, (![A_166, B_167]: (k5_xboole_0(A_166, k3_xboole_0(A_166, B_167))=k4_xboole_0(A_166, B_167))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.89/1.96  tff(c_2005, plain, (![B_59]: (k5_xboole_0(B_59, k1_xboole_0)=k4_xboole_0(B_59, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_135, c_1996])).
% 4.89/1.96  tff(c_2043, plain, (![B_169]: (k4_xboole_0(B_169, k1_xboole_0)=B_169)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_2005])).
% 4.89/1.96  tff(c_14, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k4_xboole_0(A_12, B_13))=k3_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.89/1.96  tff(c_2053, plain, (![B_169]: (k4_xboole_0(B_169, B_169)=k3_xboole_0(B_169, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2043, c_14])).
% 4.89/1.96  tff(c_2063, plain, (![B_169]: (k4_xboole_0(B_169, B_169)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_135, c_2053])).
% 4.89/1.96  tff(c_2067, plain, (![B_50]: (k1_tarski(B_50)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2063, c_42])).
% 4.89/1.96  tff(c_48, plain, (~r2_hidden('#skF_1', '#skF_2') | r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.89/1.96  tff(c_90, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_48])).
% 4.89/1.96  tff(c_40, plain, (![A_47, B_48]: (r1_xboole_0(k1_tarski(A_47), B_48) | r2_hidden(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.89/1.96  tff(c_310, plain, (![A_80, B_81]: (k4_xboole_0(A_80, B_81)=A_80 | ~r1_xboole_0(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.89/1.96  tff(c_1836, plain, (![A_147, B_148]: (k4_xboole_0(k1_tarski(A_147), B_148)=k1_tarski(A_147) | r2_hidden(A_147, B_148))), inference(resolution, [status(thm)], [c_40, c_310])).
% 4.89/1.96  tff(c_46, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_tarski('#skF_1') | r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.89/1.96  tff(c_275, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_tarski('#skF_1')), inference(splitLeft, [status(thm)], [c_46])).
% 4.89/1.96  tff(c_1869, plain, (r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1836, c_275])).
% 4.89/1.96  tff(c_1906, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_1869])).
% 4.89/1.96  tff(c_1907, plain, (r2_hidden('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_46])).
% 4.89/1.96  tff(c_1929, plain, (![A_153, B_154]: (r1_tarski(k1_tarski(A_153), B_154) | ~r2_hidden(A_153, B_154))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.89/1.96  tff(c_10, plain, (![A_9, B_10]: (k3_xboole_0(A_9, B_10)=A_9 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.89/1.96  tff(c_3699, plain, (![A_227, B_228]: (k3_xboole_0(k1_tarski(A_227), B_228)=k1_tarski(A_227) | ~r2_hidden(A_227, B_228))), inference(resolution, [status(thm)], [c_1929, c_10])).
% 4.89/1.96  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.89/1.96  tff(c_1908, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')=k1_tarski('#skF_1')), inference(splitRight, [status(thm)], [c_46])).
% 4.89/1.96  tff(c_50, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_tarski('#skF_1') | k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.89/1.96  tff(c_1923, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_tarski('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1908, c_50])).
% 4.89/1.96  tff(c_1962, plain, (![A_164, B_165]: (k4_xboole_0(A_164, k4_xboole_0(A_164, B_165))=k3_xboole_0(A_164, B_165))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.89/1.96  tff(c_1977, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_3'))=k3_xboole_0(k1_tarski('#skF_3'), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1923, c_1962])).
% 4.89/1.96  tff(c_1983, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_3'))=k3_xboole_0('#skF_4', k1_tarski('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_1977])).
% 4.89/1.96  tff(c_2066, plain, (k3_xboole_0('#skF_4', k1_tarski('#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2063, c_1983])).
% 4.89/1.96  tff(c_8, plain, (![A_7, B_8]: (r1_tarski(k3_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.89/1.96  tff(c_243, plain, (![B_65, A_66]: (r1_tarski(k3_xboole_0(B_65, A_66), A_66))), inference(superposition, [status(thm), theory('equality')], [c_119, c_8])).
% 4.89/1.96  tff(c_2753, plain, (![B_202, A_203]: (k3_xboole_0(k3_xboole_0(B_202, A_203), A_203)=k3_xboole_0(B_202, A_203))), inference(resolution, [status(thm)], [c_243, c_10])).
% 4.89/1.96  tff(c_3339, plain, (![B_225, A_226]: (k3_xboole_0(k3_xboole_0(B_225, A_226), B_225)=k3_xboole_0(A_226, B_225))), inference(superposition, [status(thm), theory('equality')], [c_2, c_2753])).
% 4.89/1.96  tff(c_3455, plain, (k3_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k3_xboole_0(k1_xboole_0, '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2066, c_3339])).
% 4.89/1.96  tff(c_3514, plain, (k3_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_135, c_2, c_3455])).
% 4.89/1.96  tff(c_3705, plain, (k1_tarski('#skF_3')=k1_xboole_0 | ~r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3699, c_3514])).
% 4.89/1.96  tff(c_3825, plain, (k1_tarski('#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1907, c_3705])).
% 4.89/1.96  tff(c_3827, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2067, c_3825])).
% 4.89/1.96  tff(c_3828, plain, (r2_hidden('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_48])).
% 4.89/1.96  tff(c_38, plain, (![A_45, B_46]: (r1_tarski(k1_tarski(A_45), B_46) | ~r2_hidden(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.89/1.96  tff(c_4036, plain, (![A_250, B_251]: (k3_xboole_0(A_250, B_251)=A_250 | ~r1_tarski(A_250, B_251))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.89/1.96  tff(c_5728, plain, (![A_320, B_321]: (k3_xboole_0(k1_tarski(A_320), B_321)=k1_tarski(A_320) | ~r2_hidden(A_320, B_321))), inference(resolution, [status(thm)], [c_38, c_4036])).
% 4.89/1.96  tff(c_3829, plain, (r2_hidden('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_48])).
% 4.89/1.96  tff(c_52, plain, (~r2_hidden('#skF_1', '#skF_2') | k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.89/1.96  tff(c_3838, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_tarski('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3829, c_52])).
% 4.89/1.96  tff(c_4165, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_3'))=k3_xboole_0(k1_tarski('#skF_3'), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3838, c_4136])).
% 4.89/1.96  tff(c_4172, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_3'))=k3_xboole_0('#skF_4', k1_tarski('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4165])).
% 4.89/1.96  tff(c_4207, plain, (k3_xboole_0('#skF_4', k1_tarski('#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_4169, c_4172])).
% 4.89/1.96  tff(c_3887, plain, (![B_231, A_232]: (r1_tarski(k3_xboole_0(B_231, A_232), A_232))), inference(superposition, [status(thm), theory('equality')], [c_3864, c_8])).
% 4.89/1.96  tff(c_4794, plain, (![B_288, A_289]: (k3_xboole_0(k3_xboole_0(B_288, A_289), A_289)=k3_xboole_0(B_288, A_289))), inference(resolution, [status(thm)], [c_3887, c_4036])).
% 4.89/1.96  tff(c_5372, plain, (![A_316, B_317]: (k3_xboole_0(k3_xboole_0(A_316, B_317), A_316)=k3_xboole_0(B_317, A_316))), inference(superposition, [status(thm), theory('equality')], [c_2, c_4794])).
% 4.89/1.96  tff(c_5485, plain, (k3_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k3_xboole_0(k1_xboole_0, '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4207, c_5372])).
% 4.89/1.96  tff(c_5543, plain, (k3_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_89, c_5485])).
% 4.89/1.96  tff(c_5734, plain, (k1_tarski('#skF_3')=k1_xboole_0 | ~r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_5728, c_5543])).
% 4.89/1.96  tff(c_5848, plain, (k1_tarski('#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3828, c_5734])).
% 4.89/1.96  tff(c_5850, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4174, c_5848])).
% 4.89/1.96  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.89/1.96  
% 4.89/1.96  Inference rules
% 4.89/1.96  ----------------------
% 4.89/1.96  #Ref     : 0
% 4.89/1.96  #Sup     : 1408
% 4.89/1.96  #Fact    : 0
% 4.89/1.96  #Define  : 0
% 4.89/1.96  #Split   : 2
% 4.89/1.96  #Chain   : 0
% 4.89/1.96  #Close   : 0
% 4.89/1.96  
% 4.89/1.96  Ordering : KBO
% 4.89/1.96  
% 4.89/1.96  Simplification rules
% 4.89/1.96  ----------------------
% 4.89/1.96  #Subsume      : 48
% 4.89/1.96  #Demod        : 1408
% 4.89/1.96  #Tautology    : 1040
% 4.89/1.96  #SimpNegUnit  : 18
% 4.89/1.96  #BackRed      : 9
% 4.89/1.96  
% 4.89/1.96  #Partial instantiations: 0
% 4.89/1.96  #Strategies tried      : 1
% 4.89/1.96  
% 4.89/1.96  Timing (in seconds)
% 4.89/1.96  ----------------------
% 4.89/1.96  Preprocessing        : 0.35
% 4.89/1.97  Parsing              : 0.19
% 4.89/1.97  CNF conversion       : 0.02
% 4.89/1.97  Main loop            : 0.80
% 4.89/1.97  Inferencing          : 0.27
% 4.89/1.97  Reduction            : 0.35
% 4.89/1.97  Demodulation         : 0.28
% 4.89/1.97  BG Simplification    : 0.03
% 4.89/1.97  Subsumption          : 0.10
% 4.89/1.97  Abstraction          : 0.05
% 4.89/1.97  MUC search           : 0.00
% 4.89/1.97  Cooper               : 0.00
% 4.89/1.97  Total                : 1.18
% 4.89/1.97  Index Insertion      : 0.00
% 4.89/1.97  Index Deletion       : 0.00
% 4.89/1.97  Index Matching       : 0.00
% 4.89/1.97  BG Taut test         : 0.00
%------------------------------------------------------------------------------
