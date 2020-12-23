%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:17 EST 2020

% Result     : Theorem 3.11s
% Output     : CNFRefutation 3.11s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 151 expanded)
%              Number of leaves         :   42 (  69 expanded)
%              Depth                    :    8
%              Number of atoms          :   96 ( 178 expanded)
%              Number of equality atoms :   65 ( 140 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_setfam_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_1 > #skF_4

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_33,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_35,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_88,axiom,(
    ! [A,B,C,D,E,F,G] :
      ( G = k4_enumset1(A,B,C,D,E,F)
    <=> ! [H] :
          ( r2_hidden(H,G)
        <=> ~ ( H != A
              & H != B
              & H != C
              & H != D
              & H != E
              & H != F ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_enumset1)).

tff(f_104,negated_conjecture,(
    ~ ! [A] :
        ( ? [B,C] : A = k4_tarski(B,C)
       => ( A != k1_mcart_1(A)
          & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k1_tarski(A),k2_tarski(B,C)) = k2_tarski(k4_tarski(A,B),k4_tarski(A,C))
      & k2_zfmisc_1(k2_tarski(A,B),k1_tarski(C)) = k2_tarski(k4_tarski(A,C),k4_tarski(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( r1_tarski(A,k2_zfmisc_1(A,B))
        | r1_tarski(A,k2_zfmisc_1(B,A)) )
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t135_zfmisc_1)).

tff(c_8,plain,(
    ! [A_6] : k2_tarski(A_6,A_6) = k1_tarski(A_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_7,B_8] : k1_enumset1(A_7,A_7,B_8) = k2_tarski(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_9,B_10,C_11] : k2_enumset1(A_9,A_9,B_10,C_11) = k1_enumset1(A_9,B_10,C_11) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [A_12,B_13,C_14,D_15] : k3_enumset1(A_12,A_12,B_13,C_14,D_15) = k2_enumset1(A_12,B_13,C_14,D_15) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_681,plain,(
    ! [C_245,E_242,A_243,D_244,B_241] : k4_enumset1(A_243,A_243,B_241,C_245,D_244,E_242) = k3_enumset1(A_243,B_241,C_245,D_244,E_242) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_48,plain,(
    ! [H_52,E_47,F_48,D_46,C_45,A_43] : r2_hidden(H_52,k4_enumset1(A_43,H_52,C_45,D_46,E_47,F_48)) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_708,plain,(
    ! [B_249,A_250,D_248,E_247,C_246] : r2_hidden(A_250,k3_enumset1(A_250,B_249,C_246,D_248,E_247)) ),
    inference(superposition,[status(thm),theory(equality)],[c_681,c_48])).

tff(c_712,plain,(
    ! [A_251,B_252,C_253,D_254] : r2_hidden(A_251,k2_enumset1(A_251,B_252,C_253,D_254)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_708])).

tff(c_716,plain,(
    ! [A_255,B_256,C_257] : r2_hidden(A_255,k1_enumset1(A_255,B_256,C_257)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_712])).

tff(c_720,plain,(
    ! [A_258,B_259] : r2_hidden(A_258,k2_tarski(A_258,B_259)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_716])).

tff(c_723,plain,(
    ! [A_6] : r2_hidden(A_6,k1_tarski(A_6)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_720])).

tff(c_470,plain,(
    ! [B_149,D_152,C_153,E_150,A_151] : k4_enumset1(A_151,A_151,B_149,C_153,D_152,E_150) = k3_enumset1(A_151,B_149,C_153,D_152,E_150) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_46,plain,(
    ! [H_52,E_47,F_48,D_46,A_43,B_44] : r2_hidden(H_52,k4_enumset1(A_43,B_44,H_52,D_46,E_47,F_48)) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_501,plain,(
    ! [A_155,D_156,B_158,C_157,E_154] : r2_hidden(B_158,k3_enumset1(A_155,B_158,C_157,D_156,E_154)) ),
    inference(superposition,[status(thm),theory(equality)],[c_470,c_46])).

tff(c_505,plain,(
    ! [A_159,B_160,C_161,D_162] : r2_hidden(A_159,k2_enumset1(A_159,B_160,C_161,D_162)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_501])).

tff(c_518,plain,(
    ! [A_169,B_170,C_171] : r2_hidden(A_169,k1_enumset1(A_169,B_170,C_171)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_505])).

tff(c_522,plain,(
    ! [A_172,B_173] : r2_hidden(A_172,k2_tarski(A_172,B_173)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_518])).

tff(c_531,plain,(
    ! [A_6] : r2_hidden(A_6,k1_tarski(A_6)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_522])).

tff(c_88,plain,(
    k4_tarski('#skF_4','#skF_5') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_118,plain,(
    ! [A_62,B_63] : k1_mcart_1(k4_tarski(A_62,B_63)) = A_62 ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_127,plain,(
    k1_mcart_1('#skF_3') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_118])).

tff(c_130,plain,(
    ! [A_64,B_65] : k2_mcart_1(k4_tarski(A_64,B_65)) = B_65 ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_139,plain,(
    k2_mcart_1('#skF_3') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_130])).

tff(c_86,plain,
    ( k2_mcart_1('#skF_3') = '#skF_3'
    | k1_mcart_1('#skF_3') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_150,plain,
    ( '#skF_5' = '#skF_3'
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_139,c_86])).

tff(c_151,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_150])).

tff(c_154,plain,(
    k4_tarski('#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_88])).

tff(c_301,plain,(
    ! [A_133,B_134,C_135] : k2_zfmisc_1(k1_tarski(A_133),k2_tarski(B_134,C_135)) = k2_tarski(k4_tarski(A_133,B_134),k4_tarski(A_133,C_135)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_326,plain,(
    ! [A_133,C_135] : k2_zfmisc_1(k1_tarski(A_133),k2_tarski(C_135,C_135)) = k1_tarski(k4_tarski(A_133,C_135)) ),
    inference(superposition,[status(thm),theory(equality)],[c_301,c_8])).

tff(c_351,plain,(
    ! [A_136,C_137] : k2_zfmisc_1(k1_tarski(A_136),k1_tarski(C_137)) = k1_tarski(k4_tarski(A_136,C_137)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_326])).

tff(c_6,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_229,plain,(
    ! [A_80,B_81] : k5_xboole_0(A_80,k3_xboole_0(A_80,B_81)) = k4_xboole_0(A_80,B_81) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_238,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_229])).

tff(c_241,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_238])).

tff(c_30,plain,(
    ! [B_39] : k4_xboole_0(k1_tarski(B_39),k1_tarski(B_39)) != k1_tarski(B_39) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_242,plain,(
    ! [B_39] : k1_tarski(B_39) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_241,c_30])).

tff(c_24,plain,(
    ! [A_34,B_35] :
      ( r1_tarski(k1_tarski(A_34),B_35)
      | ~ r2_hidden(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_223,plain,(
    ! [A_78,B_79] :
      ( ~ r1_tarski(A_78,k2_zfmisc_1(A_78,B_79))
      | k1_xboole_0 = A_78 ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_228,plain,(
    ! [A_34,B_79] :
      ( k1_tarski(A_34) = k1_xboole_0
      | ~ r2_hidden(A_34,k2_zfmisc_1(k1_tarski(A_34),B_79)) ) ),
    inference(resolution,[status(thm)],[c_24,c_223])).

tff(c_290,plain,(
    ! [A_34,B_79] : ~ r2_hidden(A_34,k2_zfmisc_1(k1_tarski(A_34),B_79)) ),
    inference(negUnitSimplification,[status(thm)],[c_242,c_228])).

tff(c_374,plain,(
    ! [A_138,C_139] : ~ r2_hidden(A_138,k1_tarski(k4_tarski(A_138,C_139))) ),
    inference(superposition,[status(thm),theory(equality)],[c_351,c_290])).

tff(c_377,plain,(
    ~ r2_hidden('#skF_4',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_374])).

tff(c_534,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_531,c_377])).

tff(c_535,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_150])).

tff(c_538,plain,(
    k4_tarski('#skF_4','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_535,c_88])).

tff(c_725,plain,(
    ! [A_261,B_262,C_263] : k2_zfmisc_1(k2_tarski(A_261,B_262),k1_tarski(C_263)) = k2_tarski(k4_tarski(A_261,C_263),k4_tarski(B_262,C_263)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_765,plain,(
    ! [A_6,C_263] : k2_zfmisc_1(k1_tarski(A_6),k1_tarski(C_263)) = k2_tarski(k4_tarski(A_6,C_263),k4_tarski(A_6,C_263)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_725])).

tff(c_916,plain,(
    ! [A_320,C_321] : k2_zfmisc_1(k1_tarski(A_320),k1_tarski(C_321)) = k1_tarski(k4_tarski(A_320,C_321)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_765])).

tff(c_609,plain,(
    ! [A_188,B_189] : k5_xboole_0(A_188,k3_xboole_0(A_188,B_189)) = k4_xboole_0(A_188,B_189) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_618,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_609])).

tff(c_621,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_618])).

tff(c_622,plain,(
    ! [B_39] : k1_tarski(B_39) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_621,c_30])).

tff(c_582,plain,(
    ! [A_179,B_180] :
      ( ~ r1_tarski(A_179,k2_zfmisc_1(B_180,A_179))
      | k1_xboole_0 = A_179 ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_587,plain,(
    ! [A_34,B_180] :
      ( k1_tarski(A_34) = k1_xboole_0
      | ~ r2_hidden(A_34,k2_zfmisc_1(B_180,k1_tarski(A_34))) ) ),
    inference(resolution,[status(thm)],[c_24,c_582])).

tff(c_670,plain,(
    ! [A_34,B_180] : ~ r2_hidden(A_34,k2_zfmisc_1(B_180,k1_tarski(A_34))) ),
    inference(negUnitSimplification,[status(thm)],[c_622,c_587])).

tff(c_939,plain,(
    ! [C_322,A_323] : ~ r2_hidden(C_322,k1_tarski(k4_tarski(A_323,C_322))) ),
    inference(superposition,[status(thm),theory(equality)],[c_916,c_670])).

tff(c_942,plain,(
    ~ r2_hidden('#skF_3',k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_538,c_939])).

tff(c_945,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_723,c_942])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:54:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.11/1.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.11/1.46  
% 3.11/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.11/1.46  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_setfam_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_1 > #skF_4
% 3.11/1.46  
% 3.11/1.46  %Foreground sorts:
% 3.11/1.46  
% 3.11/1.46  
% 3.11/1.46  %Background operators:
% 3.11/1.46  
% 3.11/1.46  
% 3.11/1.46  %Foreground operators:
% 3.11/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.11/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.11/1.46  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.11/1.46  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.11/1.46  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.11/1.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.11/1.46  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.11/1.46  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.11/1.46  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.11/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.11/1.46  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.11/1.46  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.11/1.46  tff('#skF_5', type, '#skF_5': $i).
% 3.11/1.46  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.11/1.46  tff('#skF_3', type, '#skF_3': $i).
% 3.11/1.46  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.11/1.46  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.11/1.46  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.11/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.11/1.46  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 3.11/1.46  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.11/1.46  tff('#skF_4', type, '#skF_4': $i).
% 3.11/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.11/1.46  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 3.11/1.46  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.11/1.46  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.11/1.46  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.11/1.46  
% 3.11/1.48  tff(f_33, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.11/1.48  tff(f_35, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.11/1.48  tff(f_37, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 3.11/1.48  tff(f_39, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 3.11/1.48  tff(f_41, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 3.11/1.48  tff(f_88, axiom, (![A, B, C, D, E, F, G]: ((G = k4_enumset1(A, B, C, D, E, F)) <=> (![H]: (r2_hidden(H, G) <=> ~(((((~(H = A) & ~(H = B)) & ~(H = C)) & ~(H = D)) & ~(H = E)) & ~(H = F)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_enumset1)).
% 3.11/1.48  tff(f_104, negated_conjecture, ~(![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_mcart_1)).
% 3.11/1.48  tff(f_94, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 3.11/1.48  tff(f_64, axiom, (![A, B, C]: ((k2_zfmisc_1(k1_tarski(A), k2_tarski(B, C)) = k2_tarski(k4_tarski(A, B), k4_tarski(A, C))) & (k2_zfmisc_1(k2_tarski(A, B), k1_tarski(C)) = k2_tarski(k4_tarski(A, C), k4_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_zfmisc_1)).
% 3.11/1.48  tff(f_31, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.11/1.48  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 3.11/1.48  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.11/1.48  tff(f_60, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 3.11/1.48  tff(f_49, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.11/1.48  tff(f_55, axiom, (![A, B]: ((r1_tarski(A, k2_zfmisc_1(A, B)) | r1_tarski(A, k2_zfmisc_1(B, A))) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t135_zfmisc_1)).
% 3.11/1.48  tff(c_8, plain, (![A_6]: (k2_tarski(A_6, A_6)=k1_tarski(A_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.11/1.48  tff(c_10, plain, (![A_7, B_8]: (k1_enumset1(A_7, A_7, B_8)=k2_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.11/1.48  tff(c_12, plain, (![A_9, B_10, C_11]: (k2_enumset1(A_9, A_9, B_10, C_11)=k1_enumset1(A_9, B_10, C_11))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.11/1.48  tff(c_14, plain, (![A_12, B_13, C_14, D_15]: (k3_enumset1(A_12, A_12, B_13, C_14, D_15)=k2_enumset1(A_12, B_13, C_14, D_15))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.11/1.48  tff(c_681, plain, (![C_245, E_242, A_243, D_244, B_241]: (k4_enumset1(A_243, A_243, B_241, C_245, D_244, E_242)=k3_enumset1(A_243, B_241, C_245, D_244, E_242))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.11/1.48  tff(c_48, plain, (![H_52, E_47, F_48, D_46, C_45, A_43]: (r2_hidden(H_52, k4_enumset1(A_43, H_52, C_45, D_46, E_47, F_48)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.11/1.48  tff(c_708, plain, (![B_249, A_250, D_248, E_247, C_246]: (r2_hidden(A_250, k3_enumset1(A_250, B_249, C_246, D_248, E_247)))), inference(superposition, [status(thm), theory('equality')], [c_681, c_48])).
% 3.11/1.48  tff(c_712, plain, (![A_251, B_252, C_253, D_254]: (r2_hidden(A_251, k2_enumset1(A_251, B_252, C_253, D_254)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_708])).
% 3.11/1.48  tff(c_716, plain, (![A_255, B_256, C_257]: (r2_hidden(A_255, k1_enumset1(A_255, B_256, C_257)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_712])).
% 3.11/1.48  tff(c_720, plain, (![A_258, B_259]: (r2_hidden(A_258, k2_tarski(A_258, B_259)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_716])).
% 3.11/1.48  tff(c_723, plain, (![A_6]: (r2_hidden(A_6, k1_tarski(A_6)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_720])).
% 3.11/1.48  tff(c_470, plain, (![B_149, D_152, C_153, E_150, A_151]: (k4_enumset1(A_151, A_151, B_149, C_153, D_152, E_150)=k3_enumset1(A_151, B_149, C_153, D_152, E_150))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.11/1.48  tff(c_46, plain, (![H_52, E_47, F_48, D_46, A_43, B_44]: (r2_hidden(H_52, k4_enumset1(A_43, B_44, H_52, D_46, E_47, F_48)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.11/1.48  tff(c_501, plain, (![A_155, D_156, B_158, C_157, E_154]: (r2_hidden(B_158, k3_enumset1(A_155, B_158, C_157, D_156, E_154)))), inference(superposition, [status(thm), theory('equality')], [c_470, c_46])).
% 3.11/1.48  tff(c_505, plain, (![A_159, B_160, C_161, D_162]: (r2_hidden(A_159, k2_enumset1(A_159, B_160, C_161, D_162)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_501])).
% 3.11/1.48  tff(c_518, plain, (![A_169, B_170, C_171]: (r2_hidden(A_169, k1_enumset1(A_169, B_170, C_171)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_505])).
% 3.11/1.48  tff(c_522, plain, (![A_172, B_173]: (r2_hidden(A_172, k2_tarski(A_172, B_173)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_518])).
% 3.11/1.48  tff(c_531, plain, (![A_6]: (r2_hidden(A_6, k1_tarski(A_6)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_522])).
% 3.11/1.48  tff(c_88, plain, (k4_tarski('#skF_4', '#skF_5')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.11/1.48  tff(c_118, plain, (![A_62, B_63]: (k1_mcart_1(k4_tarski(A_62, B_63))=A_62)), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.11/1.48  tff(c_127, plain, (k1_mcart_1('#skF_3')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_88, c_118])).
% 3.11/1.48  tff(c_130, plain, (![A_64, B_65]: (k2_mcart_1(k4_tarski(A_64, B_65))=B_65)), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.11/1.48  tff(c_139, plain, (k2_mcart_1('#skF_3')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_88, c_130])).
% 3.11/1.48  tff(c_86, plain, (k2_mcart_1('#skF_3')='#skF_3' | k1_mcart_1('#skF_3')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.11/1.48  tff(c_150, plain, ('#skF_5'='#skF_3' | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_127, c_139, c_86])).
% 3.11/1.48  tff(c_151, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_150])).
% 3.11/1.48  tff(c_154, plain, (k4_tarski('#skF_4', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_151, c_88])).
% 3.11/1.48  tff(c_301, plain, (![A_133, B_134, C_135]: (k2_zfmisc_1(k1_tarski(A_133), k2_tarski(B_134, C_135))=k2_tarski(k4_tarski(A_133, B_134), k4_tarski(A_133, C_135)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.11/1.48  tff(c_326, plain, (![A_133, C_135]: (k2_zfmisc_1(k1_tarski(A_133), k2_tarski(C_135, C_135))=k1_tarski(k4_tarski(A_133, C_135)))), inference(superposition, [status(thm), theory('equality')], [c_301, c_8])).
% 3.11/1.48  tff(c_351, plain, (![A_136, C_137]: (k2_zfmisc_1(k1_tarski(A_136), k1_tarski(C_137))=k1_tarski(k4_tarski(A_136, C_137)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_326])).
% 3.11/1.48  tff(c_6, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.11/1.48  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.11/1.48  tff(c_229, plain, (![A_80, B_81]: (k5_xboole_0(A_80, k3_xboole_0(A_80, B_81))=k4_xboole_0(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.11/1.48  tff(c_238, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_229])).
% 3.11/1.48  tff(c_241, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_238])).
% 3.11/1.48  tff(c_30, plain, (![B_39]: (k4_xboole_0(k1_tarski(B_39), k1_tarski(B_39))!=k1_tarski(B_39))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.11/1.48  tff(c_242, plain, (![B_39]: (k1_tarski(B_39)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_241, c_30])).
% 3.11/1.48  tff(c_24, plain, (![A_34, B_35]: (r1_tarski(k1_tarski(A_34), B_35) | ~r2_hidden(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.11/1.48  tff(c_223, plain, (![A_78, B_79]: (~r1_tarski(A_78, k2_zfmisc_1(A_78, B_79)) | k1_xboole_0=A_78)), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.11/1.48  tff(c_228, plain, (![A_34, B_79]: (k1_tarski(A_34)=k1_xboole_0 | ~r2_hidden(A_34, k2_zfmisc_1(k1_tarski(A_34), B_79)))), inference(resolution, [status(thm)], [c_24, c_223])).
% 3.11/1.48  tff(c_290, plain, (![A_34, B_79]: (~r2_hidden(A_34, k2_zfmisc_1(k1_tarski(A_34), B_79)))), inference(negUnitSimplification, [status(thm)], [c_242, c_228])).
% 3.11/1.48  tff(c_374, plain, (![A_138, C_139]: (~r2_hidden(A_138, k1_tarski(k4_tarski(A_138, C_139))))), inference(superposition, [status(thm), theory('equality')], [c_351, c_290])).
% 3.11/1.48  tff(c_377, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_154, c_374])).
% 3.11/1.48  tff(c_534, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_531, c_377])).
% 3.11/1.48  tff(c_535, plain, ('#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_150])).
% 3.11/1.48  tff(c_538, plain, (k4_tarski('#skF_4', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_535, c_88])).
% 3.11/1.48  tff(c_725, plain, (![A_261, B_262, C_263]: (k2_zfmisc_1(k2_tarski(A_261, B_262), k1_tarski(C_263))=k2_tarski(k4_tarski(A_261, C_263), k4_tarski(B_262, C_263)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.11/1.48  tff(c_765, plain, (![A_6, C_263]: (k2_zfmisc_1(k1_tarski(A_6), k1_tarski(C_263))=k2_tarski(k4_tarski(A_6, C_263), k4_tarski(A_6, C_263)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_725])).
% 3.11/1.48  tff(c_916, plain, (![A_320, C_321]: (k2_zfmisc_1(k1_tarski(A_320), k1_tarski(C_321))=k1_tarski(k4_tarski(A_320, C_321)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_765])).
% 3.11/1.48  tff(c_609, plain, (![A_188, B_189]: (k5_xboole_0(A_188, k3_xboole_0(A_188, B_189))=k4_xboole_0(A_188, B_189))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.11/1.48  tff(c_618, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_609])).
% 3.11/1.48  tff(c_621, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_618])).
% 3.11/1.48  tff(c_622, plain, (![B_39]: (k1_tarski(B_39)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_621, c_30])).
% 3.11/1.48  tff(c_582, plain, (![A_179, B_180]: (~r1_tarski(A_179, k2_zfmisc_1(B_180, A_179)) | k1_xboole_0=A_179)), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.11/1.48  tff(c_587, plain, (![A_34, B_180]: (k1_tarski(A_34)=k1_xboole_0 | ~r2_hidden(A_34, k2_zfmisc_1(B_180, k1_tarski(A_34))))), inference(resolution, [status(thm)], [c_24, c_582])).
% 3.11/1.48  tff(c_670, plain, (![A_34, B_180]: (~r2_hidden(A_34, k2_zfmisc_1(B_180, k1_tarski(A_34))))), inference(negUnitSimplification, [status(thm)], [c_622, c_587])).
% 3.11/1.48  tff(c_939, plain, (![C_322, A_323]: (~r2_hidden(C_322, k1_tarski(k4_tarski(A_323, C_322))))), inference(superposition, [status(thm), theory('equality')], [c_916, c_670])).
% 3.11/1.48  tff(c_942, plain, (~r2_hidden('#skF_3', k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_538, c_939])).
% 3.11/1.48  tff(c_945, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_723, c_942])).
% 3.11/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.11/1.48  
% 3.11/1.48  Inference rules
% 3.11/1.48  ----------------------
% 3.11/1.48  #Ref     : 0
% 3.11/1.48  #Sup     : 209
% 3.11/1.48  #Fact    : 0
% 3.11/1.48  #Define  : 0
% 3.11/1.48  #Split   : 1
% 3.11/1.48  #Chain   : 0
% 3.11/1.48  #Close   : 0
% 3.11/1.48  
% 3.11/1.48  Ordering : KBO
% 3.11/1.48  
% 3.11/1.48  Simplification rules
% 3.11/1.48  ----------------------
% 3.11/1.48  #Subsume      : 4
% 3.11/1.48  #Demod        : 47
% 3.11/1.48  #Tautology    : 114
% 3.11/1.48  #SimpNegUnit  : 16
% 3.11/1.48  #BackRed      : 8
% 3.11/1.48  
% 3.11/1.48  #Partial instantiations: 0
% 3.11/1.48  #Strategies tried      : 1
% 3.11/1.48  
% 3.11/1.48  Timing (in seconds)
% 3.11/1.48  ----------------------
% 3.11/1.48  Preprocessing        : 0.35
% 3.11/1.48  Parsing              : 0.17
% 3.11/1.48  CNF conversion       : 0.02
% 3.11/1.48  Main loop            : 0.36
% 3.11/1.48  Inferencing          : 0.13
% 3.11/1.48  Reduction            : 0.11
% 3.11/1.48  Demodulation         : 0.08
% 3.11/1.48  BG Simplification    : 0.03
% 3.11/1.48  Subsumption          : 0.07
% 3.11/1.48  Abstraction          : 0.03
% 3.11/1.48  MUC search           : 0.00
% 3.11/1.48  Cooper               : 0.00
% 3.11/1.48  Total                : 0.74
% 3.11/1.48  Index Insertion      : 0.00
% 3.11/1.48  Index Deletion       : 0.00
% 3.11/1.48  Index Matching       : 0.00
% 3.11/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
