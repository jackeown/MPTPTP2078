%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:16 EST 2020

% Result     : Theorem 3.11s
% Output     : CNFRefutation 3.29s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 135 expanded)
%              Number of leaves         :   43 (  65 expanded)
%              Depth                    :    8
%              Number of atoms          :   86 ( 158 expanded)
%              Number of equality atoms :   54 ( 120 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_mcart_1 > k1_tarski > k1_setfam_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_1 > #skF_4

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_35,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_37,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_90,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_enumset1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_106,negated_conjecture,(
    ~ ! [A] :
        ( ? [B,C] : A = k4_tarski(B,C)
       => ( A != k1_mcart_1(A)
          & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_96,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_66,axiom,(
    ! [A,B] : k2_zfmisc_1(k1_tarski(A),k1_tarski(B)) = k1_tarski(k4_tarski(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( r1_tarski(A,k2_zfmisc_1(A,B))
        | r1_tarski(A,k2_zfmisc_1(B,A)) )
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t135_zfmisc_1)).

tff(c_10,plain,(
    ! [A_8] : k2_tarski(A_8,A_8) = k1_tarski(A_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_9,B_10] : k1_enumset1(A_9,A_9,B_10) = k2_tarski(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [A_11,B_12,C_13] : k2_enumset1(A_11,A_11,B_12,C_13) = k1_enumset1(A_11,B_12,C_13) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ! [A_14,B_15,C_16,D_17] : k3_enumset1(A_14,A_14,B_15,C_16,D_17) = k2_enumset1(A_14,B_15,C_16,D_17) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_731,plain,(
    ! [A_258,B_262,C_259,D_261,E_260] : k4_enumset1(A_258,A_258,B_262,C_259,D_261,E_260) = k3_enumset1(A_258,B_262,C_259,D_261,E_260) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_48,plain,(
    ! [A_46,E_50,B_47,D_49,H_55,F_51] : r2_hidden(H_55,k4_enumset1(A_46,B_47,H_55,D_49,E_50,F_51)) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_758,plain,(
    ! [C_266,D_267,E_264,A_265,B_263] : r2_hidden(B_263,k3_enumset1(A_265,B_263,C_266,D_267,E_264)) ),
    inference(superposition,[status(thm),theory(equality)],[c_731,c_48])).

tff(c_771,plain,(
    ! [A_274,B_275,C_276,D_277] : r2_hidden(A_274,k2_enumset1(A_274,B_275,C_276,D_277)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_758])).

tff(c_775,plain,(
    ! [A_278,B_279,C_280] : r2_hidden(A_278,k1_enumset1(A_278,B_279,C_280)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_771])).

tff(c_779,plain,(
    ! [A_281,B_282] : r2_hidden(A_281,k2_tarski(A_281,B_282)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_775])).

tff(c_782,plain,(
    ! [A_8] : r2_hidden(A_8,k1_tarski(A_8)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_779])).

tff(c_26,plain,(
    ! [A_36,B_37] :
      ( r1_tarski(k1_tarski(A_36),B_37)
      | ~ r2_hidden(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_423,plain,(
    ! [A_152,D_155,B_156,C_153,E_154] : k4_enumset1(A_152,A_152,B_156,C_153,D_155,E_154) = k3_enumset1(A_152,B_156,C_153,D_155,E_154) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_459,plain,(
    ! [A_163,C_166,D_165,B_164,E_167] : r2_hidden(B_164,k3_enumset1(A_163,B_164,C_166,D_165,E_167)) ),
    inference(superposition,[status(thm),theory(equality)],[c_423,c_48])).

tff(c_463,plain,(
    ! [A_168,B_169,C_170,D_171] : r2_hidden(A_168,k2_enumset1(A_168,B_169,C_170,D_171)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_459])).

tff(c_467,plain,(
    ! [A_172,B_173,C_174] : r2_hidden(A_172,k1_enumset1(A_172,B_173,C_174)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_463])).

tff(c_471,plain,(
    ! [A_175,B_176] : r2_hidden(A_175,k2_tarski(A_175,B_176)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_467])).

tff(c_474,plain,(
    ! [A_8] : r2_hidden(A_8,k1_tarski(A_8)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_471])).

tff(c_90,plain,(
    k4_tarski('#skF_4','#skF_5') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_122,plain,(
    ! [A_65,B_66] : k1_mcart_1(k4_tarski(A_65,B_66)) = A_65 ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_131,plain,(
    k1_mcart_1('#skF_3') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_122])).

tff(c_134,plain,(
    ! [A_67,B_68] : k2_mcart_1(k4_tarski(A_67,B_68)) = B_68 ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_143,plain,(
    k2_mcart_1('#skF_3') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_134])).

tff(c_88,plain,
    ( k2_mcart_1('#skF_3') = '#skF_3'
    | k1_mcart_1('#skF_3') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_164,plain,
    ( '#skF_5' = '#skF_3'
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_143,c_88])).

tff(c_165,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_164])).

tff(c_168,plain,(
    k4_tarski('#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_90])).

tff(c_321,plain,(
    ! [A_103,B_104] : k2_zfmisc_1(k1_tarski(A_103),k1_tarski(B_104)) = k1_tarski(k4_tarski(A_103,B_104)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_6,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_154,plain,(
    ! [A_69,B_70] : k4_xboole_0(A_69,k2_xboole_0(A_69,B_70)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_161,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_154])).

tff(c_34,plain,(
    ! [B_43] : k4_xboole_0(k1_tarski(B_43),k1_tarski(B_43)) != k1_tarski(B_43) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_201,plain,(
    ! [B_43] : k1_tarski(B_43) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_34])).

tff(c_279,plain,(
    ! [A_88,B_89] :
      ( r1_tarski(k1_tarski(A_88),B_89)
      | ~ r2_hidden(A_88,B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_32,plain,(
    ! [A_40,B_41] :
      ( ~ r1_tarski(A_40,k2_zfmisc_1(A_40,B_41))
      | k1_xboole_0 = A_40 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_286,plain,(
    ! [A_88,B_41] :
      ( k1_tarski(A_88) = k1_xboole_0
      | ~ r2_hidden(A_88,k2_zfmisc_1(k1_tarski(A_88),B_41)) ) ),
    inference(resolution,[status(thm)],[c_279,c_32])).

tff(c_294,plain,(
    ! [A_88,B_41] : ~ r2_hidden(A_88,k2_zfmisc_1(k1_tarski(A_88),B_41)) ),
    inference(negUnitSimplification,[status(thm)],[c_201,c_286])).

tff(c_348,plain,(
    ! [A_107,B_108] : ~ r2_hidden(A_107,k1_tarski(k4_tarski(A_107,B_108))) ),
    inference(superposition,[status(thm),theory(equality)],[c_321,c_294])).

tff(c_351,plain,(
    ~ r2_hidden('#skF_4',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_348])).

tff(c_477,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_474,c_351])).

tff(c_478,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_164])).

tff(c_482,plain,(
    k4_tarski('#skF_4','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_478,c_90])).

tff(c_516,plain,(
    ! [B_43] : k1_tarski(B_43) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_34])).

tff(c_628,plain,(
    ! [A_213,B_214] : k2_zfmisc_1(k1_tarski(A_213),k1_tarski(B_214)) = k1_tarski(k4_tarski(A_213,B_214)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_30,plain,(
    ! [A_40,B_41] :
      ( ~ r1_tarski(A_40,k2_zfmisc_1(B_41,A_40))
      | k1_xboole_0 = A_40 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_640,plain,(
    ! [B_214,A_213] :
      ( ~ r1_tarski(k1_tarski(B_214),k1_tarski(k4_tarski(A_213,B_214)))
      | k1_tarski(B_214) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_628,c_30])).

tff(c_687,plain,(
    ! [B_221,A_222] : ~ r1_tarski(k1_tarski(B_221),k1_tarski(k4_tarski(A_222,B_221))) ),
    inference(negUnitSimplification,[status(thm)],[c_516,c_640])).

tff(c_690,plain,(
    ~ r1_tarski(k1_tarski('#skF_3'),k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_482,c_687])).

tff(c_699,plain,(
    ~ r2_hidden('#skF_3',k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_26,c_690])).

tff(c_794,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_782,c_699])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:36:59 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.11/1.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.11/1.44  
% 3.11/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.11/1.44  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_mcart_1 > k1_tarski > k1_setfam_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_1 > #skF_4
% 3.11/1.44  
% 3.11/1.44  %Foreground sorts:
% 3.11/1.44  
% 3.11/1.44  
% 3.11/1.44  %Background operators:
% 3.11/1.44  
% 3.11/1.44  
% 3.11/1.44  %Foreground operators:
% 3.11/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.11/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.11/1.44  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.11/1.44  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.11/1.44  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.11/1.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.11/1.44  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.11/1.44  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.11/1.44  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.11/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.11/1.44  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.11/1.44  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.11/1.44  tff('#skF_5', type, '#skF_5': $i).
% 3.11/1.44  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.11/1.44  tff('#skF_3', type, '#skF_3': $i).
% 3.11/1.44  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.11/1.44  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.11/1.44  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.11/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.11/1.44  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 3.11/1.44  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.11/1.44  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.11/1.44  tff('#skF_4', type, '#skF_4': $i).
% 3.11/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.11/1.44  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 3.11/1.44  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.11/1.44  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.11/1.44  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.11/1.44  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.11/1.44  
% 3.29/1.46  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.29/1.46  tff(f_37, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.29/1.46  tff(f_39, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 3.29/1.46  tff(f_41, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 3.29/1.46  tff(f_43, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 3.29/1.46  tff(f_90, axiom, (![A, B, C, D, E, F, G]: ((G = k4_enumset1(A, B, C, D, E, F)) <=> (![H]: (r2_hidden(H, G) <=> ~(((((~(H = A) & ~(H = B)) & ~(H = C)) & ~(H = D)) & ~(H = E)) & ~(H = F)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_enumset1)).
% 3.29/1.46  tff(f_51, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.29/1.46  tff(f_106, negated_conjecture, ~(![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_mcart_1)).
% 3.29/1.46  tff(f_96, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 3.29/1.46  tff(f_66, axiom, (![A, B]: (k2_zfmisc_1(k1_tarski(A), k1_tarski(B)) = k1_tarski(k4_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_zfmisc_1)).
% 3.29/1.46  tff(f_31, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 3.29/1.46  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 3.29/1.46  tff(f_64, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 3.29/1.46  tff(f_59, axiom, (![A, B]: ((r1_tarski(A, k2_zfmisc_1(A, B)) | r1_tarski(A, k2_zfmisc_1(B, A))) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t135_zfmisc_1)).
% 3.29/1.46  tff(c_10, plain, (![A_8]: (k2_tarski(A_8, A_8)=k1_tarski(A_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.29/1.46  tff(c_12, plain, (![A_9, B_10]: (k1_enumset1(A_9, A_9, B_10)=k2_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.29/1.46  tff(c_14, plain, (![A_11, B_12, C_13]: (k2_enumset1(A_11, A_11, B_12, C_13)=k1_enumset1(A_11, B_12, C_13))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.29/1.46  tff(c_16, plain, (![A_14, B_15, C_16, D_17]: (k3_enumset1(A_14, A_14, B_15, C_16, D_17)=k2_enumset1(A_14, B_15, C_16, D_17))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.29/1.46  tff(c_731, plain, (![A_258, B_262, C_259, D_261, E_260]: (k4_enumset1(A_258, A_258, B_262, C_259, D_261, E_260)=k3_enumset1(A_258, B_262, C_259, D_261, E_260))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.29/1.46  tff(c_48, plain, (![A_46, E_50, B_47, D_49, H_55, F_51]: (r2_hidden(H_55, k4_enumset1(A_46, B_47, H_55, D_49, E_50, F_51)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.29/1.46  tff(c_758, plain, (![C_266, D_267, E_264, A_265, B_263]: (r2_hidden(B_263, k3_enumset1(A_265, B_263, C_266, D_267, E_264)))), inference(superposition, [status(thm), theory('equality')], [c_731, c_48])).
% 3.29/1.46  tff(c_771, plain, (![A_274, B_275, C_276, D_277]: (r2_hidden(A_274, k2_enumset1(A_274, B_275, C_276, D_277)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_758])).
% 3.29/1.46  tff(c_775, plain, (![A_278, B_279, C_280]: (r2_hidden(A_278, k1_enumset1(A_278, B_279, C_280)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_771])).
% 3.29/1.46  tff(c_779, plain, (![A_281, B_282]: (r2_hidden(A_281, k2_tarski(A_281, B_282)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_775])).
% 3.29/1.46  tff(c_782, plain, (![A_8]: (r2_hidden(A_8, k1_tarski(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_779])).
% 3.29/1.46  tff(c_26, plain, (![A_36, B_37]: (r1_tarski(k1_tarski(A_36), B_37) | ~r2_hidden(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.29/1.46  tff(c_423, plain, (![A_152, D_155, B_156, C_153, E_154]: (k4_enumset1(A_152, A_152, B_156, C_153, D_155, E_154)=k3_enumset1(A_152, B_156, C_153, D_155, E_154))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.29/1.46  tff(c_459, plain, (![A_163, C_166, D_165, B_164, E_167]: (r2_hidden(B_164, k3_enumset1(A_163, B_164, C_166, D_165, E_167)))), inference(superposition, [status(thm), theory('equality')], [c_423, c_48])).
% 3.29/1.46  tff(c_463, plain, (![A_168, B_169, C_170, D_171]: (r2_hidden(A_168, k2_enumset1(A_168, B_169, C_170, D_171)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_459])).
% 3.29/1.46  tff(c_467, plain, (![A_172, B_173, C_174]: (r2_hidden(A_172, k1_enumset1(A_172, B_173, C_174)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_463])).
% 3.29/1.46  tff(c_471, plain, (![A_175, B_176]: (r2_hidden(A_175, k2_tarski(A_175, B_176)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_467])).
% 3.29/1.46  tff(c_474, plain, (![A_8]: (r2_hidden(A_8, k1_tarski(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_471])).
% 3.29/1.46  tff(c_90, plain, (k4_tarski('#skF_4', '#skF_5')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.29/1.46  tff(c_122, plain, (![A_65, B_66]: (k1_mcart_1(k4_tarski(A_65, B_66))=A_65)), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.29/1.46  tff(c_131, plain, (k1_mcart_1('#skF_3')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_90, c_122])).
% 3.29/1.46  tff(c_134, plain, (![A_67, B_68]: (k2_mcart_1(k4_tarski(A_67, B_68))=B_68)), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.29/1.46  tff(c_143, plain, (k2_mcart_1('#skF_3')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_90, c_134])).
% 3.29/1.46  tff(c_88, plain, (k2_mcart_1('#skF_3')='#skF_3' | k1_mcart_1('#skF_3')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.29/1.46  tff(c_164, plain, ('#skF_5'='#skF_3' | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_131, c_143, c_88])).
% 3.29/1.46  tff(c_165, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_164])).
% 3.29/1.46  tff(c_168, plain, (k4_tarski('#skF_4', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_165, c_90])).
% 3.29/1.46  tff(c_321, plain, (![A_103, B_104]: (k2_zfmisc_1(k1_tarski(A_103), k1_tarski(B_104))=k1_tarski(k4_tarski(A_103, B_104)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.29/1.46  tff(c_6, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.29/1.46  tff(c_154, plain, (![A_69, B_70]: (k4_xboole_0(A_69, k2_xboole_0(A_69, B_70))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.29/1.46  tff(c_161, plain, (![A_5]: (k4_xboole_0(A_5, A_5)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6, c_154])).
% 3.29/1.46  tff(c_34, plain, (![B_43]: (k4_xboole_0(k1_tarski(B_43), k1_tarski(B_43))!=k1_tarski(B_43))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.29/1.46  tff(c_201, plain, (![B_43]: (k1_tarski(B_43)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_161, c_34])).
% 3.29/1.46  tff(c_279, plain, (![A_88, B_89]: (r1_tarski(k1_tarski(A_88), B_89) | ~r2_hidden(A_88, B_89))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.29/1.46  tff(c_32, plain, (![A_40, B_41]: (~r1_tarski(A_40, k2_zfmisc_1(A_40, B_41)) | k1_xboole_0=A_40)), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.29/1.46  tff(c_286, plain, (![A_88, B_41]: (k1_tarski(A_88)=k1_xboole_0 | ~r2_hidden(A_88, k2_zfmisc_1(k1_tarski(A_88), B_41)))), inference(resolution, [status(thm)], [c_279, c_32])).
% 3.29/1.46  tff(c_294, plain, (![A_88, B_41]: (~r2_hidden(A_88, k2_zfmisc_1(k1_tarski(A_88), B_41)))), inference(negUnitSimplification, [status(thm)], [c_201, c_286])).
% 3.29/1.46  tff(c_348, plain, (![A_107, B_108]: (~r2_hidden(A_107, k1_tarski(k4_tarski(A_107, B_108))))), inference(superposition, [status(thm), theory('equality')], [c_321, c_294])).
% 3.29/1.46  tff(c_351, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_168, c_348])).
% 3.29/1.46  tff(c_477, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_474, c_351])).
% 3.29/1.46  tff(c_478, plain, ('#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_164])).
% 3.29/1.46  tff(c_482, plain, (k4_tarski('#skF_4', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_478, c_90])).
% 3.29/1.46  tff(c_516, plain, (![B_43]: (k1_tarski(B_43)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_161, c_34])).
% 3.29/1.46  tff(c_628, plain, (![A_213, B_214]: (k2_zfmisc_1(k1_tarski(A_213), k1_tarski(B_214))=k1_tarski(k4_tarski(A_213, B_214)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.29/1.46  tff(c_30, plain, (![A_40, B_41]: (~r1_tarski(A_40, k2_zfmisc_1(B_41, A_40)) | k1_xboole_0=A_40)), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.29/1.46  tff(c_640, plain, (![B_214, A_213]: (~r1_tarski(k1_tarski(B_214), k1_tarski(k4_tarski(A_213, B_214))) | k1_tarski(B_214)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_628, c_30])).
% 3.29/1.46  tff(c_687, plain, (![B_221, A_222]: (~r1_tarski(k1_tarski(B_221), k1_tarski(k4_tarski(A_222, B_221))))), inference(negUnitSimplification, [status(thm)], [c_516, c_640])).
% 3.29/1.46  tff(c_690, plain, (~r1_tarski(k1_tarski('#skF_3'), k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_482, c_687])).
% 3.29/1.46  tff(c_699, plain, (~r2_hidden('#skF_3', k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_26, c_690])).
% 3.29/1.46  tff(c_794, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_782, c_699])).
% 3.29/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.29/1.46  
% 3.29/1.46  Inference rules
% 3.29/1.46  ----------------------
% 3.29/1.46  #Ref     : 0
% 3.29/1.46  #Sup     : 169
% 3.29/1.46  #Fact    : 0
% 3.29/1.46  #Define  : 0
% 3.29/1.46  #Split   : 1
% 3.29/1.46  #Chain   : 0
% 3.29/1.46  #Close   : 0
% 3.29/1.46  
% 3.29/1.46  Ordering : KBO
% 3.29/1.46  
% 3.29/1.46  Simplification rules
% 3.29/1.46  ----------------------
% 3.29/1.46  #Subsume      : 8
% 3.29/1.46  #Demod        : 21
% 3.29/1.46  #Tautology    : 110
% 3.29/1.46  #SimpNegUnit  : 12
% 3.29/1.46  #BackRed      : 7
% 3.29/1.46  
% 3.29/1.46  #Partial instantiations: 0
% 3.29/1.46  #Strategies tried      : 1
% 3.29/1.46  
% 3.29/1.46  Timing (in seconds)
% 3.29/1.46  ----------------------
% 3.29/1.46  Preprocessing        : 0.36
% 3.29/1.46  Parsing              : 0.18
% 3.29/1.46  CNF conversion       : 0.03
% 3.29/1.46  Main loop            : 0.32
% 3.29/1.46  Inferencing          : 0.12
% 3.29/1.46  Reduction            : 0.09
% 3.29/1.46  Demodulation         : 0.06
% 3.29/1.46  BG Simplification    : 0.02
% 3.29/1.46  Subsumption          : 0.07
% 3.29/1.46  Abstraction          : 0.02
% 3.29/1.46  MUC search           : 0.00
% 3.29/1.47  Cooper               : 0.00
% 3.29/1.47  Total                : 0.72
% 3.29/1.47  Index Insertion      : 0.00
% 3.29/1.47  Index Deletion       : 0.00
% 3.29/1.47  Index Matching       : 0.00
% 3.29/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
