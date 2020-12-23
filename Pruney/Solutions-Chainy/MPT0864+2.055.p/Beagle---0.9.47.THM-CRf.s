%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:16 EST 2020

% Result     : Theorem 3.12s
% Output     : CNFRefutation 3.12s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 208 expanded)
%              Number of leaves         :   45 (  89 expanded)
%              Depth                    :   10
%              Number of atoms          :  116 ( 283 expanded)
%              Number of equality atoms :   63 ( 200 expanded)
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

tff(f_94,axiom,(
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

tff(f_35,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_37,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_110,negated_conjecture,(
    ~ ! [A] :
        ( ? [B,C] : A = k4_tarski(B,C)
       => ( A != k1_mcart_1(A)
          & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_100,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_59,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_70,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( r1_tarski(A,k2_zfmisc_1(A,B))
        | r1_tarski(A,k2_zfmisc_1(B,A)) )
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t135_zfmisc_1)).

tff(c_56,plain,(
    ! [H_58,D_52,C_51,F_54,B_50,E_53] : r2_hidden(H_58,k4_enumset1(H_58,B_50,C_51,D_52,E_53,F_54)) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_10,plain,(
    ! [A_9] : k2_tarski(A_9,A_9) = k1_tarski(A_9) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_10,B_11] : k1_enumset1(A_10,A_10,B_11) = k2_tarski(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [A_12,B_13,C_14] : k2_enumset1(A_12,A_12,B_13,C_14) = k1_enumset1(A_12,B_13,C_14) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ! [A_15,B_16,C_17,D_18] : k3_enumset1(A_15,A_15,B_16,C_17,D_18) = k2_enumset1(A_15,B_16,C_17,D_18) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_853,plain,(
    ! [A_312,D_313,B_311,E_310,C_309] : k4_enumset1(A_312,A_312,B_311,C_309,D_313,E_310) = k3_enumset1(A_312,B_311,C_309,D_313,E_310) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_52,plain,(
    ! [H_58,D_52,F_54,B_50,A_49,E_53] : r2_hidden(H_58,k4_enumset1(A_49,B_50,H_58,D_52,E_53,F_54)) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_899,plain,(
    ! [E_319,A_318,D_316,C_317,B_320] : r2_hidden(B_320,k3_enumset1(A_318,B_320,C_317,D_316,E_319)) ),
    inference(superposition,[status(thm),theory(equality)],[c_853,c_52])).

tff(c_903,plain,(
    ! [A_321,B_322,C_323,D_324] : r2_hidden(A_321,k2_enumset1(A_321,B_322,C_323,D_324)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_899])).

tff(c_907,plain,(
    ! [A_325,B_326,C_327] : r2_hidden(A_325,k1_enumset1(A_325,B_326,C_327)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_903])).

tff(c_911,plain,(
    ! [A_328,B_329] : r2_hidden(A_328,k2_tarski(A_328,B_329)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_907])).

tff(c_914,plain,(
    ! [A_9] : r2_hidden(A_9,k1_tarski(A_9)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_911])).

tff(c_401,plain,(
    ! [A_163,C_160,B_162,D_164,E_161] : k4_enumset1(A_163,A_163,B_162,C_160,D_164,E_161) = k3_enumset1(A_163,B_162,C_160,D_164,E_161) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_48,plain,(
    ! [H_58,D_52,C_51,F_54,B_50,A_49] : r2_hidden(H_58,k4_enumset1(A_49,B_50,C_51,D_52,H_58,F_54)) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_419,plain,(
    ! [A_163,C_160,B_162,D_164,E_161] : r2_hidden(D_164,k3_enumset1(A_163,B_162,C_160,D_164,E_161)) ),
    inference(superposition,[status(thm),theory(equality)],[c_401,c_48])).

tff(c_428,plain,(
    ! [C_169,D_166,E_167,B_165,A_168] : r2_hidden(A_168,k3_enumset1(A_168,B_165,C_169,D_166,E_167)) ),
    inference(superposition,[status(thm),theory(equality)],[c_401,c_56])).

tff(c_432,plain,(
    ! [A_170,B_171,C_172,D_173] : r2_hidden(A_170,k2_enumset1(A_170,B_171,C_172,D_173)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_428])).

tff(c_458,plain,(
    ! [A_178,B_179,C_180] : r2_hidden(A_178,k1_enumset1(A_178,B_179,C_180)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_432])).

tff(c_462,plain,(
    ! [A_181,B_182] : r2_hidden(A_181,k2_tarski(A_181,B_182)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_458])).

tff(c_465,plain,(
    ! [A_9] : r2_hidden(A_9,k1_tarski(A_9)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_462])).

tff(c_94,plain,(
    k4_tarski('#skF_4','#skF_5') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_108,plain,(
    ! [A_66,B_67] : k1_mcart_1(k4_tarski(A_66,B_67)) = A_66 ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_117,plain,(
    k1_mcart_1('#skF_3') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_108])).

tff(c_133,plain,(
    ! [A_69,B_70] : k2_mcart_1(k4_tarski(A_69,B_70)) = B_70 ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_142,plain,(
    k2_mcart_1('#skF_3') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_133])).

tff(c_92,plain,
    ( k2_mcart_1('#skF_3') = '#skF_3'
    | k1_mcart_1('#skF_3') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_165,plain,
    ( '#skF_5' = '#skF_3'
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_142,c_92])).

tff(c_166,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_165])).

tff(c_169,plain,(
    k4_tarski('#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_94])).

tff(c_436,plain,(
    ! [A_174,B_175,C_176,D_177] :
      ( r2_hidden(k4_tarski(A_174,B_175),k2_zfmisc_1(C_176,D_177))
      | ~ r2_hidden(B_175,D_177)
      | ~ r2_hidden(A_174,C_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_497,plain,(
    ! [C_209,D_210] :
      ( r2_hidden('#skF_4',k2_zfmisc_1(C_209,D_210))
      | ~ r2_hidden('#skF_5',D_210)
      | ~ r2_hidden('#skF_4',C_209) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_436])).

tff(c_8,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k2_xboole_0(A_7,B_8)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [A_5,B_6] : k3_xboole_0(A_5,k2_xboole_0(A_5,B_6)) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_303,plain,(
    ! [A_94,B_95] : k5_xboole_0(A_94,k3_xboole_0(A_94,B_95)) = k4_xboole_0(A_94,B_95) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_315,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k2_xboole_0(A_5,B_6)) = k5_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_303])).

tff(c_322,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_315])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_318,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_303])).

tff(c_332,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_322,c_318])).

tff(c_40,plain,(
    ! [B_48] : k4_xboole_0(k1_tarski(B_48),k1_tarski(B_48)) != k1_tarski(B_48) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_333,plain,(
    ! [B_48] : k1_tarski(B_48) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_332,c_40])).

tff(c_26,plain,(
    ! [A_37,B_38] :
      ( r1_tarski(k1_tarski(A_37),B_38)
      | ~ r2_hidden(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_222,plain,(
    ! [A_82,B_83] :
      ( ~ r1_tarski(A_82,k2_zfmisc_1(A_82,B_83))
      | k1_xboole_0 = A_82 ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_227,plain,(
    ! [A_37,B_83] :
      ( k1_tarski(A_37) = k1_xboole_0
      | ~ r2_hidden(A_37,k2_zfmisc_1(k1_tarski(A_37),B_83)) ) ),
    inference(resolution,[status(thm)],[c_26,c_222])).

tff(c_385,plain,(
    ! [A_37,B_83] : ~ r2_hidden(A_37,k2_zfmisc_1(k1_tarski(A_37),B_83)) ),
    inference(negUnitSimplification,[status(thm)],[c_333,c_227])).

tff(c_504,plain,(
    ! [D_210] :
      ( ~ r2_hidden('#skF_5',D_210)
      | ~ r2_hidden('#skF_4',k1_tarski('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_497,c_385])).

tff(c_519,plain,(
    ! [D_211] : ~ r2_hidden('#skF_5',D_211) ),
    inference(demodulation,[status(thm),theory(equality)],[c_465,c_504])).

tff(c_569,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_419,c_519])).

tff(c_570,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_165])).

tff(c_573,plain,(
    k4_tarski('#skF_4','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_570,c_94])).

tff(c_801,plain,(
    ! [A_297,B_298,C_299,D_300] :
      ( r2_hidden(k4_tarski(A_297,B_298),k2_zfmisc_1(C_299,D_300))
      | ~ r2_hidden(B_298,D_300)
      | ~ r2_hidden(A_297,C_299) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_679,plain,(
    ! [A_229,B_230] : k5_xboole_0(A_229,k3_xboole_0(A_229,B_230)) = k4_xboole_0(A_229,B_230) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_688,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k2_xboole_0(A_5,B_6)) = k5_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_679])).

tff(c_694,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_688])).

tff(c_691,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_679])).

tff(c_702,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_694,c_691])).

tff(c_703,plain,(
    ! [B_48] : k1_tarski(B_48) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_702,c_40])).

tff(c_597,plain,(
    ! [A_218,B_219] :
      ( r1_tarski(k1_tarski(A_218),B_219)
      | ~ r2_hidden(A_218,B_219) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_36,plain,(
    ! [A_45,B_46] :
      ( ~ r1_tarski(A_45,k2_zfmisc_1(B_46,A_45))
      | k1_xboole_0 = A_45 ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_610,plain,(
    ! [A_218,B_46] :
      ( k1_tarski(A_218) = k1_xboole_0
      | ~ r2_hidden(A_218,k2_zfmisc_1(B_46,k1_tarski(A_218))) ) ),
    inference(resolution,[status(thm)],[c_597,c_36])).

tff(c_780,plain,(
    ! [A_218,B_46] : ~ r2_hidden(A_218,k2_zfmisc_1(B_46,k1_tarski(A_218))) ),
    inference(negUnitSimplification,[status(thm)],[c_703,c_610])).

tff(c_823,plain,(
    ! [B_301,A_302,C_303] :
      ( ~ r2_hidden(B_301,k1_tarski(k4_tarski(A_302,B_301)))
      | ~ r2_hidden(A_302,C_303) ) ),
    inference(resolution,[status(thm)],[c_801,c_780])).

tff(c_825,plain,(
    ! [C_303] :
      ( ~ r2_hidden('#skF_3',k1_tarski('#skF_3'))
      | ~ r2_hidden('#skF_4',C_303) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_573,c_823])).

tff(c_826,plain,(
    ~ r2_hidden('#skF_3',k1_tarski('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_825])).

tff(c_926,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_914,c_826])).

tff(c_930,plain,(
    ! [C_336] : ~ r2_hidden('#skF_4',C_336) ),
    inference(splitRight,[status(thm)],[c_825])).

tff(c_950,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_56,c_930])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:43:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.12/1.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.12/1.47  
% 3.12/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.12/1.47  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_mcart_1 > k1_tarski > k1_setfam_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_1 > #skF_4
% 3.12/1.47  
% 3.12/1.47  %Foreground sorts:
% 3.12/1.47  
% 3.12/1.47  
% 3.12/1.47  %Background operators:
% 3.12/1.47  
% 3.12/1.47  
% 3.12/1.47  %Foreground operators:
% 3.12/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.12/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.12/1.47  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.12/1.47  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.12/1.47  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.12/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.12/1.47  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.12/1.47  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.12/1.47  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.12/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.12/1.47  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.12/1.47  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.12/1.47  tff('#skF_5', type, '#skF_5': $i).
% 3.12/1.47  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.12/1.47  tff('#skF_3', type, '#skF_3': $i).
% 3.12/1.47  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.12/1.47  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.12/1.47  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.12/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.12/1.47  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 3.12/1.47  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.12/1.47  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.12/1.47  tff('#skF_4', type, '#skF_4': $i).
% 3.12/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.12/1.47  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 3.12/1.47  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.12/1.47  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.12/1.47  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.12/1.47  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.12/1.47  
% 3.12/1.49  tff(f_94, axiom, (![A, B, C, D, E, F, G]: ((G = k4_enumset1(A, B, C, D, E, F)) <=> (![H]: (r2_hidden(H, G) <=> ~(((((~(H = A) & ~(H = B)) & ~(H = C)) & ~(H = D)) & ~(H = E)) & ~(H = F)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_enumset1)).
% 3.12/1.49  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.12/1.49  tff(f_37, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.12/1.49  tff(f_39, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 3.12/1.49  tff(f_41, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 3.12/1.49  tff(f_43, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 3.12/1.49  tff(f_110, negated_conjecture, ~(![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_mcart_1)).
% 3.12/1.49  tff(f_100, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 3.12/1.49  tff(f_59, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 3.12/1.49  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 3.12/1.49  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 3.12/1.49  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.12/1.49  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 3.12/1.49  tff(f_70, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 3.12/1.49  tff(f_51, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.12/1.49  tff(f_65, axiom, (![A, B]: ((r1_tarski(A, k2_zfmisc_1(A, B)) | r1_tarski(A, k2_zfmisc_1(B, A))) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t135_zfmisc_1)).
% 3.12/1.49  tff(c_56, plain, (![H_58, D_52, C_51, F_54, B_50, E_53]: (r2_hidden(H_58, k4_enumset1(H_58, B_50, C_51, D_52, E_53, F_54)))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.12/1.49  tff(c_10, plain, (![A_9]: (k2_tarski(A_9, A_9)=k1_tarski(A_9))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.12/1.49  tff(c_12, plain, (![A_10, B_11]: (k1_enumset1(A_10, A_10, B_11)=k2_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.12/1.49  tff(c_14, plain, (![A_12, B_13, C_14]: (k2_enumset1(A_12, A_12, B_13, C_14)=k1_enumset1(A_12, B_13, C_14))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.12/1.49  tff(c_16, plain, (![A_15, B_16, C_17, D_18]: (k3_enumset1(A_15, A_15, B_16, C_17, D_18)=k2_enumset1(A_15, B_16, C_17, D_18))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.12/1.49  tff(c_853, plain, (![A_312, D_313, B_311, E_310, C_309]: (k4_enumset1(A_312, A_312, B_311, C_309, D_313, E_310)=k3_enumset1(A_312, B_311, C_309, D_313, E_310))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.12/1.49  tff(c_52, plain, (![H_58, D_52, F_54, B_50, A_49, E_53]: (r2_hidden(H_58, k4_enumset1(A_49, B_50, H_58, D_52, E_53, F_54)))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.12/1.49  tff(c_899, plain, (![E_319, A_318, D_316, C_317, B_320]: (r2_hidden(B_320, k3_enumset1(A_318, B_320, C_317, D_316, E_319)))), inference(superposition, [status(thm), theory('equality')], [c_853, c_52])).
% 3.12/1.49  tff(c_903, plain, (![A_321, B_322, C_323, D_324]: (r2_hidden(A_321, k2_enumset1(A_321, B_322, C_323, D_324)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_899])).
% 3.12/1.49  tff(c_907, plain, (![A_325, B_326, C_327]: (r2_hidden(A_325, k1_enumset1(A_325, B_326, C_327)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_903])).
% 3.12/1.49  tff(c_911, plain, (![A_328, B_329]: (r2_hidden(A_328, k2_tarski(A_328, B_329)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_907])).
% 3.12/1.49  tff(c_914, plain, (![A_9]: (r2_hidden(A_9, k1_tarski(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_911])).
% 3.12/1.49  tff(c_401, plain, (![A_163, C_160, B_162, D_164, E_161]: (k4_enumset1(A_163, A_163, B_162, C_160, D_164, E_161)=k3_enumset1(A_163, B_162, C_160, D_164, E_161))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.12/1.49  tff(c_48, plain, (![H_58, D_52, C_51, F_54, B_50, A_49]: (r2_hidden(H_58, k4_enumset1(A_49, B_50, C_51, D_52, H_58, F_54)))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.12/1.49  tff(c_419, plain, (![A_163, C_160, B_162, D_164, E_161]: (r2_hidden(D_164, k3_enumset1(A_163, B_162, C_160, D_164, E_161)))), inference(superposition, [status(thm), theory('equality')], [c_401, c_48])).
% 3.12/1.49  tff(c_428, plain, (![C_169, D_166, E_167, B_165, A_168]: (r2_hidden(A_168, k3_enumset1(A_168, B_165, C_169, D_166, E_167)))), inference(superposition, [status(thm), theory('equality')], [c_401, c_56])).
% 3.12/1.49  tff(c_432, plain, (![A_170, B_171, C_172, D_173]: (r2_hidden(A_170, k2_enumset1(A_170, B_171, C_172, D_173)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_428])).
% 3.12/1.49  tff(c_458, plain, (![A_178, B_179, C_180]: (r2_hidden(A_178, k1_enumset1(A_178, B_179, C_180)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_432])).
% 3.12/1.49  tff(c_462, plain, (![A_181, B_182]: (r2_hidden(A_181, k2_tarski(A_181, B_182)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_458])).
% 3.12/1.49  tff(c_465, plain, (![A_9]: (r2_hidden(A_9, k1_tarski(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_462])).
% 3.12/1.49  tff(c_94, plain, (k4_tarski('#skF_4', '#skF_5')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.12/1.49  tff(c_108, plain, (![A_66, B_67]: (k1_mcart_1(k4_tarski(A_66, B_67))=A_66)), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.12/1.49  tff(c_117, plain, (k1_mcart_1('#skF_3')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_94, c_108])).
% 3.12/1.49  tff(c_133, plain, (![A_69, B_70]: (k2_mcart_1(k4_tarski(A_69, B_70))=B_70)), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.12/1.49  tff(c_142, plain, (k2_mcart_1('#skF_3')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_94, c_133])).
% 3.12/1.49  tff(c_92, plain, (k2_mcart_1('#skF_3')='#skF_3' | k1_mcart_1('#skF_3')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.12/1.49  tff(c_165, plain, ('#skF_5'='#skF_3' | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_117, c_142, c_92])).
% 3.12/1.49  tff(c_166, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_165])).
% 3.12/1.49  tff(c_169, plain, (k4_tarski('#skF_4', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_166, c_94])).
% 3.12/1.49  tff(c_436, plain, (![A_174, B_175, C_176, D_177]: (r2_hidden(k4_tarski(A_174, B_175), k2_zfmisc_1(C_176, D_177)) | ~r2_hidden(B_175, D_177) | ~r2_hidden(A_174, C_176))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.12/1.49  tff(c_497, plain, (![C_209, D_210]: (r2_hidden('#skF_4', k2_zfmisc_1(C_209, D_210)) | ~r2_hidden('#skF_5', D_210) | ~r2_hidden('#skF_4', C_209))), inference(superposition, [status(thm), theory('equality')], [c_169, c_436])).
% 3.12/1.49  tff(c_8, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k2_xboole_0(A_7, B_8))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.12/1.49  tff(c_6, plain, (![A_5, B_6]: (k3_xboole_0(A_5, k2_xboole_0(A_5, B_6))=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.12/1.49  tff(c_303, plain, (![A_94, B_95]: (k5_xboole_0(A_94, k3_xboole_0(A_94, B_95))=k4_xboole_0(A_94, B_95))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.12/1.49  tff(c_315, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k2_xboole_0(A_5, B_6))=k5_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_303])).
% 3.12/1.49  tff(c_322, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_315])).
% 3.12/1.49  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.12/1.49  tff(c_318, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_303])).
% 3.12/1.49  tff(c_332, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_322, c_318])).
% 3.12/1.49  tff(c_40, plain, (![B_48]: (k4_xboole_0(k1_tarski(B_48), k1_tarski(B_48))!=k1_tarski(B_48))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.12/1.49  tff(c_333, plain, (![B_48]: (k1_tarski(B_48)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_332, c_40])).
% 3.12/1.49  tff(c_26, plain, (![A_37, B_38]: (r1_tarski(k1_tarski(A_37), B_38) | ~r2_hidden(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.12/1.49  tff(c_222, plain, (![A_82, B_83]: (~r1_tarski(A_82, k2_zfmisc_1(A_82, B_83)) | k1_xboole_0=A_82)), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.12/1.49  tff(c_227, plain, (![A_37, B_83]: (k1_tarski(A_37)=k1_xboole_0 | ~r2_hidden(A_37, k2_zfmisc_1(k1_tarski(A_37), B_83)))), inference(resolution, [status(thm)], [c_26, c_222])).
% 3.12/1.49  tff(c_385, plain, (![A_37, B_83]: (~r2_hidden(A_37, k2_zfmisc_1(k1_tarski(A_37), B_83)))), inference(negUnitSimplification, [status(thm)], [c_333, c_227])).
% 3.12/1.49  tff(c_504, plain, (![D_210]: (~r2_hidden('#skF_5', D_210) | ~r2_hidden('#skF_4', k1_tarski('#skF_4')))), inference(resolution, [status(thm)], [c_497, c_385])).
% 3.12/1.49  tff(c_519, plain, (![D_211]: (~r2_hidden('#skF_5', D_211))), inference(demodulation, [status(thm), theory('equality')], [c_465, c_504])).
% 3.12/1.49  tff(c_569, plain, $false, inference(resolution, [status(thm)], [c_419, c_519])).
% 3.12/1.49  tff(c_570, plain, ('#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_165])).
% 3.12/1.49  tff(c_573, plain, (k4_tarski('#skF_4', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_570, c_94])).
% 3.12/1.49  tff(c_801, plain, (![A_297, B_298, C_299, D_300]: (r2_hidden(k4_tarski(A_297, B_298), k2_zfmisc_1(C_299, D_300)) | ~r2_hidden(B_298, D_300) | ~r2_hidden(A_297, C_299))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.12/1.49  tff(c_679, plain, (![A_229, B_230]: (k5_xboole_0(A_229, k3_xboole_0(A_229, B_230))=k4_xboole_0(A_229, B_230))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.12/1.49  tff(c_688, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k2_xboole_0(A_5, B_6))=k5_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_679])).
% 3.12/1.49  tff(c_694, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_688])).
% 3.12/1.49  tff(c_691, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_679])).
% 3.12/1.49  tff(c_702, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_694, c_691])).
% 3.12/1.49  tff(c_703, plain, (![B_48]: (k1_tarski(B_48)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_702, c_40])).
% 3.12/1.49  tff(c_597, plain, (![A_218, B_219]: (r1_tarski(k1_tarski(A_218), B_219) | ~r2_hidden(A_218, B_219))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.12/1.49  tff(c_36, plain, (![A_45, B_46]: (~r1_tarski(A_45, k2_zfmisc_1(B_46, A_45)) | k1_xboole_0=A_45)), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.12/1.49  tff(c_610, plain, (![A_218, B_46]: (k1_tarski(A_218)=k1_xboole_0 | ~r2_hidden(A_218, k2_zfmisc_1(B_46, k1_tarski(A_218))))), inference(resolution, [status(thm)], [c_597, c_36])).
% 3.12/1.49  tff(c_780, plain, (![A_218, B_46]: (~r2_hidden(A_218, k2_zfmisc_1(B_46, k1_tarski(A_218))))), inference(negUnitSimplification, [status(thm)], [c_703, c_610])).
% 3.12/1.49  tff(c_823, plain, (![B_301, A_302, C_303]: (~r2_hidden(B_301, k1_tarski(k4_tarski(A_302, B_301))) | ~r2_hidden(A_302, C_303))), inference(resolution, [status(thm)], [c_801, c_780])).
% 3.12/1.49  tff(c_825, plain, (![C_303]: (~r2_hidden('#skF_3', k1_tarski('#skF_3')) | ~r2_hidden('#skF_4', C_303))), inference(superposition, [status(thm), theory('equality')], [c_573, c_823])).
% 3.12/1.49  tff(c_826, plain, (~r2_hidden('#skF_3', k1_tarski('#skF_3'))), inference(splitLeft, [status(thm)], [c_825])).
% 3.12/1.49  tff(c_926, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_914, c_826])).
% 3.12/1.49  tff(c_930, plain, (![C_336]: (~r2_hidden('#skF_4', C_336))), inference(splitRight, [status(thm)], [c_825])).
% 3.12/1.49  tff(c_950, plain, $false, inference(resolution, [status(thm)], [c_56, c_930])).
% 3.12/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.12/1.49  
% 3.12/1.49  Inference rules
% 3.12/1.49  ----------------------
% 3.12/1.49  #Ref     : 0
% 3.12/1.49  #Sup     : 208
% 3.12/1.49  #Fact    : 0
% 3.12/1.49  #Define  : 0
% 3.12/1.49  #Split   : 2
% 3.12/1.49  #Chain   : 0
% 3.12/1.49  #Close   : 0
% 3.12/1.49  
% 3.12/1.49  Ordering : KBO
% 3.12/1.49  
% 3.12/1.49  Simplification rules
% 3.12/1.49  ----------------------
% 3.12/1.49  #Subsume      : 9
% 3.12/1.49  #Demod        : 30
% 3.12/1.49  #Tautology    : 121
% 3.12/1.49  #SimpNegUnit  : 10
% 3.12/1.49  #BackRed      : 10
% 3.12/1.49  
% 3.12/1.49  #Partial instantiations: 0
% 3.12/1.49  #Strategies tried      : 1
% 3.12/1.49  
% 3.12/1.49  Timing (in seconds)
% 3.12/1.49  ----------------------
% 3.26/1.49  Preprocessing        : 0.35
% 3.26/1.49  Parsing              : 0.18
% 3.26/1.49  CNF conversion       : 0.03
% 3.26/1.49  Main loop            : 0.35
% 3.26/1.49  Inferencing          : 0.13
% 3.26/1.49  Reduction            : 0.10
% 3.26/1.49  Demodulation         : 0.07
% 3.26/1.49  BG Simplification    : 0.02
% 3.26/1.49  Subsumption          : 0.07
% 3.26/1.49  Abstraction          : 0.02
% 3.26/1.49  MUC search           : 0.00
% 3.26/1.50  Cooper               : 0.00
% 3.26/1.50  Total                : 0.74
% 3.26/1.50  Index Insertion      : 0.00
% 3.26/1.50  Index Deletion       : 0.00
% 3.26/1.50  Index Matching       : 0.00
% 3.26/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
