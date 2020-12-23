%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:17 EST 2020

% Result     : Theorem 3.55s
% Output     : CNFRefutation 3.55s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 164 expanded)
%              Number of leaves         :   46 (  74 expanded)
%              Depth                    :   10
%              Number of atoms          :  111 ( 188 expanded)
%              Number of equality atoms :   77 ( 149 expanded)
%              Maximal formula depth    :   20 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_mcart_1 > k1_tarski > k1_setfam_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_95,axiom,(
    ! [A,B,C,D,E,F,G,H] :
      ( H = k5_enumset1(A,B,C,D,E,F,G)
    <=> ! [I] :
          ( r2_hidden(I,H)
        <=> ~ ( I != A
              & I != B
              & I != C
              & I != D
              & I != E
              & I != F
              & I != G ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_enumset1)).

tff(f_33,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_111,negated_conjecture,(
    ~ ! [A] :
        ( ? [B,C] : A = k4_tarski(B,C)
       => ( A != k1_mcart_1(A)
          & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_101,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k1_tarski(A),k2_tarski(B,C)) = k2_tarski(k4_tarski(A,B),k4_tarski(A,C))
      & k2_zfmisc_1(k2_tarski(A,B),k1_tarski(C)) = k2_tarski(k4_tarski(A,C),k4_tarski(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : k3_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_zfmisc_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( r1_tarski(A,k2_zfmisc_1(A,B))
        | r1_tarski(A,k2_zfmisc_1(B,A)) )
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t135_zfmisc_1)).

tff(c_10,plain,(
    ! [A_8,B_9] : k1_enumset1(A_8,A_8,B_9) = k2_tarski(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_10,B_11,C_12] : k2_enumset1(A_10,A_10,B_11,C_12) = k1_enumset1(A_10,B_11,C_12) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [A_13,B_14,C_15,D_16] : k3_enumset1(A_13,A_13,B_14,C_15,D_16) = k2_enumset1(A_13,B_14,C_15,D_16) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ! [E_21,D_20,C_19,B_18,A_17] : k4_enumset1(A_17,A_17,B_18,C_19,D_20,E_21) = k3_enumset1(A_17,B_18,C_19,D_20,E_21) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1274,plain,(
    ! [A_342,D_346,C_343,B_347,E_344,F_345] : k5_enumset1(A_342,A_342,B_347,C_343,D_346,E_344,F_345) = k4_enumset1(A_342,B_347,C_343,D_346,E_344,F_345) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_44,plain,(
    ! [B_49,F_53,A_48,D_51,I_58,E_52,C_50] : r2_hidden(I_58,k5_enumset1(A_48,B_49,C_50,D_51,E_52,F_53,I_58)) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1312,plain,(
    ! [B_352,C_350,D_355,A_351,F_353,E_354] : r2_hidden(F_353,k4_enumset1(A_351,B_352,C_350,D_355,E_354,F_353)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1274,c_44])).

tff(c_1325,plain,(
    ! [A_364,D_366,E_367,C_363,B_365] : r2_hidden(E_367,k3_enumset1(A_364,B_365,C_363,D_366,E_367)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1312])).

tff(c_1329,plain,(
    ! [D_368,A_369,B_370,C_371] : r2_hidden(D_368,k2_enumset1(A_369,B_370,C_371,D_368)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1325])).

tff(c_1333,plain,(
    ! [C_372,A_373,B_374] : r2_hidden(C_372,k1_enumset1(A_373,B_374,C_372)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1329])).

tff(c_1336,plain,(
    ! [B_9,A_8] : r2_hidden(B_9,k2_tarski(A_8,B_9)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_1333])).

tff(c_8,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_665,plain,(
    ! [D_192,E_190,A_188,C_189,F_191,B_193] : k5_enumset1(A_188,A_188,B_193,C_189,D_192,E_190,F_191) = k4_enumset1(A_188,B_193,C_189,D_192,E_190,F_191) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_56,plain,(
    ! [B_49,F_53,G_54,D_51,I_58,E_52,C_50] : r2_hidden(I_58,k5_enumset1(I_58,B_49,C_50,D_51,E_52,F_53,G_54)) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_696,plain,(
    ! [F_196,B_199,C_194,A_198,E_195,D_197] : r2_hidden(A_198,k4_enumset1(A_198,B_199,C_194,D_197,E_195,F_196)) ),
    inference(superposition,[status(thm),theory(equality)],[c_665,c_56])).

tff(c_700,plain,(
    ! [C_200,D_203,B_202,E_204,A_201] : r2_hidden(A_201,k3_enumset1(A_201,B_202,C_200,D_203,E_204)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_696])).

tff(c_704,plain,(
    ! [A_205,B_206,C_207,D_208] : r2_hidden(A_205,k2_enumset1(A_205,B_206,C_207,D_208)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_700])).

tff(c_708,plain,(
    ! [A_209,B_210,C_211] : r2_hidden(A_209,k1_enumset1(A_209,B_210,C_211)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_704])).

tff(c_721,plain,(
    ! [A_219,B_220] : r2_hidden(A_219,k2_tarski(A_219,B_220)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_708])).

tff(c_730,plain,(
    ! [A_7] : r2_hidden(A_7,k1_tarski(A_7)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_721])).

tff(c_98,plain,(
    k4_tarski('#skF_4','#skF_5') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_103,plain,(
    ! [A_65,B_66] : k1_mcart_1(k4_tarski(A_65,B_66)) = A_65 ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_112,plain,(
    k1_mcart_1('#skF_3') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_103])).

tff(c_96,plain,
    ( k2_mcart_1('#skF_3') = '#skF_3'
    | k1_mcart_1('#skF_3') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_140,plain,
    ( k2_mcart_1('#skF_3') = '#skF_3'
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_96])).

tff(c_141,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_140])).

tff(c_143,plain,(
    k4_tarski('#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_98])).

tff(c_465,plain,(
    ! [A_167,B_168,C_169] : k2_zfmisc_1(k2_tarski(A_167,B_168),k1_tarski(C_169)) = k2_tarski(k4_tarski(A_167,C_169),k4_tarski(B_168,C_169)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_499,plain,(
    ! [B_168,C_169] : k2_zfmisc_1(k2_tarski(B_168,B_168),k1_tarski(C_169)) = k1_tarski(k4_tarski(B_168,C_169)) ),
    inference(superposition,[status(thm),theory(equality)],[c_465,c_8])).

tff(c_524,plain,(
    ! [B_170,C_171] : k2_zfmisc_1(k1_tarski(B_170),k1_tarski(C_171)) = k1_tarski(k4_tarski(B_170,C_171)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_499])).

tff(c_6,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k2_xboole_0(A_5,B_6)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_3,B_4] : k3_xboole_0(A_3,k2_xboole_0(A_3,B_4)) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_301,plain,(
    ! [A_93,B_94] : k5_xboole_0(A_93,k3_xboole_0(A_93,B_94)) = k4_xboole_0(A_93,B_94) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_316,plain,(
    ! [A_3,B_4] : k4_xboole_0(A_3,k2_xboole_0(A_3,B_4)) = k5_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_301])).

tff(c_320,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_316])).

tff(c_321,plain,(
    ! [A_95,B_96] : k3_xboole_0(k1_tarski(A_95),k2_tarski(A_95,B_96)) = k1_tarski(A_95) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_344,plain,(
    ! [A_98] : k3_xboole_0(k1_tarski(A_98),k1_tarski(A_98)) = k1_tarski(A_98) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_321])).

tff(c_2,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(A_1,B_2)) = k4_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_350,plain,(
    ! [A_98] : k5_xboole_0(k1_tarski(A_98),k1_tarski(A_98)) = k4_xboole_0(k1_tarski(A_98),k1_tarski(A_98)) ),
    inference(superposition,[status(thm),theory(equality)],[c_344,c_2])).

tff(c_361,plain,(
    ! [A_98] : k4_xboole_0(k1_tarski(A_98),k1_tarski(A_98)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_320,c_350])).

tff(c_34,plain,(
    ! [B_44] : k4_xboole_0(k1_tarski(B_44),k1_tarski(B_44)) != k1_tarski(B_44) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_379,plain,(
    ! [B_44] : k1_tarski(B_44) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_361,c_34])).

tff(c_198,plain,(
    ! [A_83,B_84] :
      ( r1_tarski(k1_tarski(A_83),B_84)
      | ~ r2_hidden(A_83,B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_30,plain,(
    ! [A_39,B_40] :
      ( ~ r1_tarski(A_39,k2_zfmisc_1(A_39,B_40))
      | k1_xboole_0 = A_39 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_211,plain,(
    ! [A_83,B_40] :
      ( k1_tarski(A_83) = k1_xboole_0
      | ~ r2_hidden(A_83,k2_zfmisc_1(k1_tarski(A_83),B_40)) ) ),
    inference(resolution,[status(thm)],[c_198,c_30])).

tff(c_435,plain,(
    ! [A_83,B_40] : ~ r2_hidden(A_83,k2_zfmisc_1(k1_tarski(A_83),B_40)) ),
    inference(negUnitSimplification,[status(thm)],[c_379,c_211])).

tff(c_556,plain,(
    ! [B_177,C_178] : ~ r2_hidden(B_177,k1_tarski(k4_tarski(B_177,C_178))) ),
    inference(superposition,[status(thm),theory(equality)],[c_524,c_435])).

tff(c_559,plain,(
    ~ r2_hidden('#skF_4',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_556])).

tff(c_733,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_730,c_559])).

tff(c_734,plain,(
    k2_mcart_1('#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_140])).

tff(c_128,plain,(
    ! [A_68,B_69] : k2_mcart_1(k4_tarski(A_68,B_69)) = B_69 ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_137,plain,(
    k2_mcart_1('#skF_3') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_128])).

tff(c_740,plain,(
    '#skF_5' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_734,c_137])).

tff(c_745,plain,(
    k4_tarski('#skF_4','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_740,c_98])).

tff(c_1143,plain,(
    ! [A_327,B_328,C_329] : k2_zfmisc_1(k2_tarski(A_327,B_328),k1_tarski(C_329)) = k2_tarski(k4_tarski(A_327,C_329),k4_tarski(B_328,C_329)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_894,plain,(
    ! [A_244,B_245] : k5_xboole_0(A_244,k3_xboole_0(A_244,B_245)) = k4_xboole_0(A_244,B_245) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_909,plain,(
    ! [A_3,B_4] : k4_xboole_0(A_3,k2_xboole_0(A_3,B_4)) = k5_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_894])).

tff(c_913,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_909])).

tff(c_921,plain,(
    ! [A_247,B_248] : k3_xboole_0(k1_tarski(A_247),k2_tarski(A_247,B_248)) = k1_tarski(A_247) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_927,plain,(
    ! [A_247,B_248] : k5_xboole_0(k1_tarski(A_247),k1_tarski(A_247)) = k4_xboole_0(k1_tarski(A_247),k2_tarski(A_247,B_248)) ),
    inference(superposition,[status(thm),theory(equality)],[c_921,c_2])).

tff(c_938,plain,(
    ! [A_249,B_250] : k4_xboole_0(k1_tarski(A_249),k2_tarski(A_249,B_250)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_913,c_927])).

tff(c_945,plain,(
    ! [A_7] : k4_xboole_0(k1_tarski(A_7),k1_tarski(A_7)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_938])).

tff(c_948,plain,(
    ! [B_44] : k1_tarski(B_44) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_945,c_34])).

tff(c_24,plain,(
    ! [A_35,B_36] :
      ( r1_tarski(k1_tarski(A_35),B_36)
      | ~ r2_hidden(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_888,plain,(
    ! [A_242,B_243] :
      ( ~ r1_tarski(A_242,k2_zfmisc_1(B_243,A_242))
      | k1_xboole_0 = A_242 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_893,plain,(
    ! [A_35,B_243] :
      ( k1_tarski(A_35) = k1_xboole_0
      | ~ r2_hidden(A_35,k2_zfmisc_1(B_243,k1_tarski(A_35))) ) ),
    inference(resolution,[status(thm)],[c_24,c_888])).

tff(c_1033,plain,(
    ! [A_35,B_243] : ~ r2_hidden(A_35,k2_zfmisc_1(B_243,k1_tarski(A_35))) ),
    inference(negUnitSimplification,[status(thm)],[c_948,c_893])).

tff(c_1255,plain,(
    ! [C_339,A_340,B_341] : ~ r2_hidden(C_339,k2_tarski(k4_tarski(A_340,C_339),k4_tarski(B_341,C_339))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1143,c_1033])).

tff(c_1268,plain,(
    ! [A_340] : ~ r2_hidden('#skF_3',k2_tarski(k4_tarski(A_340,'#skF_3'),'#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_745,c_1255])).

tff(c_1339,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1336,c_1268])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:35:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.55/1.54  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.55/1.55  
% 3.55/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.55/1.55  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_mcart_1 > k1_tarski > k1_setfam_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 3.55/1.55  
% 3.55/1.55  %Foreground sorts:
% 3.55/1.55  
% 3.55/1.55  
% 3.55/1.55  %Background operators:
% 3.55/1.55  
% 3.55/1.55  
% 3.55/1.55  %Foreground operators:
% 3.55/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.55/1.55  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.55/1.55  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.55/1.55  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.55/1.55  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.55/1.55  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.55/1.55  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.55/1.55  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.55/1.55  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.55/1.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.55/1.55  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.55/1.55  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.55/1.55  tff('#skF_5', type, '#skF_5': $i).
% 3.55/1.55  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.55/1.55  tff('#skF_3', type, '#skF_3': $i).
% 3.55/1.55  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.55/1.55  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.55/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.55/1.55  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 3.55/1.55  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.55/1.55  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.55/1.55  tff('#skF_4', type, '#skF_4': $i).
% 3.55/1.55  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.55/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.55/1.55  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 3.55/1.55  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.55/1.55  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.55/1.55  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.55/1.55  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.55/1.55  
% 3.55/1.57  tff(f_35, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.55/1.57  tff(f_37, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 3.55/1.57  tff(f_39, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 3.55/1.57  tff(f_41, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 3.55/1.57  tff(f_43, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 3.55/1.57  tff(f_95, axiom, (![A, B, C, D, E, F, G, H]: ((H = k5_enumset1(A, B, C, D, E, F, G)) <=> (![I]: (r2_hidden(I, H) <=> ~((((((~(I = A) & ~(I = B)) & ~(I = C)) & ~(I = D)) & ~(I = E)) & ~(I = F)) & ~(I = G)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_enumset1)).
% 3.55/1.57  tff(f_33, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.55/1.57  tff(f_111, negated_conjecture, ~(![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_mcart_1)).
% 3.55/1.57  tff(f_101, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 3.55/1.57  tff(f_68, axiom, (![A, B, C]: ((k2_zfmisc_1(k1_tarski(A), k2_tarski(B, C)) = k2_tarski(k4_tarski(A, B), k4_tarski(A, C))) & (k2_zfmisc_1(k2_tarski(A, B), k1_tarski(C)) = k2_tarski(k4_tarski(A, C), k4_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_zfmisc_1)).
% 3.55/1.57  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 3.55/1.57  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_xboole_1)).
% 3.55/1.57  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.55/1.57  tff(f_59, axiom, (![A, B]: (k3_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_zfmisc_1)).
% 3.55/1.57  tff(f_64, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 3.55/1.57  tff(f_49, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.55/1.57  tff(f_57, axiom, (![A, B]: ((r1_tarski(A, k2_zfmisc_1(A, B)) | r1_tarski(A, k2_zfmisc_1(B, A))) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t135_zfmisc_1)).
% 3.55/1.57  tff(c_10, plain, (![A_8, B_9]: (k1_enumset1(A_8, A_8, B_9)=k2_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.55/1.57  tff(c_12, plain, (![A_10, B_11, C_12]: (k2_enumset1(A_10, A_10, B_11, C_12)=k1_enumset1(A_10, B_11, C_12))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.55/1.57  tff(c_14, plain, (![A_13, B_14, C_15, D_16]: (k3_enumset1(A_13, A_13, B_14, C_15, D_16)=k2_enumset1(A_13, B_14, C_15, D_16))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.55/1.57  tff(c_16, plain, (![E_21, D_20, C_19, B_18, A_17]: (k4_enumset1(A_17, A_17, B_18, C_19, D_20, E_21)=k3_enumset1(A_17, B_18, C_19, D_20, E_21))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.55/1.57  tff(c_1274, plain, (![A_342, D_346, C_343, B_347, E_344, F_345]: (k5_enumset1(A_342, A_342, B_347, C_343, D_346, E_344, F_345)=k4_enumset1(A_342, B_347, C_343, D_346, E_344, F_345))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.55/1.57  tff(c_44, plain, (![B_49, F_53, A_48, D_51, I_58, E_52, C_50]: (r2_hidden(I_58, k5_enumset1(A_48, B_49, C_50, D_51, E_52, F_53, I_58)))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.55/1.57  tff(c_1312, plain, (![B_352, C_350, D_355, A_351, F_353, E_354]: (r2_hidden(F_353, k4_enumset1(A_351, B_352, C_350, D_355, E_354, F_353)))), inference(superposition, [status(thm), theory('equality')], [c_1274, c_44])).
% 3.55/1.57  tff(c_1325, plain, (![A_364, D_366, E_367, C_363, B_365]: (r2_hidden(E_367, k3_enumset1(A_364, B_365, C_363, D_366, E_367)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_1312])).
% 3.55/1.57  tff(c_1329, plain, (![D_368, A_369, B_370, C_371]: (r2_hidden(D_368, k2_enumset1(A_369, B_370, C_371, D_368)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_1325])).
% 3.55/1.57  tff(c_1333, plain, (![C_372, A_373, B_374]: (r2_hidden(C_372, k1_enumset1(A_373, B_374, C_372)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_1329])).
% 3.55/1.57  tff(c_1336, plain, (![B_9, A_8]: (r2_hidden(B_9, k2_tarski(A_8, B_9)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_1333])).
% 3.55/1.57  tff(c_8, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.55/1.57  tff(c_665, plain, (![D_192, E_190, A_188, C_189, F_191, B_193]: (k5_enumset1(A_188, A_188, B_193, C_189, D_192, E_190, F_191)=k4_enumset1(A_188, B_193, C_189, D_192, E_190, F_191))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.55/1.57  tff(c_56, plain, (![B_49, F_53, G_54, D_51, I_58, E_52, C_50]: (r2_hidden(I_58, k5_enumset1(I_58, B_49, C_50, D_51, E_52, F_53, G_54)))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.55/1.57  tff(c_696, plain, (![F_196, B_199, C_194, A_198, E_195, D_197]: (r2_hidden(A_198, k4_enumset1(A_198, B_199, C_194, D_197, E_195, F_196)))), inference(superposition, [status(thm), theory('equality')], [c_665, c_56])).
% 3.55/1.57  tff(c_700, plain, (![C_200, D_203, B_202, E_204, A_201]: (r2_hidden(A_201, k3_enumset1(A_201, B_202, C_200, D_203, E_204)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_696])).
% 3.55/1.57  tff(c_704, plain, (![A_205, B_206, C_207, D_208]: (r2_hidden(A_205, k2_enumset1(A_205, B_206, C_207, D_208)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_700])).
% 3.55/1.57  tff(c_708, plain, (![A_209, B_210, C_211]: (r2_hidden(A_209, k1_enumset1(A_209, B_210, C_211)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_704])).
% 3.55/1.57  tff(c_721, plain, (![A_219, B_220]: (r2_hidden(A_219, k2_tarski(A_219, B_220)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_708])).
% 3.55/1.57  tff(c_730, plain, (![A_7]: (r2_hidden(A_7, k1_tarski(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_721])).
% 3.55/1.57  tff(c_98, plain, (k4_tarski('#skF_4', '#skF_5')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.55/1.57  tff(c_103, plain, (![A_65, B_66]: (k1_mcart_1(k4_tarski(A_65, B_66))=A_65)), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.55/1.57  tff(c_112, plain, (k1_mcart_1('#skF_3')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_98, c_103])).
% 3.55/1.57  tff(c_96, plain, (k2_mcart_1('#skF_3')='#skF_3' | k1_mcart_1('#skF_3')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.55/1.57  tff(c_140, plain, (k2_mcart_1('#skF_3')='#skF_3' | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_112, c_96])).
% 3.55/1.57  tff(c_141, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_140])).
% 3.55/1.57  tff(c_143, plain, (k4_tarski('#skF_4', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_141, c_98])).
% 3.55/1.57  tff(c_465, plain, (![A_167, B_168, C_169]: (k2_zfmisc_1(k2_tarski(A_167, B_168), k1_tarski(C_169))=k2_tarski(k4_tarski(A_167, C_169), k4_tarski(B_168, C_169)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.55/1.57  tff(c_499, plain, (![B_168, C_169]: (k2_zfmisc_1(k2_tarski(B_168, B_168), k1_tarski(C_169))=k1_tarski(k4_tarski(B_168, C_169)))), inference(superposition, [status(thm), theory('equality')], [c_465, c_8])).
% 3.55/1.57  tff(c_524, plain, (![B_170, C_171]: (k2_zfmisc_1(k1_tarski(B_170), k1_tarski(C_171))=k1_tarski(k4_tarski(B_170, C_171)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_499])).
% 3.55/1.57  tff(c_6, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k2_xboole_0(A_5, B_6))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.55/1.57  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, k2_xboole_0(A_3, B_4))=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.55/1.57  tff(c_301, plain, (![A_93, B_94]: (k5_xboole_0(A_93, k3_xboole_0(A_93, B_94))=k4_xboole_0(A_93, B_94))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.55/1.57  tff(c_316, plain, (![A_3, B_4]: (k4_xboole_0(A_3, k2_xboole_0(A_3, B_4))=k5_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_301])).
% 3.55/1.57  tff(c_320, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_316])).
% 3.55/1.57  tff(c_321, plain, (![A_95, B_96]: (k3_xboole_0(k1_tarski(A_95), k2_tarski(A_95, B_96))=k1_tarski(A_95))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.55/1.57  tff(c_344, plain, (![A_98]: (k3_xboole_0(k1_tarski(A_98), k1_tarski(A_98))=k1_tarski(A_98))), inference(superposition, [status(thm), theory('equality')], [c_8, c_321])).
% 3.55/1.57  tff(c_2, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(A_1, B_2))=k4_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.55/1.57  tff(c_350, plain, (![A_98]: (k5_xboole_0(k1_tarski(A_98), k1_tarski(A_98))=k4_xboole_0(k1_tarski(A_98), k1_tarski(A_98)))), inference(superposition, [status(thm), theory('equality')], [c_344, c_2])).
% 3.55/1.57  tff(c_361, plain, (![A_98]: (k4_xboole_0(k1_tarski(A_98), k1_tarski(A_98))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_320, c_350])).
% 3.55/1.57  tff(c_34, plain, (![B_44]: (k4_xboole_0(k1_tarski(B_44), k1_tarski(B_44))!=k1_tarski(B_44))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.55/1.57  tff(c_379, plain, (![B_44]: (k1_tarski(B_44)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_361, c_34])).
% 3.55/1.57  tff(c_198, plain, (![A_83, B_84]: (r1_tarski(k1_tarski(A_83), B_84) | ~r2_hidden(A_83, B_84))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.55/1.57  tff(c_30, plain, (![A_39, B_40]: (~r1_tarski(A_39, k2_zfmisc_1(A_39, B_40)) | k1_xboole_0=A_39)), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.55/1.57  tff(c_211, plain, (![A_83, B_40]: (k1_tarski(A_83)=k1_xboole_0 | ~r2_hidden(A_83, k2_zfmisc_1(k1_tarski(A_83), B_40)))), inference(resolution, [status(thm)], [c_198, c_30])).
% 3.55/1.57  tff(c_435, plain, (![A_83, B_40]: (~r2_hidden(A_83, k2_zfmisc_1(k1_tarski(A_83), B_40)))), inference(negUnitSimplification, [status(thm)], [c_379, c_211])).
% 3.55/1.57  tff(c_556, plain, (![B_177, C_178]: (~r2_hidden(B_177, k1_tarski(k4_tarski(B_177, C_178))))), inference(superposition, [status(thm), theory('equality')], [c_524, c_435])).
% 3.55/1.57  tff(c_559, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_143, c_556])).
% 3.55/1.57  tff(c_733, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_730, c_559])).
% 3.55/1.57  tff(c_734, plain, (k2_mcart_1('#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_140])).
% 3.55/1.57  tff(c_128, plain, (![A_68, B_69]: (k2_mcart_1(k4_tarski(A_68, B_69))=B_69)), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.55/1.57  tff(c_137, plain, (k2_mcart_1('#skF_3')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_98, c_128])).
% 3.55/1.57  tff(c_740, plain, ('#skF_5'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_734, c_137])).
% 3.55/1.57  tff(c_745, plain, (k4_tarski('#skF_4', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_740, c_98])).
% 3.55/1.57  tff(c_1143, plain, (![A_327, B_328, C_329]: (k2_zfmisc_1(k2_tarski(A_327, B_328), k1_tarski(C_329))=k2_tarski(k4_tarski(A_327, C_329), k4_tarski(B_328, C_329)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.55/1.57  tff(c_894, plain, (![A_244, B_245]: (k5_xboole_0(A_244, k3_xboole_0(A_244, B_245))=k4_xboole_0(A_244, B_245))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.55/1.57  tff(c_909, plain, (![A_3, B_4]: (k4_xboole_0(A_3, k2_xboole_0(A_3, B_4))=k5_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_894])).
% 3.55/1.57  tff(c_913, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_909])).
% 3.55/1.57  tff(c_921, plain, (![A_247, B_248]: (k3_xboole_0(k1_tarski(A_247), k2_tarski(A_247, B_248))=k1_tarski(A_247))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.55/1.57  tff(c_927, plain, (![A_247, B_248]: (k5_xboole_0(k1_tarski(A_247), k1_tarski(A_247))=k4_xboole_0(k1_tarski(A_247), k2_tarski(A_247, B_248)))), inference(superposition, [status(thm), theory('equality')], [c_921, c_2])).
% 3.55/1.57  tff(c_938, plain, (![A_249, B_250]: (k4_xboole_0(k1_tarski(A_249), k2_tarski(A_249, B_250))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_913, c_927])).
% 3.55/1.57  tff(c_945, plain, (![A_7]: (k4_xboole_0(k1_tarski(A_7), k1_tarski(A_7))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8, c_938])).
% 3.55/1.57  tff(c_948, plain, (![B_44]: (k1_tarski(B_44)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_945, c_34])).
% 3.55/1.57  tff(c_24, plain, (![A_35, B_36]: (r1_tarski(k1_tarski(A_35), B_36) | ~r2_hidden(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.55/1.57  tff(c_888, plain, (![A_242, B_243]: (~r1_tarski(A_242, k2_zfmisc_1(B_243, A_242)) | k1_xboole_0=A_242)), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.55/1.57  tff(c_893, plain, (![A_35, B_243]: (k1_tarski(A_35)=k1_xboole_0 | ~r2_hidden(A_35, k2_zfmisc_1(B_243, k1_tarski(A_35))))), inference(resolution, [status(thm)], [c_24, c_888])).
% 3.55/1.57  tff(c_1033, plain, (![A_35, B_243]: (~r2_hidden(A_35, k2_zfmisc_1(B_243, k1_tarski(A_35))))), inference(negUnitSimplification, [status(thm)], [c_948, c_893])).
% 3.55/1.57  tff(c_1255, plain, (![C_339, A_340, B_341]: (~r2_hidden(C_339, k2_tarski(k4_tarski(A_340, C_339), k4_tarski(B_341, C_339))))), inference(superposition, [status(thm), theory('equality')], [c_1143, c_1033])).
% 3.55/1.57  tff(c_1268, plain, (![A_340]: (~r2_hidden('#skF_3', k2_tarski(k4_tarski(A_340, '#skF_3'), '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_745, c_1255])).
% 3.55/1.57  tff(c_1339, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1336, c_1268])).
% 3.55/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.55/1.57  
% 3.55/1.57  Inference rules
% 3.55/1.57  ----------------------
% 3.55/1.57  #Ref     : 0
% 3.55/1.57  #Sup     : 309
% 3.55/1.57  #Fact    : 0
% 3.55/1.57  #Define  : 0
% 3.55/1.57  #Split   : 1
% 3.55/1.57  #Chain   : 0
% 3.55/1.57  #Close   : 0
% 3.55/1.57  
% 3.55/1.57  Ordering : KBO
% 3.55/1.57  
% 3.55/1.57  Simplification rules
% 3.55/1.57  ----------------------
% 3.55/1.57  #Subsume      : 13
% 3.55/1.57  #Demod        : 71
% 3.55/1.57  #Tautology    : 184
% 3.55/1.57  #SimpNegUnit  : 14
% 3.55/1.57  #BackRed      : 8
% 3.55/1.57  
% 3.55/1.57  #Partial instantiations: 0
% 3.55/1.57  #Strategies tried      : 1
% 3.55/1.57  
% 3.55/1.57  Timing (in seconds)
% 3.55/1.57  ----------------------
% 3.55/1.57  Preprocessing        : 0.36
% 3.55/1.57  Parsing              : 0.18
% 3.55/1.57  CNF conversion       : 0.03
% 3.55/1.57  Main loop            : 0.44
% 3.55/1.57  Inferencing          : 0.16
% 3.55/1.57  Reduction            : 0.13
% 3.55/1.57  Demodulation         : 0.09
% 3.55/1.57  BG Simplification    : 0.03
% 3.55/1.57  Subsumption          : 0.09
% 3.55/1.57  Abstraction          : 0.03
% 3.55/1.57  MUC search           : 0.00
% 3.55/1.57  Cooper               : 0.00
% 3.55/1.57  Total                : 0.84
% 3.55/1.57  Index Insertion      : 0.00
% 3.55/1.57  Index Deletion       : 0.00
% 3.55/1.57  Index Matching       : 0.00
% 3.55/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
