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
% DateTime   : Thu Dec  3 10:09:18 EST 2020

% Result     : Theorem 3.32s
% Output     : CNFRefutation 3.32s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 163 expanded)
%              Number of leaves         :   43 (  73 expanded)
%              Depth                    :    9
%              Number of atoms          :  106 ( 192 expanded)
%              Number of equality atoms :   71 ( 152 expanded)
%              Maximal formula depth    :   20 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_setfam_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_31,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_33,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_91,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_enumset1)).

tff(f_107,negated_conjecture,(
    ~ ! [A] :
        ( ? [B,C] : A = k4_tarski(B,C)
       => ( A != k1_mcart_1(A)
          & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_97,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k1_tarski(A),k2_tarski(B,C)) = k2_tarski(k4_tarski(A,B),k4_tarski(A,C))
      & k2_zfmisc_1(k2_tarski(A,B),k1_tarski(C)) = k2_tarski(k4_tarski(A,C),k4_tarski(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).

tff(f_29,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : k3_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ( r1_tarski(A,k2_zfmisc_1(A,B))
        | r1_tarski(A,k2_zfmisc_1(B,A)) )
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t135_zfmisc_1)).

tff(c_6,plain,(
    ! [A_4] : k2_tarski(A_4,A_4) = k1_tarski(A_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_5,B_6] : k1_enumset1(A_5,A_5,B_6) = k2_tarski(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_7,B_8,C_9] : k2_enumset1(A_7,A_7,B_8,C_9) = k1_enumset1(A_7,B_8,C_9) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_10,B_11,C_12,D_13] : k3_enumset1(A_10,A_10,B_11,C_12,D_13) = k2_enumset1(A_10,B_11,C_12,D_13) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [E_18,C_16,D_17,A_14,B_15] : k4_enumset1(A_14,A_14,B_15,C_16,D_17,E_18) = k3_enumset1(A_14,B_15,C_16,D_17,E_18) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1074,plain,(
    ! [D_324,E_320,C_319,A_322,B_321,F_323] : k5_enumset1(A_322,A_322,B_321,C_319,D_324,E_320,F_323) = k4_enumset1(A_322,B_321,C_319,D_324,E_320,F_323) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_52,plain,(
    ! [G_49,I_53,E_47,F_48,D_46,C_45,B_44] : r2_hidden(I_53,k5_enumset1(I_53,B_44,C_45,D_46,E_47,F_48,G_49)) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1130,plain,(
    ! [E_329,F_330,C_332,A_333,D_334,B_331] : r2_hidden(A_333,k4_enumset1(A_333,B_331,C_332,D_334,E_329,F_330)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1074,c_52])).

tff(c_1134,plain,(
    ! [C_337,B_338,E_335,A_339,D_336] : r2_hidden(A_339,k3_enumset1(A_339,B_338,C_337,D_336,E_335)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1130])).

tff(c_1138,plain,(
    ! [A_340,B_341,C_342,D_343] : r2_hidden(A_340,k2_enumset1(A_340,B_341,C_342,D_343)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1134])).

tff(c_1142,plain,(
    ! [A_344,B_345,C_346] : r2_hidden(A_344,k1_enumset1(A_344,B_345,C_346)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_1138])).

tff(c_1146,plain,(
    ! [A_347,B_348] : r2_hidden(A_347,k2_tarski(A_347,B_348)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_1142])).

tff(c_1155,plain,(
    ! [A_4] : r2_hidden(A_4,k1_tarski(A_4)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_1146])).

tff(c_541,plain,(
    ! [D_173,A_171,E_169,F_172,C_168,B_170] : k5_enumset1(A_171,A_171,B_170,C_168,D_173,E_169,F_172) = k4_enumset1(A_171,B_170,C_168,D_173,E_169,F_172) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_48,plain,(
    ! [G_49,I_53,E_47,F_48,D_46,A_43,B_44] : r2_hidden(I_53,k5_enumset1(A_43,B_44,I_53,D_46,E_47,F_48,G_49)) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_610,plain,(
    ! [B_188,C_190,D_187,A_192,E_189,F_191] : r2_hidden(B_188,k4_enumset1(A_192,B_188,C_190,D_187,E_189,F_191)) ),
    inference(superposition,[status(thm),theory(equality)],[c_541,c_48])).

tff(c_614,plain,(
    ! [C_195,E_193,A_197,B_196,D_194] : r2_hidden(A_197,k3_enumset1(A_197,B_196,C_195,D_194,E_193)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_610])).

tff(c_657,plain,(
    ! [A_206,B_207,C_208,D_209] : r2_hidden(A_206,k2_enumset1(A_206,B_207,C_208,D_209)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_614])).

tff(c_661,plain,(
    ! [A_210,B_211,C_212] : r2_hidden(A_210,k1_enumset1(A_210,B_211,C_212)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_657])).

tff(c_665,plain,(
    ! [A_213,B_214] : r2_hidden(A_213,k2_tarski(A_213,B_214)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_661])).

tff(c_674,plain,(
    ! [A_4] : r2_hidden(A_4,k1_tarski(A_4)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_665])).

tff(c_94,plain,(
    k4_tarski('#skF_4','#skF_5') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_106,plain,(
    ! [A_61,B_62] : k1_mcart_1(k4_tarski(A_61,B_62)) = A_61 ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_115,plain,(
    k1_mcart_1('#skF_3') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_106])).

tff(c_131,plain,(
    ! [A_64,B_65] : k2_mcart_1(k4_tarski(A_64,B_65)) = B_65 ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_140,plain,(
    k2_mcart_1('#skF_3') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_131])).

tff(c_92,plain,
    ( k2_mcart_1('#skF_3') = '#skF_3'
    | k1_mcart_1('#skF_3') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_147,plain,
    ( '#skF_5' = '#skF_3'
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_140,c_92])).

tff(c_148,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_147])).

tff(c_151,plain,(
    k4_tarski('#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_94])).

tff(c_386,plain,(
    ! [A_158,B_159,C_160] : k2_zfmisc_1(k1_tarski(A_158),k2_tarski(B_159,C_160)) = k2_tarski(k4_tarski(A_158,B_159),k4_tarski(A_158,C_160)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_417,plain,(
    ! [A_158,C_160] : k2_zfmisc_1(k1_tarski(A_158),k2_tarski(C_160,C_160)) = k1_tarski(k4_tarski(A_158,C_160)) ),
    inference(superposition,[status(thm),theory(equality)],[c_386,c_6])).

tff(c_514,plain,(
    ! [A_164,C_165] : k2_zfmisc_1(k1_tarski(A_164),k1_tarski(C_165)) = k1_tarski(k4_tarski(A_164,C_165)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_417])).

tff(c_4,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_233,plain,(
    ! [A_80,B_81] : k3_xboole_0(k1_tarski(A_80),k2_tarski(A_80,B_81)) = k1_tarski(A_80) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_242,plain,(
    ! [A_4] : k3_xboole_0(k1_tarski(A_4),k1_tarski(A_4)) = k1_tarski(A_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_233])).

tff(c_269,plain,(
    ! [A_84,B_85] : k5_xboole_0(A_84,k3_xboole_0(A_84,B_85)) = k4_xboole_0(A_84,B_85) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_278,plain,(
    ! [A_4] : k5_xboole_0(k1_tarski(A_4),k1_tarski(A_4)) = k4_xboole_0(k1_tarski(A_4),k1_tarski(A_4)) ),
    inference(superposition,[status(thm),theory(equality)],[c_242,c_269])).

tff(c_287,plain,(
    ! [A_4] : k4_xboole_0(k1_tarski(A_4),k1_tarski(A_4)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_278])).

tff(c_30,plain,(
    ! [B_39] : k4_xboole_0(k1_tarski(B_39),k1_tarski(B_39)) != k1_tarski(B_39) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_290,plain,(
    ! [B_39] : k1_tarski(B_39) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_287,c_30])).

tff(c_208,plain,(
    ! [A_74,B_75] :
      ( r1_tarski(k1_tarski(A_74),B_75)
      | ~ r2_hidden(A_74,B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_26,plain,(
    ! [A_34,B_35] :
      ( ~ r1_tarski(A_34,k2_zfmisc_1(A_34,B_35))
      | k1_xboole_0 = A_34 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_216,plain,(
    ! [A_74,B_35] :
      ( k1_tarski(A_74) = k1_xboole_0
      | ~ r2_hidden(A_74,k2_zfmisc_1(k1_tarski(A_74),B_35)) ) ),
    inference(resolution,[status(thm)],[c_208,c_26])).

tff(c_357,plain,(
    ! [A_74,B_35] : ~ r2_hidden(A_74,k2_zfmisc_1(k1_tarski(A_74),B_35)) ),
    inference(negUnitSimplification,[status(thm)],[c_290,c_216])).

tff(c_571,plain,(
    ! [A_174,C_175] : ~ r2_hidden(A_174,k1_tarski(k4_tarski(A_174,C_175))) ),
    inference(superposition,[status(thm),theory(equality)],[c_514,c_357])).

tff(c_574,plain,(
    ~ r2_hidden('#skF_4',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_571])).

tff(c_677,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_674,c_574])).

tff(c_678,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_147])).

tff(c_681,plain,(
    k4_tarski('#skF_4','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_678,c_94])).

tff(c_915,plain,(
    ! [A_307,B_308,C_309] : k2_zfmisc_1(k1_tarski(A_307),k2_tarski(B_308,C_309)) = k2_tarski(k4_tarski(A_307,B_308),k4_tarski(A_307,C_309)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_946,plain,(
    ! [A_307,C_309] : k2_zfmisc_1(k1_tarski(A_307),k2_tarski(C_309,C_309)) = k1_tarski(k4_tarski(A_307,C_309)) ),
    inference(superposition,[status(thm),theory(equality)],[c_915,c_6])).

tff(c_1043,plain,(
    ! [A_313,C_314] : k2_zfmisc_1(k1_tarski(A_313),k1_tarski(C_314)) = k1_tarski(k4_tarski(A_313,C_314)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_946])).

tff(c_771,plain,(
    ! [A_231,B_232] : k3_xboole_0(k1_tarski(A_231),k2_tarski(A_231,B_232)) = k1_tarski(A_231) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(A_1,B_2)) = k4_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_777,plain,(
    ! [A_231,B_232] : k5_xboole_0(k1_tarski(A_231),k1_tarski(A_231)) = k4_xboole_0(k1_tarski(A_231),k2_tarski(A_231,B_232)) ),
    inference(superposition,[status(thm),theory(equality)],[c_771,c_2])).

tff(c_787,plain,(
    ! [A_233,B_234] : k4_xboole_0(k1_tarski(A_233),k2_tarski(A_233,B_234)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_777])).

tff(c_794,plain,(
    ! [A_4] : k4_xboole_0(k1_tarski(A_4),k1_tarski(A_4)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_787])).

tff(c_813,plain,(
    ! [B_39] : k1_tarski(B_39) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_794,c_30])).

tff(c_22,plain,(
    ! [A_32,B_33] :
      ( r1_tarski(k1_tarski(A_32),B_33)
      | ~ r2_hidden(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_743,plain,(
    ! [A_224,B_225] :
      ( ~ r1_tarski(A_224,k2_zfmisc_1(B_225,A_224))
      | k1_xboole_0 = A_224 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_748,plain,(
    ! [A_32,B_225] :
      ( k1_tarski(A_32) = k1_xboole_0
      | ~ r2_hidden(A_32,k2_zfmisc_1(B_225,k1_tarski(A_32))) ) ),
    inference(resolution,[status(thm)],[c_22,c_743])).

tff(c_888,plain,(
    ! [A_32,B_225] : ~ r2_hidden(A_32,k2_zfmisc_1(B_225,k1_tarski(A_32))) ),
    inference(negUnitSimplification,[status(thm)],[c_813,c_748])).

tff(c_1066,plain,(
    ! [C_315,A_316] : ~ r2_hidden(C_315,k1_tarski(k4_tarski(A_316,C_315))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1043,c_888])).

tff(c_1069,plain,(
    ~ r2_hidden('#skF_3',k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_681,c_1066])).

tff(c_1167,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1155,c_1069])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:49:15 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.32/1.58  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.32/1.59  
% 3.32/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.32/1.59  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_setfam_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 3.32/1.59  
% 3.32/1.59  %Foreground sorts:
% 3.32/1.59  
% 3.32/1.59  
% 3.32/1.59  %Background operators:
% 3.32/1.59  
% 3.32/1.59  
% 3.32/1.59  %Foreground operators:
% 3.32/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.32/1.59  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.32/1.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.32/1.59  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.32/1.59  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.32/1.59  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.32/1.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.32/1.59  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.32/1.59  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.32/1.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.32/1.59  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.32/1.59  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.32/1.59  tff('#skF_5', type, '#skF_5': $i).
% 3.32/1.59  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.32/1.59  tff('#skF_3', type, '#skF_3': $i).
% 3.32/1.59  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.32/1.59  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.32/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.32/1.59  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 3.32/1.59  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.32/1.59  tff('#skF_4', type, '#skF_4': $i).
% 3.32/1.59  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.32/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.32/1.59  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 3.32/1.59  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.32/1.59  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.32/1.59  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.32/1.59  
% 3.32/1.61  tff(f_31, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.32/1.61  tff(f_33, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.32/1.61  tff(f_35, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 3.32/1.61  tff(f_37, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 3.32/1.61  tff(f_39, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 3.32/1.61  tff(f_41, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 3.32/1.61  tff(f_91, axiom, (![A, B, C, D, E, F, G, H]: ((H = k5_enumset1(A, B, C, D, E, F, G)) <=> (![I]: (r2_hidden(I, H) <=> ~((((((~(I = A) & ~(I = B)) & ~(I = C)) & ~(I = D)) & ~(I = E)) & ~(I = F)) & ~(I = G)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_enumset1)).
% 3.32/1.61  tff(f_107, negated_conjecture, ~(![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_mcart_1)).
% 3.32/1.61  tff(f_97, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 3.32/1.61  tff(f_64, axiom, (![A, B, C]: ((k2_zfmisc_1(k1_tarski(A), k2_tarski(B, C)) = k2_tarski(k4_tarski(A, B), k4_tarski(A, C))) & (k2_zfmisc_1(k2_tarski(A, B), k1_tarski(C)) = k2_tarski(k4_tarski(A, C), k4_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_zfmisc_1)).
% 3.32/1.61  tff(f_29, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.32/1.61  tff(f_55, axiom, (![A, B]: (k3_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_zfmisc_1)).
% 3.32/1.61  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.32/1.61  tff(f_60, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 3.32/1.61  tff(f_47, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.32/1.61  tff(f_53, axiom, (![A, B]: ((r1_tarski(A, k2_zfmisc_1(A, B)) | r1_tarski(A, k2_zfmisc_1(B, A))) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t135_zfmisc_1)).
% 3.32/1.61  tff(c_6, plain, (![A_4]: (k2_tarski(A_4, A_4)=k1_tarski(A_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.32/1.61  tff(c_8, plain, (![A_5, B_6]: (k1_enumset1(A_5, A_5, B_6)=k2_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.32/1.61  tff(c_10, plain, (![A_7, B_8, C_9]: (k2_enumset1(A_7, A_7, B_8, C_9)=k1_enumset1(A_7, B_8, C_9))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.32/1.61  tff(c_12, plain, (![A_10, B_11, C_12, D_13]: (k3_enumset1(A_10, A_10, B_11, C_12, D_13)=k2_enumset1(A_10, B_11, C_12, D_13))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.32/1.61  tff(c_14, plain, (![E_18, C_16, D_17, A_14, B_15]: (k4_enumset1(A_14, A_14, B_15, C_16, D_17, E_18)=k3_enumset1(A_14, B_15, C_16, D_17, E_18))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.32/1.61  tff(c_1074, plain, (![D_324, E_320, C_319, A_322, B_321, F_323]: (k5_enumset1(A_322, A_322, B_321, C_319, D_324, E_320, F_323)=k4_enumset1(A_322, B_321, C_319, D_324, E_320, F_323))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.32/1.61  tff(c_52, plain, (![G_49, I_53, E_47, F_48, D_46, C_45, B_44]: (r2_hidden(I_53, k5_enumset1(I_53, B_44, C_45, D_46, E_47, F_48, G_49)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.32/1.61  tff(c_1130, plain, (![E_329, F_330, C_332, A_333, D_334, B_331]: (r2_hidden(A_333, k4_enumset1(A_333, B_331, C_332, D_334, E_329, F_330)))), inference(superposition, [status(thm), theory('equality')], [c_1074, c_52])).
% 3.32/1.61  tff(c_1134, plain, (![C_337, B_338, E_335, A_339, D_336]: (r2_hidden(A_339, k3_enumset1(A_339, B_338, C_337, D_336, E_335)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_1130])).
% 3.32/1.61  tff(c_1138, plain, (![A_340, B_341, C_342, D_343]: (r2_hidden(A_340, k2_enumset1(A_340, B_341, C_342, D_343)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_1134])).
% 3.32/1.61  tff(c_1142, plain, (![A_344, B_345, C_346]: (r2_hidden(A_344, k1_enumset1(A_344, B_345, C_346)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_1138])).
% 3.32/1.61  tff(c_1146, plain, (![A_347, B_348]: (r2_hidden(A_347, k2_tarski(A_347, B_348)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_1142])).
% 3.32/1.61  tff(c_1155, plain, (![A_4]: (r2_hidden(A_4, k1_tarski(A_4)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_1146])).
% 3.32/1.61  tff(c_541, plain, (![D_173, A_171, E_169, F_172, C_168, B_170]: (k5_enumset1(A_171, A_171, B_170, C_168, D_173, E_169, F_172)=k4_enumset1(A_171, B_170, C_168, D_173, E_169, F_172))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.32/1.61  tff(c_48, plain, (![G_49, I_53, E_47, F_48, D_46, A_43, B_44]: (r2_hidden(I_53, k5_enumset1(A_43, B_44, I_53, D_46, E_47, F_48, G_49)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.32/1.61  tff(c_610, plain, (![B_188, C_190, D_187, A_192, E_189, F_191]: (r2_hidden(B_188, k4_enumset1(A_192, B_188, C_190, D_187, E_189, F_191)))), inference(superposition, [status(thm), theory('equality')], [c_541, c_48])).
% 3.32/1.61  tff(c_614, plain, (![C_195, E_193, A_197, B_196, D_194]: (r2_hidden(A_197, k3_enumset1(A_197, B_196, C_195, D_194, E_193)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_610])).
% 3.32/1.61  tff(c_657, plain, (![A_206, B_207, C_208, D_209]: (r2_hidden(A_206, k2_enumset1(A_206, B_207, C_208, D_209)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_614])).
% 3.32/1.61  tff(c_661, plain, (![A_210, B_211, C_212]: (r2_hidden(A_210, k1_enumset1(A_210, B_211, C_212)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_657])).
% 3.32/1.61  tff(c_665, plain, (![A_213, B_214]: (r2_hidden(A_213, k2_tarski(A_213, B_214)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_661])).
% 3.32/1.61  tff(c_674, plain, (![A_4]: (r2_hidden(A_4, k1_tarski(A_4)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_665])).
% 3.32/1.61  tff(c_94, plain, (k4_tarski('#skF_4', '#skF_5')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.32/1.61  tff(c_106, plain, (![A_61, B_62]: (k1_mcart_1(k4_tarski(A_61, B_62))=A_61)), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.32/1.61  tff(c_115, plain, (k1_mcart_1('#skF_3')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_94, c_106])).
% 3.32/1.61  tff(c_131, plain, (![A_64, B_65]: (k2_mcart_1(k4_tarski(A_64, B_65))=B_65)), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.32/1.61  tff(c_140, plain, (k2_mcart_1('#skF_3')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_94, c_131])).
% 3.32/1.61  tff(c_92, plain, (k2_mcart_1('#skF_3')='#skF_3' | k1_mcart_1('#skF_3')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.32/1.61  tff(c_147, plain, ('#skF_5'='#skF_3' | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_115, c_140, c_92])).
% 3.32/1.61  tff(c_148, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_147])).
% 3.32/1.61  tff(c_151, plain, (k4_tarski('#skF_4', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_148, c_94])).
% 3.32/1.61  tff(c_386, plain, (![A_158, B_159, C_160]: (k2_zfmisc_1(k1_tarski(A_158), k2_tarski(B_159, C_160))=k2_tarski(k4_tarski(A_158, B_159), k4_tarski(A_158, C_160)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.32/1.61  tff(c_417, plain, (![A_158, C_160]: (k2_zfmisc_1(k1_tarski(A_158), k2_tarski(C_160, C_160))=k1_tarski(k4_tarski(A_158, C_160)))), inference(superposition, [status(thm), theory('equality')], [c_386, c_6])).
% 3.32/1.61  tff(c_514, plain, (![A_164, C_165]: (k2_zfmisc_1(k1_tarski(A_164), k1_tarski(C_165))=k1_tarski(k4_tarski(A_164, C_165)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_417])).
% 3.32/1.61  tff(c_4, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.32/1.61  tff(c_233, plain, (![A_80, B_81]: (k3_xboole_0(k1_tarski(A_80), k2_tarski(A_80, B_81))=k1_tarski(A_80))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.32/1.61  tff(c_242, plain, (![A_4]: (k3_xboole_0(k1_tarski(A_4), k1_tarski(A_4))=k1_tarski(A_4))), inference(superposition, [status(thm), theory('equality')], [c_6, c_233])).
% 3.32/1.61  tff(c_269, plain, (![A_84, B_85]: (k5_xboole_0(A_84, k3_xboole_0(A_84, B_85))=k4_xboole_0(A_84, B_85))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.32/1.61  tff(c_278, plain, (![A_4]: (k5_xboole_0(k1_tarski(A_4), k1_tarski(A_4))=k4_xboole_0(k1_tarski(A_4), k1_tarski(A_4)))), inference(superposition, [status(thm), theory('equality')], [c_242, c_269])).
% 3.32/1.61  tff(c_287, plain, (![A_4]: (k4_xboole_0(k1_tarski(A_4), k1_tarski(A_4))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_278])).
% 3.32/1.61  tff(c_30, plain, (![B_39]: (k4_xboole_0(k1_tarski(B_39), k1_tarski(B_39))!=k1_tarski(B_39))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.32/1.61  tff(c_290, plain, (![B_39]: (k1_tarski(B_39)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_287, c_30])).
% 3.32/1.61  tff(c_208, plain, (![A_74, B_75]: (r1_tarski(k1_tarski(A_74), B_75) | ~r2_hidden(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.32/1.61  tff(c_26, plain, (![A_34, B_35]: (~r1_tarski(A_34, k2_zfmisc_1(A_34, B_35)) | k1_xboole_0=A_34)), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.32/1.61  tff(c_216, plain, (![A_74, B_35]: (k1_tarski(A_74)=k1_xboole_0 | ~r2_hidden(A_74, k2_zfmisc_1(k1_tarski(A_74), B_35)))), inference(resolution, [status(thm)], [c_208, c_26])).
% 3.32/1.61  tff(c_357, plain, (![A_74, B_35]: (~r2_hidden(A_74, k2_zfmisc_1(k1_tarski(A_74), B_35)))), inference(negUnitSimplification, [status(thm)], [c_290, c_216])).
% 3.32/1.61  tff(c_571, plain, (![A_174, C_175]: (~r2_hidden(A_174, k1_tarski(k4_tarski(A_174, C_175))))), inference(superposition, [status(thm), theory('equality')], [c_514, c_357])).
% 3.32/1.61  tff(c_574, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_151, c_571])).
% 3.32/1.61  tff(c_677, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_674, c_574])).
% 3.32/1.61  tff(c_678, plain, ('#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_147])).
% 3.32/1.61  tff(c_681, plain, (k4_tarski('#skF_4', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_678, c_94])).
% 3.32/1.61  tff(c_915, plain, (![A_307, B_308, C_309]: (k2_zfmisc_1(k1_tarski(A_307), k2_tarski(B_308, C_309))=k2_tarski(k4_tarski(A_307, B_308), k4_tarski(A_307, C_309)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.32/1.61  tff(c_946, plain, (![A_307, C_309]: (k2_zfmisc_1(k1_tarski(A_307), k2_tarski(C_309, C_309))=k1_tarski(k4_tarski(A_307, C_309)))), inference(superposition, [status(thm), theory('equality')], [c_915, c_6])).
% 3.32/1.61  tff(c_1043, plain, (![A_313, C_314]: (k2_zfmisc_1(k1_tarski(A_313), k1_tarski(C_314))=k1_tarski(k4_tarski(A_313, C_314)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_946])).
% 3.32/1.61  tff(c_771, plain, (![A_231, B_232]: (k3_xboole_0(k1_tarski(A_231), k2_tarski(A_231, B_232))=k1_tarski(A_231))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.32/1.61  tff(c_2, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(A_1, B_2))=k4_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.32/1.61  tff(c_777, plain, (![A_231, B_232]: (k5_xboole_0(k1_tarski(A_231), k1_tarski(A_231))=k4_xboole_0(k1_tarski(A_231), k2_tarski(A_231, B_232)))), inference(superposition, [status(thm), theory('equality')], [c_771, c_2])).
% 3.32/1.61  tff(c_787, plain, (![A_233, B_234]: (k4_xboole_0(k1_tarski(A_233), k2_tarski(A_233, B_234))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_777])).
% 3.32/1.61  tff(c_794, plain, (![A_4]: (k4_xboole_0(k1_tarski(A_4), k1_tarski(A_4))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6, c_787])).
% 3.32/1.61  tff(c_813, plain, (![B_39]: (k1_tarski(B_39)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_794, c_30])).
% 3.32/1.61  tff(c_22, plain, (![A_32, B_33]: (r1_tarski(k1_tarski(A_32), B_33) | ~r2_hidden(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.32/1.61  tff(c_743, plain, (![A_224, B_225]: (~r1_tarski(A_224, k2_zfmisc_1(B_225, A_224)) | k1_xboole_0=A_224)), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.32/1.61  tff(c_748, plain, (![A_32, B_225]: (k1_tarski(A_32)=k1_xboole_0 | ~r2_hidden(A_32, k2_zfmisc_1(B_225, k1_tarski(A_32))))), inference(resolution, [status(thm)], [c_22, c_743])).
% 3.32/1.61  tff(c_888, plain, (![A_32, B_225]: (~r2_hidden(A_32, k2_zfmisc_1(B_225, k1_tarski(A_32))))), inference(negUnitSimplification, [status(thm)], [c_813, c_748])).
% 3.32/1.61  tff(c_1066, plain, (![C_315, A_316]: (~r2_hidden(C_315, k1_tarski(k4_tarski(A_316, C_315))))), inference(superposition, [status(thm), theory('equality')], [c_1043, c_888])).
% 3.32/1.61  tff(c_1069, plain, (~r2_hidden('#skF_3', k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_681, c_1066])).
% 3.32/1.61  tff(c_1167, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1155, c_1069])).
% 3.32/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.32/1.61  
% 3.32/1.61  Inference rules
% 3.32/1.61  ----------------------
% 3.32/1.61  #Ref     : 0
% 3.32/1.61  #Sup     : 265
% 3.32/1.61  #Fact    : 0
% 3.32/1.61  #Define  : 0
% 3.32/1.61  #Split   : 1
% 3.32/1.61  #Chain   : 0
% 3.32/1.61  #Close   : 0
% 3.32/1.61  
% 3.32/1.61  Ordering : KBO
% 3.32/1.61  
% 3.32/1.61  Simplification rules
% 3.32/1.61  ----------------------
% 3.32/1.61  #Subsume      : 8
% 3.32/1.61  #Demod        : 49
% 3.32/1.61  #Tautology    : 146
% 3.32/1.61  #SimpNegUnit  : 14
% 3.32/1.61  #BackRed      : 9
% 3.32/1.61  
% 3.32/1.61  #Partial instantiations: 0
% 3.32/1.61  #Strategies tried      : 1
% 3.32/1.61  
% 3.32/1.61  Timing (in seconds)
% 3.32/1.61  ----------------------
% 3.32/1.61  Preprocessing        : 0.38
% 3.32/1.61  Parsing              : 0.19
% 3.32/1.61  CNF conversion       : 0.03
% 3.32/1.61  Main loop            : 0.40
% 3.32/1.61  Inferencing          : 0.14
% 3.32/1.61  Reduction            : 0.12
% 3.32/1.61  Demodulation         : 0.08
% 3.32/1.61  BG Simplification    : 0.03
% 3.32/1.61  Subsumption          : 0.09
% 3.32/1.61  Abstraction          : 0.03
% 3.32/1.61  MUC search           : 0.00
% 3.32/1.61  Cooper               : 0.00
% 3.32/1.61  Total                : 0.82
% 3.32/1.61  Index Insertion      : 0.00
% 3.32/1.61  Index Deletion       : 0.00
% 3.32/1.61  Index Matching       : 0.00
% 3.32/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
