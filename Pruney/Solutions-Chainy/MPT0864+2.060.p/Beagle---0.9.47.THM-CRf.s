%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:16 EST 2020

% Result     : Theorem 3.26s
% Output     : CNFRefutation 3.45s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 162 expanded)
%              Number of leaves         :   42 (  72 expanded)
%              Depth                    :   10
%              Number of atoms          :  103 ( 190 expanded)
%              Number of equality atoms :   71 ( 152 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_setfam_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_1 > #skF_4

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

tff(f_37,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_39,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_enumset1)).

tff(f_106,negated_conjecture,(
    ~ ! [A] :
        ( ? [B,C] : A = k4_tarski(B,C)
       => ( A != k1_mcart_1(A)
          & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_96,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k1_tarski(A),k2_tarski(B,C)) = k2_tarski(k4_tarski(A,B),k4_tarski(A,C))
      & k2_zfmisc_1(k2_tarski(A,B),k1_tarski(C)) = k2_tarski(k4_tarski(A,C),k4_tarski(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_35,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( r1_tarski(A,k2_zfmisc_1(A,B))
        | r1_tarski(A,k2_zfmisc_1(B,A)) )
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t135_zfmisc_1)).

tff(c_12,plain,(
    ! [A_9] : k2_tarski(A_9,A_9) = k1_tarski(A_9) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [A_10,B_11] : k1_enumset1(A_10,A_10,B_11) = k2_tarski(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ! [A_12,B_13,C_14] : k2_enumset1(A_12,A_12,B_13,C_14) = k1_enumset1(A_12,B_13,C_14) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_18,plain,(
    ! [A_15,B_16,C_17,D_18] : k3_enumset1(A_15,A_15,B_16,C_17,D_18) = k2_enumset1(A_15,B_16,C_17,D_18) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1046,plain,(
    ! [A_263,D_264,B_262,C_260,E_261] : k4_enumset1(A_263,A_263,B_262,C_260,D_264,E_261) = k3_enumset1(A_263,B_262,C_260,D_264,E_261) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_42,plain,(
    ! [E_43,H_48,D_42,A_39,C_41,B_40] : r2_hidden(H_48,k4_enumset1(A_39,B_40,C_41,D_42,E_43,H_48)) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1073,plain,(
    ! [C_266,B_267,A_265,D_269,E_268] : r2_hidden(E_268,k3_enumset1(A_265,B_267,C_266,D_269,E_268)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1046,c_42])).

tff(c_1077,plain,(
    ! [D_270,A_271,B_272,C_273] : r2_hidden(D_270,k2_enumset1(A_271,B_272,C_273,D_270)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_1073])).

tff(c_1081,plain,(
    ! [C_274,A_275,B_276] : r2_hidden(C_274,k1_enumset1(A_275,B_276,C_274)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1077])).

tff(c_1135,plain,(
    ! [B_280,A_281] : r2_hidden(B_280,k2_tarski(A_281,B_280)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1081])).

tff(c_1141,plain,(
    ! [A_9] : r2_hidden(A_9,k1_tarski(A_9)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1135])).

tff(c_626,plain,(
    ! [C_151,D_155,E_152,A_154,B_153] : k4_enumset1(A_154,A_154,B_153,C_151,D_155,E_152) = k3_enumset1(A_154,B_153,C_151,D_155,E_152) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_749,plain,(
    ! [E_165,C_166,D_167,A_169,B_168] : r2_hidden(E_165,k3_enumset1(A_169,B_168,C_166,D_167,E_165)) ),
    inference(superposition,[status(thm),theory(equality)],[c_626,c_42])).

tff(c_753,plain,(
    ! [D_170,A_171,B_172,C_173] : r2_hidden(D_170,k2_enumset1(A_171,B_172,C_173,D_170)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_749])).

tff(c_766,plain,(
    ! [C_180,A_181,B_182] : r2_hidden(C_180,k1_enumset1(A_181,B_182,C_180)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_753])).

tff(c_770,plain,(
    ! [B_183,A_184] : r2_hidden(B_183,k2_tarski(A_184,B_183)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_766])).

tff(c_779,plain,(
    ! [A_9] : r2_hidden(A_9,k1_tarski(A_9)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_770])).

tff(c_90,plain,(
    k4_tarski('#skF_4','#skF_5') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_130,plain,(
    ! [A_58,B_59] : k1_mcart_1(k4_tarski(A_58,B_59)) = A_58 ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_139,plain,(
    k1_mcart_1('#skF_3') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_130])).

tff(c_155,plain,(
    ! [A_61,B_62] : k2_mcart_1(k4_tarski(A_61,B_62)) = B_62 ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_164,plain,(
    k2_mcart_1('#skF_3') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_155])).

tff(c_88,plain,
    ( k2_mcart_1('#skF_3') = '#skF_3'
    | k1_mcart_1('#skF_3') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_171,plain,
    ( '#skF_5' = '#skF_3'
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_164,c_88])).

tff(c_172,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_171])).

tff(c_175,plain,(
    k4_tarski('#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_90])).

tff(c_549,plain,(
    ! [A_144,B_145,C_146] : k2_zfmisc_1(k1_tarski(A_144),k2_tarski(B_145,C_146)) = k2_tarski(k4_tarski(A_144,B_145),k4_tarski(A_144,C_146)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_574,plain,(
    ! [A_144,C_146] : k2_zfmisc_1(k1_tarski(A_144),k2_tarski(C_146,C_146)) = k1_tarski(k4_tarski(A_144,C_146)) ),
    inference(superposition,[status(thm),theory(equality)],[c_549,c_12])).

tff(c_599,plain,(
    ! [A_147,C_148] : k2_zfmisc_1(k1_tarski(A_147),k1_tarski(C_148)) = k1_tarski(k4_tarski(A_147,C_148)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_574])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_8] : k5_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_265,plain,(
    ! [A_79,B_80] : k5_xboole_0(A_79,k3_xboole_0(A_79,B_80)) = k4_xboole_0(A_79,B_80) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_277,plain,(
    ! [A_5] : k5_xboole_0(A_5,k1_xboole_0) = k4_xboole_0(A_5,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_265])).

tff(c_281,plain,(
    ! [A_81] : k4_xboole_0(A_81,k1_xboole_0) = A_81 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_277])).

tff(c_8,plain,(
    ! [A_6,B_7] : k4_xboole_0(A_6,k4_xboole_0(A_6,B_7)) = k3_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_287,plain,(
    ! [A_81] : k4_xboole_0(A_81,A_81) = k3_xboole_0(A_81,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_281,c_8])).

tff(c_292,plain,(
    ! [A_81] : k4_xboole_0(A_81,A_81) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_287])).

tff(c_32,plain,(
    ! [B_35] : k4_xboole_0(k1_tarski(B_35),k1_tarski(B_35)) != k1_tarski(B_35) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_303,plain,(
    ! [B_35] : k1_tarski(B_35) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_292,c_32])).

tff(c_26,plain,(
    ! [A_30,B_31] :
      ( r1_tarski(k1_tarski(A_30),B_31)
      | ~ r2_hidden(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_201,plain,(
    ! [A_65,B_66] :
      ( ~ r1_tarski(A_65,k2_zfmisc_1(A_65,B_66))
      | k1_xboole_0 = A_65 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_206,plain,(
    ! [A_30,B_66] :
      ( k1_tarski(A_30) = k1_xboole_0
      | ~ r2_hidden(A_30,k2_zfmisc_1(k1_tarski(A_30),B_66)) ) ),
    inference(resolution,[status(thm)],[c_26,c_201])).

tff(c_405,plain,(
    ! [A_30,B_66] : ~ r2_hidden(A_30,k2_zfmisc_1(k1_tarski(A_30),B_66)) ),
    inference(negUnitSimplification,[status(thm)],[c_303,c_206])).

tff(c_622,plain,(
    ! [A_149,C_150] : ~ r2_hidden(A_149,k1_tarski(k4_tarski(A_149,C_150))) ),
    inference(superposition,[status(thm),theory(equality)],[c_599,c_405])).

tff(c_625,plain,(
    ~ r2_hidden('#skF_4',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_175,c_622])).

tff(c_782,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_779,c_625])).

tff(c_783,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_171])).

tff(c_786,plain,(
    k4_tarski('#skF_4','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_783,c_90])).

tff(c_1155,plain,(
    ! [A_295,B_296,C_297] : k2_zfmisc_1(k2_tarski(A_295,B_296),k1_tarski(C_297)) = k2_tarski(k4_tarski(A_295,C_297),k4_tarski(B_296,C_297)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1190,plain,(
    ! [B_296,C_297] : k2_zfmisc_1(k2_tarski(B_296,B_296),k1_tarski(C_297)) = k1_tarski(k4_tarski(B_296,C_297)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1155,c_12])).

tff(c_1306,plain,(
    ! [B_339,C_340] : k2_zfmisc_1(k1_tarski(B_339),k1_tarski(C_340)) = k1_tarski(k4_tarski(B_339,C_340)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1190])).

tff(c_872,plain,(
    ! [A_201,B_202] : k5_xboole_0(A_201,k3_xboole_0(A_201,B_202)) = k4_xboole_0(A_201,B_202) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_884,plain,(
    ! [A_5] : k5_xboole_0(A_5,k1_xboole_0) = k4_xboole_0(A_5,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_872])).

tff(c_888,plain,(
    ! [A_203] : k4_xboole_0(A_203,k1_xboole_0) = A_203 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_884])).

tff(c_894,plain,(
    ! [A_203] : k4_xboole_0(A_203,A_203) = k3_xboole_0(A_203,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_888,c_8])).

tff(c_899,plain,(
    ! [A_203] : k4_xboole_0(A_203,A_203) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_894])).

tff(c_901,plain,(
    ! [B_35] : k1_tarski(B_35) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_899,c_32])).

tff(c_819,plain,(
    ! [A_192,B_193] :
      ( r1_tarski(k1_tarski(A_192),B_193)
      | ~ r2_hidden(A_192,B_193) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_28,plain,(
    ! [A_32,B_33] :
      ( ~ r1_tarski(A_32,k2_zfmisc_1(B_33,A_32))
      | k1_xboole_0 = A_32 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_828,plain,(
    ! [A_192,B_33] :
      ( k1_tarski(A_192) = k1_xboole_0
      | ~ r2_hidden(A_192,k2_zfmisc_1(B_33,k1_tarski(A_192))) ) ),
    inference(resolution,[status(thm)],[c_819,c_28])).

tff(c_1008,plain,(
    ! [A_192,B_33] : ~ r2_hidden(A_192,k2_zfmisc_1(B_33,k1_tarski(A_192))) ),
    inference(negUnitSimplification,[status(thm)],[c_901,c_828])).

tff(c_1334,plain,(
    ! [C_350,B_351] : ~ r2_hidden(C_350,k1_tarski(k4_tarski(B_351,C_350))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1306,c_1008])).

tff(c_1337,plain,(
    ~ r2_hidden('#skF_3',k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_786,c_1334])).

tff(c_1340,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1141,c_1337])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:38:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.26/1.51  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.26/1.52  
% 3.26/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.26/1.52  %$ r2_hidden > r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_setfam_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_1 > #skF_4
% 3.26/1.52  
% 3.26/1.52  %Foreground sorts:
% 3.26/1.52  
% 3.26/1.52  
% 3.26/1.52  %Background operators:
% 3.26/1.52  
% 3.26/1.52  
% 3.26/1.52  %Foreground operators:
% 3.26/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.26/1.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.26/1.52  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.26/1.52  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.26/1.52  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.26/1.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.26/1.52  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.26/1.52  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.26/1.52  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.26/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.26/1.52  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.26/1.52  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.26/1.52  tff('#skF_5', type, '#skF_5': $i).
% 3.26/1.52  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.26/1.52  tff('#skF_3', type, '#skF_3': $i).
% 3.26/1.52  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.26/1.52  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.26/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.26/1.52  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 3.26/1.52  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.26/1.52  tff('#skF_4', type, '#skF_4': $i).
% 3.26/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.26/1.52  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 3.26/1.52  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.26/1.52  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.26/1.52  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.26/1.52  
% 3.45/1.53  tff(f_37, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.45/1.53  tff(f_39, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.45/1.53  tff(f_41, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 3.45/1.53  tff(f_43, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 3.45/1.53  tff(f_45, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 3.45/1.53  tff(f_90, axiom, (![A, B, C, D, E, F, G]: ((G = k4_enumset1(A, B, C, D, E, F)) <=> (![H]: (r2_hidden(H, G) <=> ~(((((~(H = A) & ~(H = B)) & ~(H = C)) & ~(H = D)) & ~(H = E)) & ~(H = F)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_enumset1)).
% 3.45/1.54  tff(f_106, negated_conjecture, ~(![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_mcart_1)).
% 3.45/1.54  tff(f_96, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 3.45/1.54  tff(f_66, axiom, (![A, B, C]: ((k2_zfmisc_1(k1_tarski(A), k2_tarski(B, C)) = k2_tarski(k4_tarski(A, B), k4_tarski(A, C))) & (k2_zfmisc_1(k2_tarski(A, B), k1_tarski(C)) = k2_tarski(k4_tarski(A, C), k4_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_zfmisc_1)).
% 3.45/1.54  tff(f_31, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 3.45/1.54  tff(f_35, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 3.45/1.54  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.45/1.54  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.45/1.54  tff(f_62, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 3.45/1.54  tff(f_51, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.45/1.54  tff(f_57, axiom, (![A, B]: ((r1_tarski(A, k2_zfmisc_1(A, B)) | r1_tarski(A, k2_zfmisc_1(B, A))) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t135_zfmisc_1)).
% 3.45/1.54  tff(c_12, plain, (![A_9]: (k2_tarski(A_9, A_9)=k1_tarski(A_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.45/1.54  tff(c_14, plain, (![A_10, B_11]: (k1_enumset1(A_10, A_10, B_11)=k2_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.45/1.54  tff(c_16, plain, (![A_12, B_13, C_14]: (k2_enumset1(A_12, A_12, B_13, C_14)=k1_enumset1(A_12, B_13, C_14))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.45/1.54  tff(c_18, plain, (![A_15, B_16, C_17, D_18]: (k3_enumset1(A_15, A_15, B_16, C_17, D_18)=k2_enumset1(A_15, B_16, C_17, D_18))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.45/1.54  tff(c_1046, plain, (![A_263, D_264, B_262, C_260, E_261]: (k4_enumset1(A_263, A_263, B_262, C_260, D_264, E_261)=k3_enumset1(A_263, B_262, C_260, D_264, E_261))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.45/1.54  tff(c_42, plain, (![E_43, H_48, D_42, A_39, C_41, B_40]: (r2_hidden(H_48, k4_enumset1(A_39, B_40, C_41, D_42, E_43, H_48)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.45/1.54  tff(c_1073, plain, (![C_266, B_267, A_265, D_269, E_268]: (r2_hidden(E_268, k3_enumset1(A_265, B_267, C_266, D_269, E_268)))), inference(superposition, [status(thm), theory('equality')], [c_1046, c_42])).
% 3.45/1.54  tff(c_1077, plain, (![D_270, A_271, B_272, C_273]: (r2_hidden(D_270, k2_enumset1(A_271, B_272, C_273, D_270)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_1073])).
% 3.45/1.54  tff(c_1081, plain, (![C_274, A_275, B_276]: (r2_hidden(C_274, k1_enumset1(A_275, B_276, C_274)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_1077])).
% 3.45/1.54  tff(c_1135, plain, (![B_280, A_281]: (r2_hidden(B_280, k2_tarski(A_281, B_280)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_1081])).
% 3.45/1.54  tff(c_1141, plain, (![A_9]: (r2_hidden(A_9, k1_tarski(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_1135])).
% 3.45/1.54  tff(c_626, plain, (![C_151, D_155, E_152, A_154, B_153]: (k4_enumset1(A_154, A_154, B_153, C_151, D_155, E_152)=k3_enumset1(A_154, B_153, C_151, D_155, E_152))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.45/1.54  tff(c_749, plain, (![E_165, C_166, D_167, A_169, B_168]: (r2_hidden(E_165, k3_enumset1(A_169, B_168, C_166, D_167, E_165)))), inference(superposition, [status(thm), theory('equality')], [c_626, c_42])).
% 3.45/1.54  tff(c_753, plain, (![D_170, A_171, B_172, C_173]: (r2_hidden(D_170, k2_enumset1(A_171, B_172, C_173, D_170)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_749])).
% 3.45/1.54  tff(c_766, plain, (![C_180, A_181, B_182]: (r2_hidden(C_180, k1_enumset1(A_181, B_182, C_180)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_753])).
% 3.45/1.54  tff(c_770, plain, (![B_183, A_184]: (r2_hidden(B_183, k2_tarski(A_184, B_183)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_766])).
% 3.45/1.54  tff(c_779, plain, (![A_9]: (r2_hidden(A_9, k1_tarski(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_770])).
% 3.45/1.54  tff(c_90, plain, (k4_tarski('#skF_4', '#skF_5')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.45/1.54  tff(c_130, plain, (![A_58, B_59]: (k1_mcart_1(k4_tarski(A_58, B_59))=A_58)), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.45/1.54  tff(c_139, plain, (k1_mcart_1('#skF_3')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_90, c_130])).
% 3.45/1.54  tff(c_155, plain, (![A_61, B_62]: (k2_mcart_1(k4_tarski(A_61, B_62))=B_62)), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.45/1.54  tff(c_164, plain, (k2_mcart_1('#skF_3')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_90, c_155])).
% 3.45/1.54  tff(c_88, plain, (k2_mcart_1('#skF_3')='#skF_3' | k1_mcart_1('#skF_3')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.45/1.54  tff(c_171, plain, ('#skF_5'='#skF_3' | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_139, c_164, c_88])).
% 3.45/1.54  tff(c_172, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_171])).
% 3.45/1.54  tff(c_175, plain, (k4_tarski('#skF_4', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_172, c_90])).
% 3.45/1.54  tff(c_549, plain, (![A_144, B_145, C_146]: (k2_zfmisc_1(k1_tarski(A_144), k2_tarski(B_145, C_146))=k2_tarski(k4_tarski(A_144, B_145), k4_tarski(A_144, C_146)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.45/1.54  tff(c_574, plain, (![A_144, C_146]: (k2_zfmisc_1(k1_tarski(A_144), k2_tarski(C_146, C_146))=k1_tarski(k4_tarski(A_144, C_146)))), inference(superposition, [status(thm), theory('equality')], [c_549, c_12])).
% 3.45/1.54  tff(c_599, plain, (![A_147, C_148]: (k2_zfmisc_1(k1_tarski(A_147), k1_tarski(C_148))=k1_tarski(k4_tarski(A_147, C_148)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_574])).
% 3.45/1.54  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.45/1.54  tff(c_10, plain, (![A_8]: (k5_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.45/1.54  tff(c_265, plain, (![A_79, B_80]: (k5_xboole_0(A_79, k3_xboole_0(A_79, B_80))=k4_xboole_0(A_79, B_80))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.45/1.54  tff(c_277, plain, (![A_5]: (k5_xboole_0(A_5, k1_xboole_0)=k4_xboole_0(A_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_265])).
% 3.45/1.54  tff(c_281, plain, (![A_81]: (k4_xboole_0(A_81, k1_xboole_0)=A_81)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_277])).
% 3.45/1.54  tff(c_8, plain, (![A_6, B_7]: (k4_xboole_0(A_6, k4_xboole_0(A_6, B_7))=k3_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.45/1.54  tff(c_287, plain, (![A_81]: (k4_xboole_0(A_81, A_81)=k3_xboole_0(A_81, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_281, c_8])).
% 3.45/1.54  tff(c_292, plain, (![A_81]: (k4_xboole_0(A_81, A_81)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_287])).
% 3.45/1.54  tff(c_32, plain, (![B_35]: (k4_xboole_0(k1_tarski(B_35), k1_tarski(B_35))!=k1_tarski(B_35))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.45/1.54  tff(c_303, plain, (![B_35]: (k1_tarski(B_35)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_292, c_32])).
% 3.45/1.54  tff(c_26, plain, (![A_30, B_31]: (r1_tarski(k1_tarski(A_30), B_31) | ~r2_hidden(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.45/1.54  tff(c_201, plain, (![A_65, B_66]: (~r1_tarski(A_65, k2_zfmisc_1(A_65, B_66)) | k1_xboole_0=A_65)), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.45/1.54  tff(c_206, plain, (![A_30, B_66]: (k1_tarski(A_30)=k1_xboole_0 | ~r2_hidden(A_30, k2_zfmisc_1(k1_tarski(A_30), B_66)))), inference(resolution, [status(thm)], [c_26, c_201])).
% 3.45/1.54  tff(c_405, plain, (![A_30, B_66]: (~r2_hidden(A_30, k2_zfmisc_1(k1_tarski(A_30), B_66)))), inference(negUnitSimplification, [status(thm)], [c_303, c_206])).
% 3.45/1.54  tff(c_622, plain, (![A_149, C_150]: (~r2_hidden(A_149, k1_tarski(k4_tarski(A_149, C_150))))), inference(superposition, [status(thm), theory('equality')], [c_599, c_405])).
% 3.45/1.54  tff(c_625, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_175, c_622])).
% 3.45/1.54  tff(c_782, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_779, c_625])).
% 3.45/1.54  tff(c_783, plain, ('#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_171])).
% 3.45/1.54  tff(c_786, plain, (k4_tarski('#skF_4', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_783, c_90])).
% 3.45/1.54  tff(c_1155, plain, (![A_295, B_296, C_297]: (k2_zfmisc_1(k2_tarski(A_295, B_296), k1_tarski(C_297))=k2_tarski(k4_tarski(A_295, C_297), k4_tarski(B_296, C_297)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.45/1.54  tff(c_1190, plain, (![B_296, C_297]: (k2_zfmisc_1(k2_tarski(B_296, B_296), k1_tarski(C_297))=k1_tarski(k4_tarski(B_296, C_297)))), inference(superposition, [status(thm), theory('equality')], [c_1155, c_12])).
% 3.45/1.54  tff(c_1306, plain, (![B_339, C_340]: (k2_zfmisc_1(k1_tarski(B_339), k1_tarski(C_340))=k1_tarski(k4_tarski(B_339, C_340)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1190])).
% 3.45/1.54  tff(c_872, plain, (![A_201, B_202]: (k5_xboole_0(A_201, k3_xboole_0(A_201, B_202))=k4_xboole_0(A_201, B_202))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.45/1.54  tff(c_884, plain, (![A_5]: (k5_xboole_0(A_5, k1_xboole_0)=k4_xboole_0(A_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_872])).
% 3.45/1.54  tff(c_888, plain, (![A_203]: (k4_xboole_0(A_203, k1_xboole_0)=A_203)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_884])).
% 3.45/1.54  tff(c_894, plain, (![A_203]: (k4_xboole_0(A_203, A_203)=k3_xboole_0(A_203, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_888, c_8])).
% 3.45/1.54  tff(c_899, plain, (![A_203]: (k4_xboole_0(A_203, A_203)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_894])).
% 3.45/1.54  tff(c_901, plain, (![B_35]: (k1_tarski(B_35)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_899, c_32])).
% 3.45/1.54  tff(c_819, plain, (![A_192, B_193]: (r1_tarski(k1_tarski(A_192), B_193) | ~r2_hidden(A_192, B_193))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.45/1.54  tff(c_28, plain, (![A_32, B_33]: (~r1_tarski(A_32, k2_zfmisc_1(B_33, A_32)) | k1_xboole_0=A_32)), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.45/1.54  tff(c_828, plain, (![A_192, B_33]: (k1_tarski(A_192)=k1_xboole_0 | ~r2_hidden(A_192, k2_zfmisc_1(B_33, k1_tarski(A_192))))), inference(resolution, [status(thm)], [c_819, c_28])).
% 3.45/1.54  tff(c_1008, plain, (![A_192, B_33]: (~r2_hidden(A_192, k2_zfmisc_1(B_33, k1_tarski(A_192))))), inference(negUnitSimplification, [status(thm)], [c_901, c_828])).
% 3.45/1.54  tff(c_1334, plain, (![C_350, B_351]: (~r2_hidden(C_350, k1_tarski(k4_tarski(B_351, C_350))))), inference(superposition, [status(thm), theory('equality')], [c_1306, c_1008])).
% 3.45/1.54  tff(c_1337, plain, (~r2_hidden('#skF_3', k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_786, c_1334])).
% 3.45/1.54  tff(c_1340, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1141, c_1337])).
% 3.45/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.45/1.54  
% 3.45/1.54  Inference rules
% 3.45/1.54  ----------------------
% 3.45/1.54  #Ref     : 0
% 3.45/1.54  #Sup     : 298
% 3.45/1.54  #Fact    : 0
% 3.45/1.54  #Define  : 0
% 3.45/1.54  #Split   : 1
% 3.45/1.54  #Chain   : 0
% 3.45/1.54  #Close   : 0
% 3.45/1.54  
% 3.45/1.54  Ordering : KBO
% 3.45/1.54  
% 3.45/1.54  Simplification rules
% 3.45/1.54  ----------------------
% 3.45/1.54  #Subsume      : 9
% 3.45/1.54  #Demod        : 100
% 3.45/1.54  #Tautology    : 176
% 3.45/1.54  #SimpNegUnit  : 20
% 3.45/1.54  #BackRed      : 8
% 3.45/1.54  
% 3.45/1.54  #Partial instantiations: 0
% 3.45/1.54  #Strategies tried      : 1
% 3.45/1.54  
% 3.45/1.54  Timing (in seconds)
% 3.45/1.54  ----------------------
% 3.45/1.54  Preprocessing        : 0.34
% 3.45/1.54  Parsing              : 0.17
% 3.45/1.54  CNF conversion       : 0.03
% 3.45/1.54  Main loop            : 0.41
% 3.45/1.54  Inferencing          : 0.15
% 3.45/1.54  Reduction            : 0.13
% 3.45/1.54  Demodulation         : 0.09
% 3.45/1.54  BG Simplification    : 0.03
% 3.45/1.54  Subsumption          : 0.08
% 3.45/1.54  Abstraction          : 0.03
% 3.45/1.54  MUC search           : 0.00
% 3.45/1.54  Cooper               : 0.00
% 3.45/1.54  Total                : 0.79
% 3.45/1.54  Index Insertion      : 0.00
% 3.45/1.54  Index Deletion       : 0.00
% 3.45/1.54  Index Matching       : 0.00
% 3.45/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
