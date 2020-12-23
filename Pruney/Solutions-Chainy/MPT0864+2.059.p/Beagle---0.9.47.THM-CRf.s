%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:16 EST 2020

% Result     : Theorem 3.04s
% Output     : CNFRefutation 3.38s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 154 expanded)
%              Number of leaves         :   42 (  70 expanded)
%              Depth                    :    9
%              Number of atoms          :  112 ( 207 expanded)
%              Number of equality atoms :   57 ( 142 expanded)
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

tff(f_41,axiom,(
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

tff(f_33,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_35,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

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

tff(f_55,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( r1_tarski(A,k2_zfmisc_1(A,B))
        | r1_tarski(A,k2_zfmisc_1(B,A)) )
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t135_zfmisc_1)).

tff(c_616,plain,(
    ! [A_268,E_267,B_266,C_270,D_269] : k4_enumset1(A_268,A_268,B_266,C_270,D_269,E_267) = k3_enumset1(A_268,B_266,C_270,D_269,E_267) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_52,plain,(
    ! [C_46,E_48,F_49,H_53,B_45,D_47] : r2_hidden(H_53,k4_enumset1(H_53,B_45,C_46,D_47,E_48,F_49)) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_625,plain,(
    ! [A_268,E_267,B_266,C_270,D_269] : r2_hidden(A_268,k3_enumset1(A_268,B_266,C_270,D_269,E_267)) ),
    inference(superposition,[status(thm),theory(equality)],[c_616,c_52])).

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

tff(c_44,plain,(
    ! [C_46,F_49,H_53,A_44,B_45,D_47] : r2_hidden(H_53,k4_enumset1(A_44,B_45,C_46,D_47,H_53,F_49)) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_643,plain,(
    ! [A_274,C_275,E_271,D_272,B_273] : r2_hidden(D_272,k3_enumset1(A_274,B_273,C_275,D_272,E_271)) ),
    inference(superposition,[status(thm),theory(equality)],[c_616,c_44])).

tff(c_647,plain,(
    ! [C_276,A_277,B_278,D_279] : r2_hidden(C_276,k2_enumset1(A_277,B_278,C_276,D_279)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_643])).

tff(c_651,plain,(
    ! [B_280,A_281,C_282] : r2_hidden(B_280,k1_enumset1(A_281,B_280,C_282)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_647])).

tff(c_677,plain,(
    ! [A_287,B_288] : r2_hidden(A_287,k2_tarski(A_287,B_288)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_651])).

tff(c_680,plain,(
    ! [A_6] : r2_hidden(A_6,k1_tarski(A_6)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_677])).

tff(c_313,plain,(
    ! [D_149,A_148,E_147,B_146,C_150] : k4_enumset1(A_148,A_148,B_146,C_150,D_149,E_147) = k3_enumset1(A_148,B_146,C_150,D_149,E_147) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_46,plain,(
    ! [C_46,E_48,F_49,H_53,A_44,B_45] : r2_hidden(H_53,k4_enumset1(A_44,B_45,C_46,H_53,E_48,F_49)) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_384,plain,(
    ! [C_176,B_177,A_175,D_178,E_179] : r2_hidden(C_176,k3_enumset1(A_175,B_177,C_176,D_178,E_179)) ),
    inference(superposition,[status(thm),theory(equality)],[c_313,c_46])).

tff(c_387,plain,(
    ! [B_13,A_12,C_14,D_15] : r2_hidden(B_13,k2_enumset1(A_12,B_13,C_14,D_15)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_384])).

tff(c_48,plain,(
    ! [E_48,F_49,H_53,A_44,B_45,D_47] : r2_hidden(H_53,k4_enumset1(A_44,B_45,H_53,D_47,E_48,F_49)) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_340,plain,(
    ! [E_155,C_152,B_153,D_154,A_151] : r2_hidden(B_153,k3_enumset1(A_151,B_153,C_152,D_154,E_155)) ),
    inference(superposition,[status(thm),theory(equality)],[c_313,c_48])).

tff(c_344,plain,(
    ! [A_156,B_157,C_158,D_159] : r2_hidden(A_156,k2_enumset1(A_156,B_157,C_158,D_159)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_340])).

tff(c_348,plain,(
    ! [A_160,B_161,C_162] : r2_hidden(A_160,k1_enumset1(A_160,B_161,C_162)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_344])).

tff(c_352,plain,(
    ! [A_163,B_164] : r2_hidden(A_163,k2_tarski(A_163,B_164)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_348])).

tff(c_355,plain,(
    ! [A_6] : r2_hidden(A_6,k1_tarski(A_6)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_352])).

tff(c_90,plain,(
    k4_tarski('#skF_4','#skF_5') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_120,plain,(
    ! [A_63,B_64] : k1_mcart_1(k4_tarski(A_63,B_64)) = A_63 ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_129,plain,(
    k1_mcart_1('#skF_3') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_120])).

tff(c_132,plain,(
    ! [A_65,B_66] : k2_mcart_1(k4_tarski(A_65,B_66)) = B_66 ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_141,plain,(
    k2_mcart_1('#skF_3') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_132])).

tff(c_88,plain,
    ( k2_mcart_1('#skF_3') = '#skF_3'
    | k1_mcart_1('#skF_3') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_152,plain,
    ( '#skF_5' = '#skF_3'
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_141,c_88])).

tff(c_153,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_152])).

tff(c_156,plain,(
    k4_tarski('#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_90])).

tff(c_357,plain,(
    ! [A_166,B_167,C_168,D_169] :
      ( r2_hidden(k4_tarski(A_166,B_167),k2_zfmisc_1(C_168,D_169))
      | ~ r2_hidden(B_167,D_169)
      | ~ r2_hidden(A_166,C_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_393,plain,(
    ! [C_184,D_185] :
      ( r2_hidden('#skF_4',k2_zfmisc_1(C_184,D_185))
      | ~ r2_hidden('#skF_5',D_185)
      | ~ r2_hidden('#skF_4',C_184) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_357])).

tff(c_6,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_231,plain,(
    ! [A_81,B_82] : k5_xboole_0(A_81,k3_xboole_0(A_81,B_82)) = k4_xboole_0(A_81,B_82) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_240,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_231])).

tff(c_243,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_240])).

tff(c_36,plain,(
    ! [B_43] : k4_xboole_0(k1_tarski(B_43),k1_tarski(B_43)) != k1_tarski(B_43) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_244,plain,(
    ! [B_43] : k1_tarski(B_43) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_243,c_36])).

tff(c_205,plain,(
    ! [A_74,B_75] :
      ( r1_tarski(k1_tarski(A_74),B_75)
      | ~ r2_hidden(A_74,B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_34,plain,(
    ! [A_40,B_41] :
      ( ~ r1_tarski(A_40,k2_zfmisc_1(A_40,B_41))
      | k1_xboole_0 = A_40 ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_215,plain,(
    ! [A_74,B_41] :
      ( k1_tarski(A_74) = k1_xboole_0
      | ~ r2_hidden(A_74,k2_zfmisc_1(k1_tarski(A_74),B_41)) ) ),
    inference(resolution,[status(thm)],[c_205,c_34])).

tff(c_290,plain,(
    ! [A_74,B_41] : ~ r2_hidden(A_74,k2_zfmisc_1(k1_tarski(A_74),B_41)) ),
    inference(negUnitSimplification,[status(thm)],[c_244,c_215])).

tff(c_407,plain,(
    ! [D_185] :
      ( ~ r2_hidden('#skF_5',D_185)
      | ~ r2_hidden('#skF_4',k1_tarski('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_393,c_290])).

tff(c_415,plain,(
    ! [D_186] : ~ r2_hidden('#skF_5',D_186) ),
    inference(demodulation,[status(thm),theory(equality)],[c_355,c_407])).

tff(c_459,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_387,c_415])).

tff(c_460,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_152])).

tff(c_463,plain,(
    k4_tarski('#skF_4','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_460,c_90])).

tff(c_655,plain,(
    ! [A_283,B_284,C_285,D_286] :
      ( r2_hidden(k4_tarski(A_283,B_284),k2_zfmisc_1(C_285,D_286))
      | ~ r2_hidden(B_284,D_286)
      | ~ r2_hidden(A_283,C_285) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_686,plain,(
    ! [C_295,D_296] :
      ( r2_hidden('#skF_3',k2_zfmisc_1(C_295,D_296))
      | ~ r2_hidden('#skF_3',D_296)
      | ~ r2_hidden('#skF_4',C_295) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_463,c_655])).

tff(c_534,plain,(
    ! [A_201,B_202] : k5_xboole_0(A_201,k3_xboole_0(A_201,B_202)) = k4_xboole_0(A_201,B_202) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_543,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_534])).

tff(c_546,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_543])).

tff(c_547,plain,(
    ! [B_43] : k1_tarski(B_43) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_546,c_36])).

tff(c_24,plain,(
    ! [A_34,B_35] :
      ( r1_tarski(k1_tarski(A_34),B_35)
      | ~ r2_hidden(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_500,plain,(
    ! [A_193,B_194] :
      ( ~ r1_tarski(A_193,k2_zfmisc_1(B_194,A_193))
      | k1_xboole_0 = A_193 ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_505,plain,(
    ! [A_34,B_194] :
      ( k1_tarski(A_34) = k1_xboole_0
      | ~ r2_hidden(A_34,k2_zfmisc_1(B_194,k1_tarski(A_34))) ) ),
    inference(resolution,[status(thm)],[c_24,c_500])).

tff(c_593,plain,(
    ! [A_34,B_194] : ~ r2_hidden(A_34,k2_zfmisc_1(B_194,k1_tarski(A_34))) ),
    inference(negUnitSimplification,[status(thm)],[c_547,c_505])).

tff(c_700,plain,(
    ! [C_295] :
      ( ~ r2_hidden('#skF_3',k1_tarski('#skF_3'))
      | ~ r2_hidden('#skF_4',C_295) ) ),
    inference(resolution,[status(thm)],[c_686,c_593])).

tff(c_708,plain,(
    ! [C_297] : ~ r2_hidden('#skF_4',C_297) ),
    inference(demodulation,[status(thm),theory(equality)],[c_680,c_700])).

tff(c_746,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_625,c_708])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:41:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.04/1.59  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.04/1.60  
% 3.04/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.04/1.60  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_setfam_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_1 > #skF_4
% 3.04/1.60  
% 3.04/1.60  %Foreground sorts:
% 3.04/1.60  
% 3.04/1.60  
% 3.04/1.60  %Background operators:
% 3.04/1.60  
% 3.04/1.60  
% 3.04/1.60  %Foreground operators:
% 3.04/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.04/1.60  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.04/1.60  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.04/1.60  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.04/1.60  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.04/1.60  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.04/1.60  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.04/1.60  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.04/1.60  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.04/1.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.04/1.60  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.04/1.60  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.04/1.60  tff('#skF_5', type, '#skF_5': $i).
% 3.04/1.60  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.04/1.60  tff('#skF_3', type, '#skF_3': $i).
% 3.04/1.60  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.04/1.60  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.04/1.60  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.04/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.04/1.60  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 3.04/1.60  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.04/1.60  tff('#skF_4', type, '#skF_4': $i).
% 3.04/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.04/1.60  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 3.04/1.60  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.04/1.60  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.04/1.60  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.04/1.60  
% 3.38/1.62  tff(f_41, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 3.38/1.62  tff(f_90, axiom, (![A, B, C, D, E, F, G]: ((G = k4_enumset1(A, B, C, D, E, F)) <=> (![H]: (r2_hidden(H, G) <=> ~(((((~(H = A) & ~(H = B)) & ~(H = C)) & ~(H = D)) & ~(H = E)) & ~(H = F)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_enumset1)).
% 3.38/1.62  tff(f_33, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.38/1.62  tff(f_35, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.38/1.62  tff(f_37, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 3.38/1.62  tff(f_39, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 3.38/1.62  tff(f_106, negated_conjecture, ~(![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_mcart_1)).
% 3.38/1.62  tff(f_96, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 3.38/1.62  tff(f_55, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 3.38/1.62  tff(f_31, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.38/1.62  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 3.38/1.62  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.38/1.62  tff(f_66, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 3.38/1.62  tff(f_49, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.38/1.62  tff(f_61, axiom, (![A, B]: ((r1_tarski(A, k2_zfmisc_1(A, B)) | r1_tarski(A, k2_zfmisc_1(B, A))) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t135_zfmisc_1)).
% 3.38/1.62  tff(c_616, plain, (![A_268, E_267, B_266, C_270, D_269]: (k4_enumset1(A_268, A_268, B_266, C_270, D_269, E_267)=k3_enumset1(A_268, B_266, C_270, D_269, E_267))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.38/1.62  tff(c_52, plain, (![C_46, E_48, F_49, H_53, B_45, D_47]: (r2_hidden(H_53, k4_enumset1(H_53, B_45, C_46, D_47, E_48, F_49)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.38/1.62  tff(c_625, plain, (![A_268, E_267, B_266, C_270, D_269]: (r2_hidden(A_268, k3_enumset1(A_268, B_266, C_270, D_269, E_267)))), inference(superposition, [status(thm), theory('equality')], [c_616, c_52])).
% 3.38/1.62  tff(c_8, plain, (![A_6]: (k2_tarski(A_6, A_6)=k1_tarski(A_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.38/1.62  tff(c_10, plain, (![A_7, B_8]: (k1_enumset1(A_7, A_7, B_8)=k2_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.38/1.62  tff(c_12, plain, (![A_9, B_10, C_11]: (k2_enumset1(A_9, A_9, B_10, C_11)=k1_enumset1(A_9, B_10, C_11))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.38/1.62  tff(c_14, plain, (![A_12, B_13, C_14, D_15]: (k3_enumset1(A_12, A_12, B_13, C_14, D_15)=k2_enumset1(A_12, B_13, C_14, D_15))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.38/1.62  tff(c_44, plain, (![C_46, F_49, H_53, A_44, B_45, D_47]: (r2_hidden(H_53, k4_enumset1(A_44, B_45, C_46, D_47, H_53, F_49)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.38/1.62  tff(c_643, plain, (![A_274, C_275, E_271, D_272, B_273]: (r2_hidden(D_272, k3_enumset1(A_274, B_273, C_275, D_272, E_271)))), inference(superposition, [status(thm), theory('equality')], [c_616, c_44])).
% 3.38/1.62  tff(c_647, plain, (![C_276, A_277, B_278, D_279]: (r2_hidden(C_276, k2_enumset1(A_277, B_278, C_276, D_279)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_643])).
% 3.38/1.62  tff(c_651, plain, (![B_280, A_281, C_282]: (r2_hidden(B_280, k1_enumset1(A_281, B_280, C_282)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_647])).
% 3.38/1.62  tff(c_677, plain, (![A_287, B_288]: (r2_hidden(A_287, k2_tarski(A_287, B_288)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_651])).
% 3.38/1.62  tff(c_680, plain, (![A_6]: (r2_hidden(A_6, k1_tarski(A_6)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_677])).
% 3.38/1.62  tff(c_313, plain, (![D_149, A_148, E_147, B_146, C_150]: (k4_enumset1(A_148, A_148, B_146, C_150, D_149, E_147)=k3_enumset1(A_148, B_146, C_150, D_149, E_147))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.38/1.62  tff(c_46, plain, (![C_46, E_48, F_49, H_53, A_44, B_45]: (r2_hidden(H_53, k4_enumset1(A_44, B_45, C_46, H_53, E_48, F_49)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.38/1.62  tff(c_384, plain, (![C_176, B_177, A_175, D_178, E_179]: (r2_hidden(C_176, k3_enumset1(A_175, B_177, C_176, D_178, E_179)))), inference(superposition, [status(thm), theory('equality')], [c_313, c_46])).
% 3.38/1.62  tff(c_387, plain, (![B_13, A_12, C_14, D_15]: (r2_hidden(B_13, k2_enumset1(A_12, B_13, C_14, D_15)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_384])).
% 3.38/1.62  tff(c_48, plain, (![E_48, F_49, H_53, A_44, B_45, D_47]: (r2_hidden(H_53, k4_enumset1(A_44, B_45, H_53, D_47, E_48, F_49)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.38/1.62  tff(c_340, plain, (![E_155, C_152, B_153, D_154, A_151]: (r2_hidden(B_153, k3_enumset1(A_151, B_153, C_152, D_154, E_155)))), inference(superposition, [status(thm), theory('equality')], [c_313, c_48])).
% 3.38/1.62  tff(c_344, plain, (![A_156, B_157, C_158, D_159]: (r2_hidden(A_156, k2_enumset1(A_156, B_157, C_158, D_159)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_340])).
% 3.38/1.62  tff(c_348, plain, (![A_160, B_161, C_162]: (r2_hidden(A_160, k1_enumset1(A_160, B_161, C_162)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_344])).
% 3.38/1.62  tff(c_352, plain, (![A_163, B_164]: (r2_hidden(A_163, k2_tarski(A_163, B_164)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_348])).
% 3.38/1.62  tff(c_355, plain, (![A_6]: (r2_hidden(A_6, k1_tarski(A_6)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_352])).
% 3.38/1.62  tff(c_90, plain, (k4_tarski('#skF_4', '#skF_5')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.38/1.62  tff(c_120, plain, (![A_63, B_64]: (k1_mcart_1(k4_tarski(A_63, B_64))=A_63)), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.38/1.62  tff(c_129, plain, (k1_mcart_1('#skF_3')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_90, c_120])).
% 3.38/1.62  tff(c_132, plain, (![A_65, B_66]: (k2_mcart_1(k4_tarski(A_65, B_66))=B_66)), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.38/1.62  tff(c_141, plain, (k2_mcart_1('#skF_3')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_90, c_132])).
% 3.38/1.62  tff(c_88, plain, (k2_mcart_1('#skF_3')='#skF_3' | k1_mcart_1('#skF_3')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.38/1.62  tff(c_152, plain, ('#skF_5'='#skF_3' | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_129, c_141, c_88])).
% 3.38/1.62  tff(c_153, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_152])).
% 3.38/1.62  tff(c_156, plain, (k4_tarski('#skF_4', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_153, c_90])).
% 3.38/1.62  tff(c_357, plain, (![A_166, B_167, C_168, D_169]: (r2_hidden(k4_tarski(A_166, B_167), k2_zfmisc_1(C_168, D_169)) | ~r2_hidden(B_167, D_169) | ~r2_hidden(A_166, C_168))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.38/1.62  tff(c_393, plain, (![C_184, D_185]: (r2_hidden('#skF_4', k2_zfmisc_1(C_184, D_185)) | ~r2_hidden('#skF_5', D_185) | ~r2_hidden('#skF_4', C_184))), inference(superposition, [status(thm), theory('equality')], [c_156, c_357])).
% 3.38/1.62  tff(c_6, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.38/1.62  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.38/1.62  tff(c_231, plain, (![A_81, B_82]: (k5_xboole_0(A_81, k3_xboole_0(A_81, B_82))=k4_xboole_0(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.38/1.62  tff(c_240, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_231])).
% 3.38/1.62  tff(c_243, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_240])).
% 3.38/1.62  tff(c_36, plain, (![B_43]: (k4_xboole_0(k1_tarski(B_43), k1_tarski(B_43))!=k1_tarski(B_43))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.38/1.62  tff(c_244, plain, (![B_43]: (k1_tarski(B_43)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_243, c_36])).
% 3.38/1.62  tff(c_205, plain, (![A_74, B_75]: (r1_tarski(k1_tarski(A_74), B_75) | ~r2_hidden(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.38/1.62  tff(c_34, plain, (![A_40, B_41]: (~r1_tarski(A_40, k2_zfmisc_1(A_40, B_41)) | k1_xboole_0=A_40)), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.38/1.62  tff(c_215, plain, (![A_74, B_41]: (k1_tarski(A_74)=k1_xboole_0 | ~r2_hidden(A_74, k2_zfmisc_1(k1_tarski(A_74), B_41)))), inference(resolution, [status(thm)], [c_205, c_34])).
% 3.38/1.62  tff(c_290, plain, (![A_74, B_41]: (~r2_hidden(A_74, k2_zfmisc_1(k1_tarski(A_74), B_41)))), inference(negUnitSimplification, [status(thm)], [c_244, c_215])).
% 3.38/1.62  tff(c_407, plain, (![D_185]: (~r2_hidden('#skF_5', D_185) | ~r2_hidden('#skF_4', k1_tarski('#skF_4')))), inference(resolution, [status(thm)], [c_393, c_290])).
% 3.38/1.62  tff(c_415, plain, (![D_186]: (~r2_hidden('#skF_5', D_186))), inference(demodulation, [status(thm), theory('equality')], [c_355, c_407])).
% 3.38/1.62  tff(c_459, plain, $false, inference(resolution, [status(thm)], [c_387, c_415])).
% 3.38/1.62  tff(c_460, plain, ('#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_152])).
% 3.38/1.62  tff(c_463, plain, (k4_tarski('#skF_4', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_460, c_90])).
% 3.38/1.62  tff(c_655, plain, (![A_283, B_284, C_285, D_286]: (r2_hidden(k4_tarski(A_283, B_284), k2_zfmisc_1(C_285, D_286)) | ~r2_hidden(B_284, D_286) | ~r2_hidden(A_283, C_285))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.38/1.62  tff(c_686, plain, (![C_295, D_296]: (r2_hidden('#skF_3', k2_zfmisc_1(C_295, D_296)) | ~r2_hidden('#skF_3', D_296) | ~r2_hidden('#skF_4', C_295))), inference(superposition, [status(thm), theory('equality')], [c_463, c_655])).
% 3.38/1.62  tff(c_534, plain, (![A_201, B_202]: (k5_xboole_0(A_201, k3_xboole_0(A_201, B_202))=k4_xboole_0(A_201, B_202))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.38/1.62  tff(c_543, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_534])).
% 3.38/1.62  tff(c_546, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_543])).
% 3.38/1.62  tff(c_547, plain, (![B_43]: (k1_tarski(B_43)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_546, c_36])).
% 3.38/1.62  tff(c_24, plain, (![A_34, B_35]: (r1_tarski(k1_tarski(A_34), B_35) | ~r2_hidden(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.38/1.62  tff(c_500, plain, (![A_193, B_194]: (~r1_tarski(A_193, k2_zfmisc_1(B_194, A_193)) | k1_xboole_0=A_193)), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.38/1.62  tff(c_505, plain, (![A_34, B_194]: (k1_tarski(A_34)=k1_xboole_0 | ~r2_hidden(A_34, k2_zfmisc_1(B_194, k1_tarski(A_34))))), inference(resolution, [status(thm)], [c_24, c_500])).
% 3.38/1.62  tff(c_593, plain, (![A_34, B_194]: (~r2_hidden(A_34, k2_zfmisc_1(B_194, k1_tarski(A_34))))), inference(negUnitSimplification, [status(thm)], [c_547, c_505])).
% 3.38/1.62  tff(c_700, plain, (![C_295]: (~r2_hidden('#skF_3', k1_tarski('#skF_3')) | ~r2_hidden('#skF_4', C_295))), inference(resolution, [status(thm)], [c_686, c_593])).
% 3.38/1.62  tff(c_708, plain, (![C_297]: (~r2_hidden('#skF_4', C_297))), inference(demodulation, [status(thm), theory('equality')], [c_680, c_700])).
% 3.38/1.62  tff(c_746, plain, $false, inference(resolution, [status(thm)], [c_625, c_708])).
% 3.38/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.38/1.62  
% 3.38/1.62  Inference rules
% 3.38/1.62  ----------------------
% 3.38/1.62  #Ref     : 0
% 3.38/1.62  #Sup     : 158
% 3.38/1.62  #Fact    : 0
% 3.38/1.62  #Define  : 0
% 3.38/1.62  #Split   : 1
% 3.38/1.62  #Chain   : 0
% 3.38/1.62  #Close   : 0
% 3.38/1.62  
% 3.38/1.62  Ordering : KBO
% 3.38/1.62  
% 3.38/1.62  Simplification rules
% 3.38/1.62  ----------------------
% 3.38/1.62  #Subsume      : 2
% 3.38/1.62  #Demod        : 21
% 3.38/1.62  #Tautology    : 86
% 3.38/1.62  #SimpNegUnit  : 10
% 3.38/1.62  #BackRed      : 9
% 3.38/1.62  
% 3.38/1.62  #Partial instantiations: 0
% 3.38/1.62  #Strategies tried      : 1
% 3.38/1.62  
% 3.38/1.62  Timing (in seconds)
% 3.38/1.62  ----------------------
% 3.38/1.63  Preprocessing        : 0.37
% 3.38/1.63  Parsing              : 0.19
% 3.38/1.63  CNF conversion       : 0.03
% 3.38/1.63  Main loop            : 0.39
% 3.38/1.63  Inferencing          : 0.13
% 3.38/1.63  Reduction            : 0.11
% 3.38/1.63  Demodulation         : 0.08
% 3.38/1.63  BG Simplification    : 0.02
% 3.38/1.63  Subsumption          : 0.09
% 3.38/1.63  Abstraction          : 0.03
% 3.38/1.63  MUC search           : 0.00
% 3.38/1.63  Cooper               : 0.00
% 3.38/1.63  Total                : 0.82
% 3.38/1.63  Index Insertion      : 0.00
% 3.38/1.63  Index Deletion       : 0.00
% 3.38/1.63  Index Matching       : 0.00
% 3.38/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
