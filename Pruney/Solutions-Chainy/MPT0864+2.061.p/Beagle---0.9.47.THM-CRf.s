%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:16 EST 2020

% Result     : Theorem 2.92s
% Output     : CNFRefutation 2.92s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 139 expanded)
%              Number of leaves         :   42 (  65 expanded)
%              Depth                    :    8
%              Number of atoms          :   90 ( 164 expanded)
%              Number of equality atoms :   60 ( 126 expanded)
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

tff(f_41,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_86,axiom,(
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

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_102,negated_conjecture,(
    ~ ! [A] :
        ( ? [B,C] : A = k4_tarski(B,C)
       => ( A != k1_mcart_1(A)
          & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_31,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_62,axiom,(
    ! [A,B] : k2_zfmisc_1(k1_tarski(A),k1_tarski(B)) = k1_tarski(k4_tarski(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( r1_tarski(A,k2_zfmisc_1(A,B))
        | r1_tarski(A,k2_zfmisc_1(B,A)) )
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t135_zfmisc_1)).

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

tff(c_623,plain,(
    ! [C_255,B_251,D_254,E_252,A_253] : k4_enumset1(A_253,A_253,B_251,C_255,D_254,E_252) = k3_enumset1(A_253,B_251,C_255,D_254,E_252) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_38,plain,(
    ! [B_43,A_42,D_45,E_46,C_44,H_51] : r2_hidden(H_51,k4_enumset1(A_42,B_43,C_44,D_45,E_46,H_51)) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_650,plain,(
    ! [D_260,C_256,E_258,A_259,B_257] : r2_hidden(E_258,k3_enumset1(A_259,B_257,C_256,D_260,E_258)) ),
    inference(superposition,[status(thm),theory(equality)],[c_623,c_38])).

tff(c_663,plain,(
    ! [D_267,A_268,B_269,C_270] : r2_hidden(D_267,k2_enumset1(A_268,B_269,C_270,D_267)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_650])).

tff(c_667,plain,(
    ! [C_271,A_272,B_273] : r2_hidden(C_271,k1_enumset1(A_272,B_273,C_271)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_663])).

tff(c_671,plain,(
    ! [B_274,A_275] : r2_hidden(B_274,k2_tarski(A_275,B_274)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_667])).

tff(c_674,plain,(
    ! [A_6] : r2_hidden(A_6,k1_tarski(A_6)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_671])).

tff(c_24,plain,(
    ! [A_34,B_35] :
      ( r1_tarski(k1_tarski(A_34),B_35)
      | ~ r2_hidden(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_356,plain,(
    ! [E_143,A_144,D_145,B_142,C_146] : k4_enumset1(A_144,A_144,B_142,C_146,D_145,E_143) = k3_enumset1(A_144,B_142,C_146,D_145,E_143) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_392,plain,(
    ! [B_155,C_154,D_157,E_156,A_153] : r2_hidden(E_156,k3_enumset1(A_153,B_155,C_154,D_157,E_156)) ),
    inference(superposition,[status(thm),theory(equality)],[c_356,c_38])).

tff(c_396,plain,(
    ! [D_158,A_159,B_160,C_161] : r2_hidden(D_158,k2_enumset1(A_159,B_160,C_161,D_158)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_392])).

tff(c_400,plain,(
    ! [C_162,A_163,B_164] : r2_hidden(C_162,k1_enumset1(A_163,B_164,C_162)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_396])).

tff(c_413,plain,(
    ! [B_172,A_173] : r2_hidden(B_172,k2_tarski(A_173,B_172)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_400])).

tff(c_416,plain,(
    ! [A_6] : r2_hidden(A_6,k1_tarski(A_6)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_413])).

tff(c_86,plain,(
    k4_tarski('#skF_4','#skF_5') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_107,plain,(
    ! [A_60,B_61] : k1_mcart_1(k4_tarski(A_60,B_61)) = A_60 ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_116,plain,(
    k1_mcart_1('#skF_3') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_107])).

tff(c_132,plain,(
    ! [A_63,B_64] : k2_mcart_1(k4_tarski(A_63,B_64)) = B_64 ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_141,plain,(
    k2_mcart_1('#skF_3') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_132])).

tff(c_84,plain,
    ( k2_mcart_1('#skF_3') = '#skF_3'
    | k1_mcart_1('#skF_3') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_148,plain,
    ( '#skF_5' = '#skF_3'
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_141,c_84])).

tff(c_149,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_148])).

tff(c_152,plain,(
    k4_tarski('#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_86])).

tff(c_6,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_227,plain,(
    ! [A_79,B_80] : k5_xboole_0(A_79,k3_xboole_0(A_79,B_80)) = k4_xboole_0(A_79,B_80) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_236,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_227])).

tff(c_239,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_236])).

tff(c_30,plain,(
    ! [B_39] : k4_xboole_0(k1_tarski(B_39),k1_tarski(B_39)) != k1_tarski(B_39) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_240,plain,(
    ! [B_39] : k1_tarski(B_39) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_239,c_30])).

tff(c_281,plain,(
    ! [A_94,B_95] : k2_zfmisc_1(k1_tarski(A_94),k1_tarski(B_95)) = k1_tarski(k4_tarski(A_94,B_95)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_28,plain,(
    ! [A_36,B_37] :
      ( ~ r1_tarski(A_36,k2_zfmisc_1(A_36,B_37))
      | k1_xboole_0 = A_36 ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_287,plain,(
    ! [A_94,B_95] :
      ( ~ r1_tarski(k1_tarski(A_94),k1_tarski(k4_tarski(A_94,B_95)))
      | k1_tarski(A_94) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_281,c_28])).

tff(c_298,plain,(
    ! [A_96,B_97] : ~ r1_tarski(k1_tarski(A_96),k1_tarski(k4_tarski(A_96,B_97))) ),
    inference(negUnitSimplification,[status(thm)],[c_240,c_287])).

tff(c_305,plain,(
    ~ r1_tarski(k1_tarski('#skF_4'),k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_298])).

tff(c_310,plain,(
    ~ r2_hidden('#skF_4',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_24,c_305])).

tff(c_419,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_416,c_310])).

tff(c_420,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_148])).

tff(c_423,plain,(
    k4_tarski('#skF_4','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_420,c_86])).

tff(c_494,plain,(
    ! [A_188,B_189] : k5_xboole_0(A_188,k3_xboole_0(A_188,B_189)) = k4_xboole_0(A_188,B_189) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_503,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_494])).

tff(c_506,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_503])).

tff(c_508,plain,(
    ! [B_39] : k1_tarski(B_39) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_506,c_30])).

tff(c_529,plain,(
    ! [A_219,B_220] : k2_zfmisc_1(k1_tarski(A_219),k1_tarski(B_220)) = k1_tarski(k4_tarski(A_219,B_220)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_26,plain,(
    ! [A_36,B_37] :
      ( ~ r1_tarski(A_36,k2_zfmisc_1(B_37,A_36))
      | k1_xboole_0 = A_36 ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_535,plain,(
    ! [B_220,A_219] :
      ( ~ r1_tarski(k1_tarski(B_220),k1_tarski(k4_tarski(A_219,B_220)))
      | k1_tarski(B_220) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_529,c_26])).

tff(c_546,plain,(
    ! [B_221,A_222] : ~ r1_tarski(k1_tarski(B_221),k1_tarski(k4_tarski(A_222,B_221))) ),
    inference(negUnitSimplification,[status(thm)],[c_508,c_535])).

tff(c_549,plain,(
    ~ r1_tarski(k1_tarski('#skF_3'),k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_423,c_546])).

tff(c_558,plain,(
    ~ r2_hidden('#skF_3',k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_24,c_549])).

tff(c_677,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_674,c_558])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:29:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.92/1.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.92/1.41  
% 2.92/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.92/1.41  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_setfam_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_1 > #skF_4
% 2.92/1.41  
% 2.92/1.41  %Foreground sorts:
% 2.92/1.41  
% 2.92/1.41  
% 2.92/1.41  %Background operators:
% 2.92/1.41  
% 2.92/1.41  
% 2.92/1.41  %Foreground operators:
% 2.92/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.92/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.92/1.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.92/1.41  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.92/1.41  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.92/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.92/1.41  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.92/1.41  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.92/1.41  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.92/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.92/1.41  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.92/1.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.92/1.41  tff('#skF_5', type, '#skF_5': $i).
% 2.92/1.41  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.92/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.92/1.41  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.92/1.41  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.92/1.41  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.92/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.92/1.41  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.92/1.41  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.92/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.92/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.92/1.41  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.92/1.41  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.92/1.41  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.92/1.41  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.92/1.41  
% 2.92/1.43  tff(f_33, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.92/1.43  tff(f_35, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.92/1.43  tff(f_37, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.92/1.43  tff(f_39, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 2.92/1.43  tff(f_41, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 2.92/1.43  tff(f_86, axiom, (![A, B, C, D, E, F, G]: ((G = k4_enumset1(A, B, C, D, E, F)) <=> (![H]: (r2_hidden(H, G) <=> ~(((((~(H = A) & ~(H = B)) & ~(H = C)) & ~(H = D)) & ~(H = E)) & ~(H = F)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_enumset1)).
% 2.92/1.43  tff(f_49, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.92/1.43  tff(f_102, negated_conjecture, ~(![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_mcart_1)).
% 2.92/1.43  tff(f_92, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 2.92/1.43  tff(f_31, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.92/1.43  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.92/1.43  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.92/1.43  tff(f_60, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.92/1.43  tff(f_62, axiom, (![A, B]: (k2_zfmisc_1(k1_tarski(A), k1_tarski(B)) = k1_tarski(k4_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_zfmisc_1)).
% 2.92/1.43  tff(f_55, axiom, (![A, B]: ((r1_tarski(A, k2_zfmisc_1(A, B)) | r1_tarski(A, k2_zfmisc_1(B, A))) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t135_zfmisc_1)).
% 2.92/1.43  tff(c_8, plain, (![A_6]: (k2_tarski(A_6, A_6)=k1_tarski(A_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.92/1.43  tff(c_10, plain, (![A_7, B_8]: (k1_enumset1(A_7, A_7, B_8)=k2_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.92/1.43  tff(c_12, plain, (![A_9, B_10, C_11]: (k2_enumset1(A_9, A_9, B_10, C_11)=k1_enumset1(A_9, B_10, C_11))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.92/1.43  tff(c_14, plain, (![A_12, B_13, C_14, D_15]: (k3_enumset1(A_12, A_12, B_13, C_14, D_15)=k2_enumset1(A_12, B_13, C_14, D_15))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.92/1.43  tff(c_623, plain, (![C_255, B_251, D_254, E_252, A_253]: (k4_enumset1(A_253, A_253, B_251, C_255, D_254, E_252)=k3_enumset1(A_253, B_251, C_255, D_254, E_252))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.92/1.43  tff(c_38, plain, (![B_43, A_42, D_45, E_46, C_44, H_51]: (r2_hidden(H_51, k4_enumset1(A_42, B_43, C_44, D_45, E_46, H_51)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.92/1.43  tff(c_650, plain, (![D_260, C_256, E_258, A_259, B_257]: (r2_hidden(E_258, k3_enumset1(A_259, B_257, C_256, D_260, E_258)))), inference(superposition, [status(thm), theory('equality')], [c_623, c_38])).
% 2.92/1.43  tff(c_663, plain, (![D_267, A_268, B_269, C_270]: (r2_hidden(D_267, k2_enumset1(A_268, B_269, C_270, D_267)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_650])).
% 2.92/1.43  tff(c_667, plain, (![C_271, A_272, B_273]: (r2_hidden(C_271, k1_enumset1(A_272, B_273, C_271)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_663])).
% 2.92/1.43  tff(c_671, plain, (![B_274, A_275]: (r2_hidden(B_274, k2_tarski(A_275, B_274)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_667])).
% 2.92/1.43  tff(c_674, plain, (![A_6]: (r2_hidden(A_6, k1_tarski(A_6)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_671])).
% 2.92/1.43  tff(c_24, plain, (![A_34, B_35]: (r1_tarski(k1_tarski(A_34), B_35) | ~r2_hidden(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.92/1.43  tff(c_356, plain, (![E_143, A_144, D_145, B_142, C_146]: (k4_enumset1(A_144, A_144, B_142, C_146, D_145, E_143)=k3_enumset1(A_144, B_142, C_146, D_145, E_143))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.92/1.43  tff(c_392, plain, (![B_155, C_154, D_157, E_156, A_153]: (r2_hidden(E_156, k3_enumset1(A_153, B_155, C_154, D_157, E_156)))), inference(superposition, [status(thm), theory('equality')], [c_356, c_38])).
% 2.92/1.43  tff(c_396, plain, (![D_158, A_159, B_160, C_161]: (r2_hidden(D_158, k2_enumset1(A_159, B_160, C_161, D_158)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_392])).
% 2.92/1.43  tff(c_400, plain, (![C_162, A_163, B_164]: (r2_hidden(C_162, k1_enumset1(A_163, B_164, C_162)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_396])).
% 2.92/1.43  tff(c_413, plain, (![B_172, A_173]: (r2_hidden(B_172, k2_tarski(A_173, B_172)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_400])).
% 2.92/1.43  tff(c_416, plain, (![A_6]: (r2_hidden(A_6, k1_tarski(A_6)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_413])).
% 2.92/1.43  tff(c_86, plain, (k4_tarski('#skF_4', '#skF_5')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.92/1.43  tff(c_107, plain, (![A_60, B_61]: (k1_mcart_1(k4_tarski(A_60, B_61))=A_60)), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.92/1.43  tff(c_116, plain, (k1_mcart_1('#skF_3')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_86, c_107])).
% 2.92/1.43  tff(c_132, plain, (![A_63, B_64]: (k2_mcart_1(k4_tarski(A_63, B_64))=B_64)), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.92/1.43  tff(c_141, plain, (k2_mcart_1('#skF_3')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_86, c_132])).
% 2.92/1.43  tff(c_84, plain, (k2_mcart_1('#skF_3')='#skF_3' | k1_mcart_1('#skF_3')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.92/1.43  tff(c_148, plain, ('#skF_5'='#skF_3' | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_116, c_141, c_84])).
% 2.92/1.43  tff(c_149, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_148])).
% 2.92/1.43  tff(c_152, plain, (k4_tarski('#skF_4', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_149, c_86])).
% 2.92/1.43  tff(c_6, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.92/1.43  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.92/1.43  tff(c_227, plain, (![A_79, B_80]: (k5_xboole_0(A_79, k3_xboole_0(A_79, B_80))=k4_xboole_0(A_79, B_80))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.92/1.43  tff(c_236, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_227])).
% 2.92/1.43  tff(c_239, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_236])).
% 2.92/1.43  tff(c_30, plain, (![B_39]: (k4_xboole_0(k1_tarski(B_39), k1_tarski(B_39))!=k1_tarski(B_39))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.92/1.43  tff(c_240, plain, (![B_39]: (k1_tarski(B_39)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_239, c_30])).
% 2.92/1.43  tff(c_281, plain, (![A_94, B_95]: (k2_zfmisc_1(k1_tarski(A_94), k1_tarski(B_95))=k1_tarski(k4_tarski(A_94, B_95)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.92/1.43  tff(c_28, plain, (![A_36, B_37]: (~r1_tarski(A_36, k2_zfmisc_1(A_36, B_37)) | k1_xboole_0=A_36)), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.92/1.43  tff(c_287, plain, (![A_94, B_95]: (~r1_tarski(k1_tarski(A_94), k1_tarski(k4_tarski(A_94, B_95))) | k1_tarski(A_94)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_281, c_28])).
% 2.92/1.43  tff(c_298, plain, (![A_96, B_97]: (~r1_tarski(k1_tarski(A_96), k1_tarski(k4_tarski(A_96, B_97))))), inference(negUnitSimplification, [status(thm)], [c_240, c_287])).
% 2.92/1.43  tff(c_305, plain, (~r1_tarski(k1_tarski('#skF_4'), k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_152, c_298])).
% 2.92/1.43  tff(c_310, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_24, c_305])).
% 2.92/1.43  tff(c_419, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_416, c_310])).
% 2.92/1.43  tff(c_420, plain, ('#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_148])).
% 2.92/1.43  tff(c_423, plain, (k4_tarski('#skF_4', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_420, c_86])).
% 2.92/1.43  tff(c_494, plain, (![A_188, B_189]: (k5_xboole_0(A_188, k3_xboole_0(A_188, B_189))=k4_xboole_0(A_188, B_189))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.92/1.43  tff(c_503, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_494])).
% 2.92/1.43  tff(c_506, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_503])).
% 2.92/1.43  tff(c_508, plain, (![B_39]: (k1_tarski(B_39)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_506, c_30])).
% 2.92/1.43  tff(c_529, plain, (![A_219, B_220]: (k2_zfmisc_1(k1_tarski(A_219), k1_tarski(B_220))=k1_tarski(k4_tarski(A_219, B_220)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.92/1.43  tff(c_26, plain, (![A_36, B_37]: (~r1_tarski(A_36, k2_zfmisc_1(B_37, A_36)) | k1_xboole_0=A_36)), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.92/1.43  tff(c_535, plain, (![B_220, A_219]: (~r1_tarski(k1_tarski(B_220), k1_tarski(k4_tarski(A_219, B_220))) | k1_tarski(B_220)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_529, c_26])).
% 2.92/1.43  tff(c_546, plain, (![B_221, A_222]: (~r1_tarski(k1_tarski(B_221), k1_tarski(k4_tarski(A_222, B_221))))), inference(negUnitSimplification, [status(thm)], [c_508, c_535])).
% 2.92/1.43  tff(c_549, plain, (~r1_tarski(k1_tarski('#skF_3'), k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_423, c_546])).
% 2.92/1.43  tff(c_558, plain, (~r2_hidden('#skF_3', k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_24, c_549])).
% 2.92/1.43  tff(c_677, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_674, c_558])).
% 2.92/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.92/1.43  
% 2.92/1.43  Inference rules
% 2.92/1.43  ----------------------
% 2.92/1.43  #Ref     : 0
% 2.92/1.43  #Sup     : 140
% 2.92/1.43  #Fact    : 0
% 2.92/1.43  #Define  : 0
% 2.92/1.43  #Split   : 1
% 2.92/1.43  #Chain   : 0
% 2.92/1.43  #Close   : 0
% 2.92/1.43  
% 2.92/1.43  Ordering : KBO
% 2.92/1.43  
% 2.92/1.43  Simplification rules
% 2.92/1.43  ----------------------
% 2.92/1.43  #Subsume      : 8
% 2.92/1.43  #Demod        : 19
% 2.92/1.43  #Tautology    : 86
% 2.92/1.43  #SimpNegUnit  : 12
% 2.92/1.43  #BackRed      : 9
% 2.92/1.43  
% 2.92/1.43  #Partial instantiations: 0
% 2.92/1.43  #Strategies tried      : 1
% 2.92/1.43  
% 2.92/1.43  Timing (in seconds)
% 2.92/1.43  ----------------------
% 2.92/1.43  Preprocessing        : 0.35
% 2.92/1.43  Parsing              : 0.17
% 2.92/1.43  CNF conversion       : 0.02
% 2.92/1.43  Main loop            : 0.32
% 2.92/1.43  Inferencing          : 0.11
% 2.92/1.43  Reduction            : 0.09
% 2.92/1.44  Demodulation         : 0.06
% 2.92/1.44  BG Simplification    : 0.02
% 2.92/1.44  Subsumption          : 0.07
% 2.92/1.44  Abstraction          : 0.02
% 2.92/1.44  MUC search           : 0.00
% 2.92/1.44  Cooper               : 0.00
% 2.92/1.44  Total                : 0.71
% 2.92/1.44  Index Insertion      : 0.00
% 2.92/1.44  Index Deletion       : 0.00
% 2.92/1.44  Index Matching       : 0.00
% 2.92/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
