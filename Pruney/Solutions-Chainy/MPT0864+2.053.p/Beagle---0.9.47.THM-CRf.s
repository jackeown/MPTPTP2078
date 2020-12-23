%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:15 EST 2020

% Result     : Theorem 3.14s
% Output     : CNFRefutation 3.30s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 135 expanded)
%              Number of leaves         :   43 (  65 expanded)
%              Depth                    :    8
%              Number of atoms          :   87 ( 158 expanded)
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

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

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

tff(c_678,plain,(
    ! [D_257,C_253,A_256,B_255,E_254] : k4_enumset1(A_256,A_256,B_255,C_253,D_257,E_254) = k3_enumset1(A_256,B_255,C_253,D_257,E_254) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_48,plain,(
    ! [A_47,F_52,E_51,D_50,B_48,H_56] : r2_hidden(H_56,k4_enumset1(A_47,B_48,H_56,D_50,E_51,F_52)) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_705,plain,(
    ! [B_259,A_261,E_260,C_258,D_262] : r2_hidden(B_259,k3_enumset1(A_261,B_259,C_258,D_262,E_260)) ),
    inference(superposition,[status(thm),theory(equality)],[c_678,c_48])).

tff(c_709,plain,(
    ! [A_263,B_264,C_265,D_266] : r2_hidden(A_263,k2_enumset1(A_263,B_264,C_265,D_266)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_705])).

tff(c_713,plain,(
    ! [A_267,B_268,C_269] : r2_hidden(A_267,k1_enumset1(A_267,B_268,C_269)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_709])).

tff(c_717,plain,(
    ! [A_270,B_271] : r2_hidden(A_270,k2_tarski(A_270,B_271)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_713])).

tff(c_720,plain,(
    ! [A_9] : r2_hidden(A_9,k1_tarski(A_9)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_717])).

tff(c_26,plain,(
    ! [A_37,B_38] :
      ( r1_tarski(k1_tarski(A_37),B_38)
      | ~ r2_hidden(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_402,plain,(
    ! [C_152,A_155,D_156,E_153,B_154] : k4_enumset1(A_155,A_155,B_154,C_152,D_156,E_153) = k3_enumset1(A_155,B_154,C_152,D_156,E_153) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_44,plain,(
    ! [A_47,F_52,D_50,C_49,B_48,H_56] : r2_hidden(H_56,k4_enumset1(A_47,B_48,C_49,D_50,H_56,F_52)) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_429,plain,(
    ! [C_160,B_159,D_161,A_158,E_157] : r2_hidden(D_161,k3_enumset1(A_158,B_159,C_160,D_161,E_157)) ),
    inference(superposition,[status(thm),theory(equality)],[c_402,c_44])).

tff(c_442,plain,(
    ! [C_168,A_169,B_170,D_171] : r2_hidden(C_168,k2_enumset1(A_169,B_170,C_168,D_171)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_429])).

tff(c_446,plain,(
    ! [B_172,A_173,C_174] : r2_hidden(B_172,k1_enumset1(A_173,B_172,C_174)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_442])).

tff(c_450,plain,(
    ! [A_175,B_176] : r2_hidden(A_175,k2_tarski(A_175,B_176)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_446])).

tff(c_453,plain,(
    ! [A_9] : r2_hidden(A_9,k1_tarski(A_9)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_450])).

tff(c_90,plain,(
    k4_tarski('#skF_4','#skF_5') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_113,plain,(
    ! [A_65,B_66] : k1_mcart_1(k4_tarski(A_65,B_66)) = A_65 ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_122,plain,(
    k1_mcart_1('#skF_3') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_113])).

tff(c_138,plain,(
    ! [A_68,B_69] : k2_mcart_1(k4_tarski(A_68,B_69)) = B_69 ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_147,plain,(
    k2_mcart_1('#skF_3') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_138])).

tff(c_88,plain,
    ( k2_mcart_1('#skF_3') = '#skF_3'
    | k1_mcart_1('#skF_3') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_164,plain,
    ( '#skF_5' = '#skF_3'
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_147,c_88])).

tff(c_165,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_164])).

tff(c_168,plain,(
    k4_tarski('#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_90])).

tff(c_332,plain,(
    ! [A_114,B_115] : k2_zfmisc_1(k1_tarski(A_114),k1_tarski(B_115)) = k1_tarski(k4_tarski(A_114,B_115)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_154,plain,(
    ! [A_70,B_71] : k4_xboole_0(A_70,k2_xboole_0(A_70,B_71)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_161,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_154])).

tff(c_34,plain,(
    ! [B_44] : k4_xboole_0(k1_tarski(B_44),k1_tarski(B_44)) != k1_tarski(B_44) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_201,plain,(
    ! [B_44] : k1_tarski(B_44) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_34])).

tff(c_258,plain,(
    ! [A_88,B_89] :
      ( r1_tarski(k1_tarski(A_88),B_89)
      | ~ r2_hidden(A_88,B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_32,plain,(
    ! [A_41,B_42] :
      ( ~ r1_tarski(A_41,k2_zfmisc_1(A_41,B_42))
      | k1_xboole_0 = A_41 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_265,plain,(
    ! [A_88,B_42] :
      ( k1_tarski(A_88) = k1_xboole_0
      | ~ r2_hidden(A_88,k2_zfmisc_1(k1_tarski(A_88),B_42)) ) ),
    inference(resolution,[status(thm)],[c_258,c_32])).

tff(c_273,plain,(
    ! [A_88,B_42] : ~ r2_hidden(A_88,k2_zfmisc_1(k1_tarski(A_88),B_42)) ),
    inference(negUnitSimplification,[status(thm)],[c_201,c_265])).

tff(c_360,plain,(
    ! [A_124,B_125] : ~ r2_hidden(A_124,k1_tarski(k4_tarski(A_124,B_125))) ),
    inference(superposition,[status(thm),theory(equality)],[c_332,c_273])).

tff(c_363,plain,(
    ~ r2_hidden('#skF_4',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_360])).

tff(c_456,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_453,c_363])).

tff(c_457,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_164])).

tff(c_460,plain,(
    k4_tarski('#skF_4','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_457,c_90])).

tff(c_510,plain,(
    ! [B_44] : k1_tarski(B_44) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_34])).

tff(c_618,plain,(
    ! [A_239,B_240] : k2_zfmisc_1(k1_tarski(A_239),k1_tarski(B_240)) = k1_tarski(k4_tarski(A_239,B_240)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_30,plain,(
    ! [A_41,B_42] :
      ( ~ r1_tarski(A_41,k2_zfmisc_1(B_42,A_41))
      | k1_xboole_0 = A_41 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_627,plain,(
    ! [B_240,A_239] :
      ( ~ r1_tarski(k1_tarski(B_240),k1_tarski(k4_tarski(A_239,B_240)))
      | k1_tarski(B_240) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_618,c_30])).

tff(c_652,plain,(
    ! [B_245,A_246] : ~ r1_tarski(k1_tarski(B_245),k1_tarski(k4_tarski(A_246,B_245))) ),
    inference(negUnitSimplification,[status(thm)],[c_510,c_627])).

tff(c_655,plain,(
    ~ r1_tarski(k1_tarski('#skF_3'),k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_460,c_652])).

tff(c_673,plain,(
    ~ r2_hidden('#skF_3',k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_26,c_655])).

tff(c_723,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_720,c_673])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:07:35 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.14/1.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.14/1.45  
% 3.14/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.14/1.45  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_mcart_1 > k1_tarski > k1_setfam_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_1 > #skF_4
% 3.14/1.45  
% 3.14/1.45  %Foreground sorts:
% 3.14/1.45  
% 3.14/1.45  
% 3.14/1.45  %Background operators:
% 3.14/1.45  
% 3.14/1.45  
% 3.14/1.45  %Foreground operators:
% 3.14/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.14/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.14/1.45  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.14/1.45  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.14/1.45  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.14/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.14/1.45  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.14/1.45  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.14/1.45  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.14/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.14/1.45  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.14/1.45  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.14/1.45  tff('#skF_5', type, '#skF_5': $i).
% 3.14/1.45  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.14/1.45  tff('#skF_3', type, '#skF_3': $i).
% 3.14/1.45  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.14/1.45  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.14/1.45  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.14/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.14/1.45  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 3.14/1.45  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.14/1.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.14/1.45  tff('#skF_4', type, '#skF_4': $i).
% 3.14/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.14/1.45  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 3.14/1.45  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.14/1.45  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.14/1.45  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.14/1.45  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.14/1.45  
% 3.30/1.48  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.30/1.48  tff(f_37, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.30/1.48  tff(f_39, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 3.30/1.48  tff(f_41, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 3.30/1.48  tff(f_43, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 3.30/1.48  tff(f_90, axiom, (![A, B, C, D, E, F, G]: ((G = k4_enumset1(A, B, C, D, E, F)) <=> (![H]: (r2_hidden(H, G) <=> ~(((((~(H = A) & ~(H = B)) & ~(H = C)) & ~(H = D)) & ~(H = E)) & ~(H = F)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_enumset1)).
% 3.30/1.48  tff(f_51, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.30/1.48  tff(f_106, negated_conjecture, ~(![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_mcart_1)).
% 3.30/1.48  tff(f_96, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 3.30/1.48  tff(f_66, axiom, (![A, B]: (k2_zfmisc_1(k1_tarski(A), k1_tarski(B)) = k1_tarski(k4_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_zfmisc_1)).
% 3.30/1.48  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 3.30/1.48  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 3.30/1.48  tff(f_64, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 3.30/1.48  tff(f_59, axiom, (![A, B]: ((r1_tarski(A, k2_zfmisc_1(A, B)) | r1_tarski(A, k2_zfmisc_1(B, A))) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t135_zfmisc_1)).
% 3.30/1.48  tff(c_10, plain, (![A_9]: (k2_tarski(A_9, A_9)=k1_tarski(A_9))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.30/1.48  tff(c_12, plain, (![A_10, B_11]: (k1_enumset1(A_10, A_10, B_11)=k2_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.30/1.48  tff(c_14, plain, (![A_12, B_13, C_14]: (k2_enumset1(A_12, A_12, B_13, C_14)=k1_enumset1(A_12, B_13, C_14))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.30/1.48  tff(c_16, plain, (![A_15, B_16, C_17, D_18]: (k3_enumset1(A_15, A_15, B_16, C_17, D_18)=k2_enumset1(A_15, B_16, C_17, D_18))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.30/1.48  tff(c_678, plain, (![D_257, C_253, A_256, B_255, E_254]: (k4_enumset1(A_256, A_256, B_255, C_253, D_257, E_254)=k3_enumset1(A_256, B_255, C_253, D_257, E_254))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.30/1.48  tff(c_48, plain, (![A_47, F_52, E_51, D_50, B_48, H_56]: (r2_hidden(H_56, k4_enumset1(A_47, B_48, H_56, D_50, E_51, F_52)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.30/1.48  tff(c_705, plain, (![B_259, A_261, E_260, C_258, D_262]: (r2_hidden(B_259, k3_enumset1(A_261, B_259, C_258, D_262, E_260)))), inference(superposition, [status(thm), theory('equality')], [c_678, c_48])).
% 3.30/1.48  tff(c_709, plain, (![A_263, B_264, C_265, D_266]: (r2_hidden(A_263, k2_enumset1(A_263, B_264, C_265, D_266)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_705])).
% 3.30/1.48  tff(c_713, plain, (![A_267, B_268, C_269]: (r2_hidden(A_267, k1_enumset1(A_267, B_268, C_269)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_709])).
% 3.30/1.48  tff(c_717, plain, (![A_270, B_271]: (r2_hidden(A_270, k2_tarski(A_270, B_271)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_713])).
% 3.30/1.48  tff(c_720, plain, (![A_9]: (r2_hidden(A_9, k1_tarski(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_717])).
% 3.30/1.48  tff(c_26, plain, (![A_37, B_38]: (r1_tarski(k1_tarski(A_37), B_38) | ~r2_hidden(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.30/1.48  tff(c_402, plain, (![C_152, A_155, D_156, E_153, B_154]: (k4_enumset1(A_155, A_155, B_154, C_152, D_156, E_153)=k3_enumset1(A_155, B_154, C_152, D_156, E_153))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.30/1.48  tff(c_44, plain, (![A_47, F_52, D_50, C_49, B_48, H_56]: (r2_hidden(H_56, k4_enumset1(A_47, B_48, C_49, D_50, H_56, F_52)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.30/1.48  tff(c_429, plain, (![C_160, B_159, D_161, A_158, E_157]: (r2_hidden(D_161, k3_enumset1(A_158, B_159, C_160, D_161, E_157)))), inference(superposition, [status(thm), theory('equality')], [c_402, c_44])).
% 3.30/1.48  tff(c_442, plain, (![C_168, A_169, B_170, D_171]: (r2_hidden(C_168, k2_enumset1(A_169, B_170, C_168, D_171)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_429])).
% 3.30/1.48  tff(c_446, plain, (![B_172, A_173, C_174]: (r2_hidden(B_172, k1_enumset1(A_173, B_172, C_174)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_442])).
% 3.30/1.48  tff(c_450, plain, (![A_175, B_176]: (r2_hidden(A_175, k2_tarski(A_175, B_176)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_446])).
% 3.30/1.48  tff(c_453, plain, (![A_9]: (r2_hidden(A_9, k1_tarski(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_450])).
% 3.30/1.48  tff(c_90, plain, (k4_tarski('#skF_4', '#skF_5')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.30/1.48  tff(c_113, plain, (![A_65, B_66]: (k1_mcart_1(k4_tarski(A_65, B_66))=A_65)), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.30/1.48  tff(c_122, plain, (k1_mcart_1('#skF_3')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_90, c_113])).
% 3.30/1.48  tff(c_138, plain, (![A_68, B_69]: (k2_mcart_1(k4_tarski(A_68, B_69))=B_69)), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.30/1.48  tff(c_147, plain, (k2_mcart_1('#skF_3')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_90, c_138])).
% 3.30/1.48  tff(c_88, plain, (k2_mcart_1('#skF_3')='#skF_3' | k1_mcart_1('#skF_3')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.30/1.48  tff(c_164, plain, ('#skF_5'='#skF_3' | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_122, c_147, c_88])).
% 3.30/1.48  tff(c_165, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_164])).
% 3.30/1.48  tff(c_168, plain, (k4_tarski('#skF_4', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_165, c_90])).
% 3.30/1.48  tff(c_332, plain, (![A_114, B_115]: (k2_zfmisc_1(k1_tarski(A_114), k1_tarski(B_115))=k1_tarski(k4_tarski(A_114, B_115)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.30/1.48  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.30/1.48  tff(c_154, plain, (![A_70, B_71]: (k4_xboole_0(A_70, k2_xboole_0(A_70, B_71))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.30/1.48  tff(c_161, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_154])).
% 3.30/1.48  tff(c_34, plain, (![B_44]: (k4_xboole_0(k1_tarski(B_44), k1_tarski(B_44))!=k1_tarski(B_44))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.30/1.48  tff(c_201, plain, (![B_44]: (k1_tarski(B_44)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_161, c_34])).
% 3.30/1.48  tff(c_258, plain, (![A_88, B_89]: (r1_tarski(k1_tarski(A_88), B_89) | ~r2_hidden(A_88, B_89))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.30/1.48  tff(c_32, plain, (![A_41, B_42]: (~r1_tarski(A_41, k2_zfmisc_1(A_41, B_42)) | k1_xboole_0=A_41)), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.30/1.48  tff(c_265, plain, (![A_88, B_42]: (k1_tarski(A_88)=k1_xboole_0 | ~r2_hidden(A_88, k2_zfmisc_1(k1_tarski(A_88), B_42)))), inference(resolution, [status(thm)], [c_258, c_32])).
% 3.30/1.48  tff(c_273, plain, (![A_88, B_42]: (~r2_hidden(A_88, k2_zfmisc_1(k1_tarski(A_88), B_42)))), inference(negUnitSimplification, [status(thm)], [c_201, c_265])).
% 3.30/1.48  tff(c_360, plain, (![A_124, B_125]: (~r2_hidden(A_124, k1_tarski(k4_tarski(A_124, B_125))))), inference(superposition, [status(thm), theory('equality')], [c_332, c_273])).
% 3.30/1.48  tff(c_363, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_168, c_360])).
% 3.30/1.48  tff(c_456, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_453, c_363])).
% 3.30/1.48  tff(c_457, plain, ('#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_164])).
% 3.30/1.48  tff(c_460, plain, (k4_tarski('#skF_4', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_457, c_90])).
% 3.30/1.48  tff(c_510, plain, (![B_44]: (k1_tarski(B_44)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_161, c_34])).
% 3.30/1.48  tff(c_618, plain, (![A_239, B_240]: (k2_zfmisc_1(k1_tarski(A_239), k1_tarski(B_240))=k1_tarski(k4_tarski(A_239, B_240)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.30/1.48  tff(c_30, plain, (![A_41, B_42]: (~r1_tarski(A_41, k2_zfmisc_1(B_42, A_41)) | k1_xboole_0=A_41)), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.30/1.48  tff(c_627, plain, (![B_240, A_239]: (~r1_tarski(k1_tarski(B_240), k1_tarski(k4_tarski(A_239, B_240))) | k1_tarski(B_240)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_618, c_30])).
% 3.30/1.48  tff(c_652, plain, (![B_245, A_246]: (~r1_tarski(k1_tarski(B_245), k1_tarski(k4_tarski(A_246, B_245))))), inference(negUnitSimplification, [status(thm)], [c_510, c_627])).
% 3.30/1.48  tff(c_655, plain, (~r1_tarski(k1_tarski('#skF_3'), k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_460, c_652])).
% 3.30/1.48  tff(c_673, plain, (~r2_hidden('#skF_3', k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_26, c_655])).
% 3.30/1.48  tff(c_723, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_720, c_673])).
% 3.30/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.30/1.48  
% 3.30/1.48  Inference rules
% 3.30/1.48  ----------------------
% 3.30/1.48  #Ref     : 0
% 3.30/1.48  #Sup     : 151
% 3.30/1.48  #Fact    : 0
% 3.30/1.48  #Define  : 0
% 3.30/1.48  #Split   : 1
% 3.30/1.48  #Chain   : 0
% 3.30/1.48  #Close   : 0
% 3.30/1.48  
% 3.30/1.48  Ordering : KBO
% 3.30/1.48  
% 3.30/1.48  Simplification rules
% 3.30/1.48  ----------------------
% 3.30/1.48  #Subsume      : 6
% 3.30/1.48  #Demod        : 21
% 3.30/1.48  #Tautology    : 96
% 3.30/1.48  #SimpNegUnit  : 10
% 3.30/1.48  #BackRed      : 7
% 3.30/1.48  
% 3.30/1.48  #Partial instantiations: 0
% 3.30/1.48  #Strategies tried      : 1
% 3.30/1.48  
% 3.30/1.48  Timing (in seconds)
% 3.30/1.48  ----------------------
% 3.30/1.49  Preprocessing        : 0.37
% 3.30/1.49  Parsing              : 0.18
% 3.30/1.49  CNF conversion       : 0.03
% 3.30/1.49  Main loop            : 0.33
% 3.30/1.49  Inferencing          : 0.11
% 3.30/1.49  Reduction            : 0.10
% 3.30/1.49  Demodulation         : 0.07
% 3.30/1.49  BG Simplification    : 0.02
% 3.30/1.49  Subsumption          : 0.07
% 3.30/1.49  Abstraction          : 0.02
% 3.30/1.49  MUC search           : 0.00
% 3.30/1.49  Cooper               : 0.00
% 3.30/1.49  Total                : 0.75
% 3.30/1.49  Index Insertion      : 0.00
% 3.30/1.49  Index Deletion       : 0.00
% 3.30/1.49  Index Matching       : 0.00
% 3.30/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
