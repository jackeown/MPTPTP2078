%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:15 EST 2020

% Result     : Theorem 3.71s
% Output     : CNFRefutation 3.87s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 141 expanded)
%              Number of leaves         :   42 (  67 expanded)
%              Depth                    :    7
%              Number of atoms          :   85 ( 164 expanded)
%              Number of equality atoms :   56 ( 128 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_mcart_1 > k1_tarski > k1_setfam_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(f_89,axiom,(
    ! [A,B,C,D,E,F] :
      ( F = k3_enumset1(A,B,C,D,E)
    <=> ! [G] :
          ( r2_hidden(G,F)
        <=> ~ ( G != A
              & G != B
              & G != C
              & G != D
              & G != E ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_enumset1)).

tff(f_105,negated_conjecture,(
    ~ ! [A] :
        ( ? [B,C] : A = k4_tarski(B,C)
       => ( A != k1_mcart_1(A)
          & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_95,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k1_tarski(A),k2_tarski(B,C)) = k2_tarski(k4_tarski(A,B),k4_tarski(A,C))
      & k2_zfmisc_1(k2_tarski(A,B),k1_tarski(C)) = k2_tarski(k4_tarski(A,C),k4_tarski(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).

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

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

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

tff(c_739,plain,(
    ! [A_233,B_234,C_235,D_236] : k3_enumset1(A_233,A_233,B_234,C_235,D_236) = k2_enumset1(A_233,B_234,C_235,D_236) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_48,plain,(
    ! [B_49,G_56,A_48,D_51,E_52] : r2_hidden(G_56,k3_enumset1(A_48,B_49,G_56,D_51,E_52)) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_763,plain,(
    ! [B_237,A_238,C_239,D_240] : r2_hidden(B_237,k2_enumset1(A_238,B_237,C_239,D_240)) ),
    inference(superposition,[status(thm),theory(equality)],[c_739,c_48])).

tff(c_767,plain,(
    ! [A_241,B_242,C_243] : r2_hidden(A_241,k1_enumset1(A_241,B_242,C_243)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_763])).

tff(c_771,plain,(
    ! [A_244,B_245] : r2_hidden(A_244,k2_tarski(A_244,B_245)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_767])).

tff(c_774,plain,(
    ! [A_9] : r2_hidden(A_9,k1_tarski(A_9)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_771])).

tff(c_331,plain,(
    ! [A_127,B_128,C_129,D_130] : k3_enumset1(A_127,A_127,B_128,C_129,D_130) = k2_enumset1(A_127,B_128,C_129,D_130) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_46,plain,(
    ! [B_49,G_56,A_48,E_52,C_50] : r2_hidden(G_56,k3_enumset1(A_48,B_49,C_50,G_56,E_52)) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_355,plain,(
    ! [C_131,A_132,B_133,D_134] : r2_hidden(C_131,k2_enumset1(A_132,B_133,C_131,D_134)) ),
    inference(superposition,[status(thm),theory(equality)],[c_331,c_46])).

tff(c_359,plain,(
    ! [B_135,A_136,C_137] : r2_hidden(B_135,k1_enumset1(A_136,B_135,C_137)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_355])).

tff(c_416,plain,(
    ! [A_141,B_142] : r2_hidden(A_141,k2_tarski(A_141,B_142)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_359])).

tff(c_422,plain,(
    ! [A_9] : r2_hidden(A_9,k1_tarski(A_9)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_416])).

tff(c_86,plain,(
    k4_tarski('#skF_4','#skF_5') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_118,plain,(
    ! [A_66,B_67] : k1_mcart_1(k4_tarski(A_66,B_67)) = A_66 ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_127,plain,(
    k1_mcart_1('#skF_3') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_118])).

tff(c_130,plain,(
    ! [A_68,B_69] : k2_mcart_1(k4_tarski(A_68,B_69)) = B_69 ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_139,plain,(
    k2_mcart_1('#skF_3') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_130])).

tff(c_84,plain,
    ( k2_mcart_1('#skF_3') = '#skF_3'
    | k1_mcart_1('#skF_3') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_160,plain,
    ( '#skF_5' = '#skF_3'
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_139,c_84])).

tff(c_161,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_160])).

tff(c_164,plain,(
    k4_tarski('#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_86])).

tff(c_363,plain,(
    ! [A_138,B_139,C_140] : k2_zfmisc_1(k1_tarski(A_138),k2_tarski(B_139,C_140)) = k2_tarski(k4_tarski(A_138,B_139),k4_tarski(A_138,C_140)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_407,plain,(
    ! [A_138,B_139] : k2_zfmisc_1(k1_tarski(A_138),k2_tarski(B_139,B_139)) = k1_tarski(k4_tarski(A_138,B_139)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_363])).

tff(c_539,plain,(
    ! [A_172,B_173] : k2_zfmisc_1(k1_tarski(A_172),k1_tarski(B_173)) = k1_tarski(k4_tarski(A_172,B_173)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_407])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_150,plain,(
    ! [A_70,B_71] : k4_xboole_0(A_70,k2_xboole_0(A_70,B_71)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_157,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_150])).

tff(c_34,plain,(
    ! [B_44] : k4_xboole_0(k1_tarski(B_44),k1_tarski(B_44)) != k1_tarski(B_44) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_202,plain,(
    ! [B_44] : k1_tarski(B_44) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_34])).

tff(c_26,plain,(
    ! [A_37,B_38] :
      ( r1_tarski(k1_tarski(A_37),B_38)
      | ~ r2_hidden(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_235,plain,(
    ! [A_83,B_84] :
      ( ~ r1_tarski(A_83,k2_zfmisc_1(A_83,B_84))
      | k1_xboole_0 = A_83 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_239,plain,(
    ! [A_37,B_84] :
      ( k1_tarski(A_37) = k1_xboole_0
      | ~ r2_hidden(A_37,k2_zfmisc_1(k1_tarski(A_37),B_84)) ) ),
    inference(resolution,[status(thm)],[c_26,c_235])).

tff(c_242,plain,(
    ! [A_37,B_84] : ~ r2_hidden(A_37,k2_zfmisc_1(k1_tarski(A_37),B_84)) ),
    inference(negUnitSimplification,[status(thm)],[c_202,c_239])).

tff(c_566,plain,(
    ! [A_176,B_177] : ~ r2_hidden(A_176,k1_tarski(k4_tarski(A_176,B_177))) ),
    inference(superposition,[status(thm),theory(equality)],[c_539,c_242])).

tff(c_569,plain,(
    ~ r2_hidden('#skF_4',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_164,c_566])).

tff(c_572,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_422,c_569])).

tff(c_573,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_160])).

tff(c_585,plain,(
    k4_tarski('#skF_4','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_573,c_86])).

tff(c_775,plain,(
    ! [A_246,B_247,C_248] : k2_zfmisc_1(k1_tarski(A_246),k2_tarski(B_247,C_248)) = k2_tarski(k4_tarski(A_246,B_247),k4_tarski(A_246,C_248)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_822,plain,(
    ! [A_246,B_247] : k2_zfmisc_1(k1_tarski(A_246),k2_tarski(B_247,B_247)) = k1_tarski(k4_tarski(A_246,B_247)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_775])).

tff(c_947,plain,(
    ! [A_278,B_279] : k2_zfmisc_1(k1_tarski(A_278),k1_tarski(B_279)) = k1_tarski(k4_tarski(A_278,B_279)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_822])).

tff(c_613,plain,(
    ! [B_44] : k1_tarski(B_44) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_34])).

tff(c_634,plain,(
    ! [A_188,B_189] :
      ( ~ r1_tarski(A_188,k2_zfmisc_1(B_189,A_188))
      | k1_xboole_0 = A_188 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_638,plain,(
    ! [A_37,B_189] :
      ( k1_tarski(A_37) = k1_xboole_0
      | ~ r2_hidden(A_37,k2_zfmisc_1(B_189,k1_tarski(A_37))) ) ),
    inference(resolution,[status(thm)],[c_26,c_634])).

tff(c_641,plain,(
    ! [A_37,B_189] : ~ r2_hidden(A_37,k2_zfmisc_1(B_189,k1_tarski(A_37))) ),
    inference(negUnitSimplification,[status(thm)],[c_613,c_638])).

tff(c_983,plain,(
    ! [B_288,A_289] : ~ r2_hidden(B_288,k1_tarski(k4_tarski(A_289,B_288))) ),
    inference(superposition,[status(thm),theory(equality)],[c_947,c_641])).

tff(c_986,plain,(
    ~ r2_hidden('#skF_3',k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_585,c_983])).

tff(c_989,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_774,c_986])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:38:55 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.71/1.80  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.71/1.81  
% 3.71/1.81  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.81/1.81  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_mcart_1 > k1_tarski > k1_setfam_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4
% 3.81/1.81  
% 3.81/1.81  %Foreground sorts:
% 3.81/1.81  
% 3.81/1.81  
% 3.81/1.81  %Background operators:
% 3.81/1.81  
% 3.81/1.81  
% 3.81/1.81  %Foreground operators:
% 3.81/1.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.81/1.81  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i) > $i).
% 3.81/1.81  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i) > $i).
% 3.81/1.81  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.81/1.81  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.81/1.81  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.81/1.81  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.81/1.81  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.81/1.81  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.81/1.81  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.81/1.81  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.81/1.81  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.81/1.81  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.81/1.81  tff('#skF_5', type, '#skF_5': $i).
% 3.81/1.81  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.81/1.81  tff('#skF_3', type, '#skF_3': $i).
% 3.81/1.81  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.81/1.81  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.81/1.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.81/1.81  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 3.81/1.81  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.81/1.81  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.81/1.81  tff('#skF_4', type, '#skF_4': $i).
% 3.81/1.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.81/1.81  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 3.81/1.81  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.81/1.81  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.81/1.81  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.81/1.81  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.81/1.81  
% 3.87/1.83  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.87/1.83  tff(f_37, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.87/1.83  tff(f_39, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 3.87/1.83  tff(f_41, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 3.87/1.83  tff(f_89, axiom, (![A, B, C, D, E, F]: ((F = k3_enumset1(A, B, C, D, E)) <=> (![G]: (r2_hidden(G, F) <=> ~((((~(G = A) & ~(G = B)) & ~(G = C)) & ~(G = D)) & ~(G = E)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_enumset1)).
% 3.87/1.83  tff(f_105, negated_conjecture, ~(![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_mcart_1)).
% 3.87/1.83  tff(f_95, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 3.87/1.83  tff(f_68, axiom, (![A, B, C]: ((k2_zfmisc_1(k1_tarski(A), k2_tarski(B, C)) = k2_tarski(k4_tarski(A, B), k4_tarski(A, C))) & (k2_zfmisc_1(k2_tarski(A, B), k1_tarski(C)) = k2_tarski(k4_tarski(A, C), k4_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_zfmisc_1)).
% 3.87/1.83  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 3.87/1.83  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 3.87/1.83  tff(f_64, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 3.87/1.83  tff(f_51, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.87/1.83  tff(f_59, axiom, (![A, B]: ((r1_tarski(A, k2_zfmisc_1(A, B)) | r1_tarski(A, k2_zfmisc_1(B, A))) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t135_zfmisc_1)).
% 3.87/1.83  tff(c_10, plain, (![A_9]: (k2_tarski(A_9, A_9)=k1_tarski(A_9))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.87/1.83  tff(c_12, plain, (![A_10, B_11]: (k1_enumset1(A_10, A_10, B_11)=k2_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.87/1.83  tff(c_14, plain, (![A_12, B_13, C_14]: (k2_enumset1(A_12, A_12, B_13, C_14)=k1_enumset1(A_12, B_13, C_14))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.87/1.83  tff(c_739, plain, (![A_233, B_234, C_235, D_236]: (k3_enumset1(A_233, A_233, B_234, C_235, D_236)=k2_enumset1(A_233, B_234, C_235, D_236))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.87/1.83  tff(c_48, plain, (![B_49, G_56, A_48, D_51, E_52]: (r2_hidden(G_56, k3_enumset1(A_48, B_49, G_56, D_51, E_52)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.87/1.83  tff(c_763, plain, (![B_237, A_238, C_239, D_240]: (r2_hidden(B_237, k2_enumset1(A_238, B_237, C_239, D_240)))), inference(superposition, [status(thm), theory('equality')], [c_739, c_48])).
% 3.87/1.83  tff(c_767, plain, (![A_241, B_242, C_243]: (r2_hidden(A_241, k1_enumset1(A_241, B_242, C_243)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_763])).
% 3.87/1.83  tff(c_771, plain, (![A_244, B_245]: (r2_hidden(A_244, k2_tarski(A_244, B_245)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_767])).
% 3.87/1.83  tff(c_774, plain, (![A_9]: (r2_hidden(A_9, k1_tarski(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_771])).
% 3.87/1.83  tff(c_331, plain, (![A_127, B_128, C_129, D_130]: (k3_enumset1(A_127, A_127, B_128, C_129, D_130)=k2_enumset1(A_127, B_128, C_129, D_130))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.87/1.83  tff(c_46, plain, (![B_49, G_56, A_48, E_52, C_50]: (r2_hidden(G_56, k3_enumset1(A_48, B_49, C_50, G_56, E_52)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.87/1.83  tff(c_355, plain, (![C_131, A_132, B_133, D_134]: (r2_hidden(C_131, k2_enumset1(A_132, B_133, C_131, D_134)))), inference(superposition, [status(thm), theory('equality')], [c_331, c_46])).
% 3.87/1.83  tff(c_359, plain, (![B_135, A_136, C_137]: (r2_hidden(B_135, k1_enumset1(A_136, B_135, C_137)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_355])).
% 3.87/1.83  tff(c_416, plain, (![A_141, B_142]: (r2_hidden(A_141, k2_tarski(A_141, B_142)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_359])).
% 3.87/1.83  tff(c_422, plain, (![A_9]: (r2_hidden(A_9, k1_tarski(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_416])).
% 3.87/1.83  tff(c_86, plain, (k4_tarski('#skF_4', '#skF_5')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.87/1.83  tff(c_118, plain, (![A_66, B_67]: (k1_mcart_1(k4_tarski(A_66, B_67))=A_66)), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.87/1.83  tff(c_127, plain, (k1_mcart_1('#skF_3')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_86, c_118])).
% 3.87/1.83  tff(c_130, plain, (![A_68, B_69]: (k2_mcart_1(k4_tarski(A_68, B_69))=B_69)), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.87/1.83  tff(c_139, plain, (k2_mcart_1('#skF_3')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_86, c_130])).
% 3.87/1.83  tff(c_84, plain, (k2_mcart_1('#skF_3')='#skF_3' | k1_mcart_1('#skF_3')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.87/1.83  tff(c_160, plain, ('#skF_5'='#skF_3' | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_127, c_139, c_84])).
% 3.87/1.83  tff(c_161, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_160])).
% 3.87/1.83  tff(c_164, plain, (k4_tarski('#skF_4', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_161, c_86])).
% 3.87/1.83  tff(c_363, plain, (![A_138, B_139, C_140]: (k2_zfmisc_1(k1_tarski(A_138), k2_tarski(B_139, C_140))=k2_tarski(k4_tarski(A_138, B_139), k4_tarski(A_138, C_140)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.87/1.83  tff(c_407, plain, (![A_138, B_139]: (k2_zfmisc_1(k1_tarski(A_138), k2_tarski(B_139, B_139))=k1_tarski(k4_tarski(A_138, B_139)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_363])).
% 3.87/1.83  tff(c_539, plain, (![A_172, B_173]: (k2_zfmisc_1(k1_tarski(A_172), k1_tarski(B_173))=k1_tarski(k4_tarski(A_172, B_173)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_407])).
% 3.87/1.83  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.87/1.83  tff(c_150, plain, (![A_70, B_71]: (k4_xboole_0(A_70, k2_xboole_0(A_70, B_71))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.87/1.83  tff(c_157, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_150])).
% 3.87/1.83  tff(c_34, plain, (![B_44]: (k4_xboole_0(k1_tarski(B_44), k1_tarski(B_44))!=k1_tarski(B_44))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.87/1.83  tff(c_202, plain, (![B_44]: (k1_tarski(B_44)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_157, c_34])).
% 3.87/1.83  tff(c_26, plain, (![A_37, B_38]: (r1_tarski(k1_tarski(A_37), B_38) | ~r2_hidden(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.87/1.83  tff(c_235, plain, (![A_83, B_84]: (~r1_tarski(A_83, k2_zfmisc_1(A_83, B_84)) | k1_xboole_0=A_83)), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.87/1.83  tff(c_239, plain, (![A_37, B_84]: (k1_tarski(A_37)=k1_xboole_0 | ~r2_hidden(A_37, k2_zfmisc_1(k1_tarski(A_37), B_84)))), inference(resolution, [status(thm)], [c_26, c_235])).
% 3.87/1.83  tff(c_242, plain, (![A_37, B_84]: (~r2_hidden(A_37, k2_zfmisc_1(k1_tarski(A_37), B_84)))), inference(negUnitSimplification, [status(thm)], [c_202, c_239])).
% 3.87/1.83  tff(c_566, plain, (![A_176, B_177]: (~r2_hidden(A_176, k1_tarski(k4_tarski(A_176, B_177))))), inference(superposition, [status(thm), theory('equality')], [c_539, c_242])).
% 3.87/1.83  tff(c_569, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_164, c_566])).
% 3.87/1.83  tff(c_572, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_422, c_569])).
% 3.87/1.83  tff(c_573, plain, ('#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_160])).
% 3.87/1.83  tff(c_585, plain, (k4_tarski('#skF_4', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_573, c_86])).
% 3.87/1.83  tff(c_775, plain, (![A_246, B_247, C_248]: (k2_zfmisc_1(k1_tarski(A_246), k2_tarski(B_247, C_248))=k2_tarski(k4_tarski(A_246, B_247), k4_tarski(A_246, C_248)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.87/1.83  tff(c_822, plain, (![A_246, B_247]: (k2_zfmisc_1(k1_tarski(A_246), k2_tarski(B_247, B_247))=k1_tarski(k4_tarski(A_246, B_247)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_775])).
% 3.87/1.83  tff(c_947, plain, (![A_278, B_279]: (k2_zfmisc_1(k1_tarski(A_278), k1_tarski(B_279))=k1_tarski(k4_tarski(A_278, B_279)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_822])).
% 3.87/1.83  tff(c_613, plain, (![B_44]: (k1_tarski(B_44)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_157, c_34])).
% 3.87/1.83  tff(c_634, plain, (![A_188, B_189]: (~r1_tarski(A_188, k2_zfmisc_1(B_189, A_188)) | k1_xboole_0=A_188)), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.87/1.83  tff(c_638, plain, (![A_37, B_189]: (k1_tarski(A_37)=k1_xboole_0 | ~r2_hidden(A_37, k2_zfmisc_1(B_189, k1_tarski(A_37))))), inference(resolution, [status(thm)], [c_26, c_634])).
% 3.87/1.83  tff(c_641, plain, (![A_37, B_189]: (~r2_hidden(A_37, k2_zfmisc_1(B_189, k1_tarski(A_37))))), inference(negUnitSimplification, [status(thm)], [c_613, c_638])).
% 3.87/1.83  tff(c_983, plain, (![B_288, A_289]: (~r2_hidden(B_288, k1_tarski(k4_tarski(A_289, B_288))))), inference(superposition, [status(thm), theory('equality')], [c_947, c_641])).
% 3.87/1.83  tff(c_986, plain, (~r2_hidden('#skF_3', k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_585, c_983])).
% 3.87/1.83  tff(c_989, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_774, c_986])).
% 3.87/1.83  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.87/1.83  
% 3.87/1.83  Inference rules
% 3.87/1.83  ----------------------
% 3.87/1.83  #Ref     : 0
% 3.87/1.83  #Sup     : 221
% 3.87/1.83  #Fact    : 0
% 3.87/1.83  #Define  : 0
% 3.87/1.83  #Split   : 1
% 3.87/1.83  #Chain   : 0
% 3.87/1.83  #Close   : 0
% 3.87/1.83  
% 3.87/1.83  Ordering : KBO
% 3.87/1.83  
% 3.87/1.83  Simplification rules
% 3.87/1.83  ----------------------
% 3.87/1.83  #Subsume      : 0
% 3.87/1.83  #Demod        : 49
% 3.87/1.83  #Tautology    : 124
% 3.87/1.83  #SimpNegUnit  : 16
% 3.87/1.83  #BackRed      : 5
% 3.87/1.83  
% 3.87/1.83  #Partial instantiations: 0
% 3.87/1.83  #Strategies tried      : 1
% 3.87/1.83  
% 3.87/1.83  Timing (in seconds)
% 3.87/1.83  ----------------------
% 3.87/1.83  Preprocessing        : 0.44
% 3.87/1.83  Parsing              : 0.23
% 3.87/1.83  CNF conversion       : 0.03
% 3.87/1.83  Main loop            : 0.54
% 3.87/1.83  Inferencing          : 0.20
% 3.87/1.83  Reduction            : 0.17
% 3.87/1.84  Demodulation         : 0.12
% 3.87/1.84  BG Simplification    : 0.03
% 3.87/1.84  Subsumption          : 0.09
% 3.87/1.84  Abstraction          : 0.03
% 3.87/1.84  MUC search           : 0.00
% 3.87/1.84  Cooper               : 0.00
% 3.87/1.84  Total                : 1.02
% 3.87/1.84  Index Insertion      : 0.00
% 3.87/1.84  Index Deletion       : 0.00
% 3.87/1.84  Index Matching       : 0.00
% 3.87/1.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
