%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:13 EST 2020

% Result     : Theorem 21.11s
% Output     : CNFRefutation 21.16s
% Verified   : 
% Statistics : Number of formulae       :   58 (  90 expanded)
%              Number of leaves         :   26 (  42 expanded)
%              Depth                    :   10
%              Number of atoms          :   45 (  84 expanded)
%              Number of equality atoms :   43 (  82 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k3_enumset1 > k2_enumset1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_35,axiom,(
    ! [A,B] : k2_enumset1(A,A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E] : k5_enumset1(A,A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k5_enumset1(A,B,C,D,E,F,G),k1_tarski(H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k2_xboole_0(A,B),C) = k2_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
      & k2_zfmisc_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).

tff(f_48,negated_conjecture,(
    ~ ! [A,B,C] :
        ( k2_zfmisc_1(k2_tarski(A,B),C) = k2_xboole_0(k2_zfmisc_1(k1_tarski(A),C),k2_zfmisc_1(k1_tarski(B),C))
        & k2_zfmisc_1(C,k2_tarski(A,B)) = k2_xboole_0(k2_zfmisc_1(C,k1_tarski(A)),k2_zfmisc_1(C,k1_tarski(B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_zfmisc_1)).

tff(c_4,plain,(
    ! [A_9] : k2_tarski(A_9,A_9) = k1_tarski(A_9) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_10,plain,(
    ! [A_21,B_22] : k2_enumset1(A_21,A_21,A_21,B_22) = k2_tarski(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6,plain,(
    ! [A_10,B_11,C_12,D_13] : k3_enumset1(A_10,A_10,B_11,C_12,D_13) = k2_enumset1(A_10,B_11,C_12,D_13) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [G_20,E_18,C_16,D_17,F_19,A_14,B_15] : k6_enumset1(A_14,A_14,B_15,C_16,D_17,E_18,F_19,G_20) = k5_enumset1(A_14,B_15,C_16,D_17,E_18,F_19,G_20) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12,plain,(
    ! [A_23,B_24,D_26,C_25,E_27] : k5_enumset1(A_23,A_23,A_23,B_24,C_25,D_26,E_27) = k3_enumset1(A_23,B_24,C_25,D_26,E_27) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_18988,plain,(
    ! [H_236,A_235,C_234,B_233,D_232,F_229,G_230,E_231] : k2_xboole_0(k5_enumset1(A_235,B_233,C_234,D_232,E_231,F_229,G_230),k1_tarski(H_236)) = k6_enumset1(A_235,B_233,C_234,D_232,E_231,F_229,G_230,H_236) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_25406,plain,(
    ! [H_273,D_274,C_270,E_271,B_272,A_275] : k6_enumset1(A_275,A_275,A_275,B_272,C_270,D_274,E_271,H_273) = k2_xboole_0(k3_enumset1(A_275,B_272,C_270,D_274,E_271),k1_tarski(H_273)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_18988])).

tff(c_37453,plain,(
    ! [E_317,B_322,C_321,D_319,G_320,F_318] : k5_enumset1(B_322,B_322,C_321,D_319,E_317,F_318,G_320) = k2_xboole_0(k3_enumset1(B_322,C_321,D_319,E_317,F_318),k1_tarski(G_320)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_25406])).

tff(c_37469,plain,(
    ! [E_317,C_321,D_319,G_320,F_318] : k2_xboole_0(k3_enumset1(C_321,C_321,D_319,E_317,F_318),k1_tarski(G_320)) = k3_enumset1(C_321,D_319,E_317,F_318,G_320) ),
    inference(superposition,[status(thm),theory(equality)],[c_37453,c_12])).

tff(c_37495,plain,(
    ! [C_323,D_326,F_324,G_325,E_327] : k2_xboole_0(k2_enumset1(C_323,D_326,E_327,F_324),k1_tarski(G_325)) = k3_enumset1(C_323,D_326,E_327,F_324,G_325) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_37469])).

tff(c_37507,plain,(
    ! [A_328,B_329,G_330] : k3_enumset1(A_328,A_328,A_328,B_329,G_330) = k2_xboole_0(k2_tarski(A_328,B_329),k1_tarski(G_330)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_37495])).

tff(c_37540,plain,(
    ! [A_331,B_332,G_333] : k2_xboole_0(k2_tarski(A_331,B_332),k1_tarski(G_333)) = k2_enumset1(A_331,A_331,B_332,G_333) ),
    inference(superposition,[status(thm),theory(equality)],[c_37507,c_6])).

tff(c_37556,plain,(
    ! [B_332,G_333] : k2_xboole_0(k2_tarski(B_332,B_332),k1_tarski(G_333)) = k2_tarski(B_332,G_333) ),
    inference(superposition,[status(thm),theory(equality)],[c_37540,c_10])).

tff(c_37576,plain,(
    ! [B_332,G_333] : k2_xboole_0(k1_tarski(B_332),k1_tarski(G_333)) = k2_tarski(B_332,G_333) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_37556])).

tff(c_1147,plain,(
    ! [H_86,A_85,F_79,B_83,C_84,G_80,E_81,D_82] : k2_xboole_0(k5_enumset1(A_85,B_83,C_84,D_82,E_81,F_79,G_80),k1_tarski(H_86)) = k6_enumset1(A_85,B_83,C_84,D_82,E_81,F_79,G_80,H_86) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1163,plain,(
    ! [E_88,A_92,H_91,B_89,C_87,D_90] : k6_enumset1(A_92,A_92,A_92,B_89,C_87,D_90,E_88,H_91) = k2_xboole_0(k3_enumset1(A_92,B_89,C_87,D_90,E_88),k1_tarski(H_91)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1147])).

tff(c_14806,plain,(
    ! [G_166,E_163,D_165,C_167,B_168,F_164] : k5_enumset1(B_168,B_168,C_167,D_165,E_163,F_164,G_166) = k2_xboole_0(k3_enumset1(B_168,C_167,D_165,E_163,F_164),k1_tarski(G_166)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_1163])).

tff(c_14837,plain,(
    ! [B_11,A_10,C_12,G_166,D_13] : k5_enumset1(A_10,A_10,A_10,B_11,C_12,D_13,G_166) = k2_xboole_0(k2_enumset1(A_10,B_11,C_12,D_13),k1_tarski(G_166)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_14806])).

tff(c_15859,plain,(
    ! [C_176,B_172,A_174,G_173,D_175] : k2_xboole_0(k2_enumset1(A_174,B_172,C_176,D_175),k1_tarski(G_173)) = k3_enumset1(A_174,B_172,C_176,D_175,G_173) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_14837])).

tff(c_15871,plain,(
    ! [A_177,B_178,G_179] : k3_enumset1(A_177,A_177,A_177,B_178,G_179) = k2_xboole_0(k2_tarski(A_177,B_178),k1_tarski(G_179)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_15859])).

tff(c_15904,plain,(
    ! [A_180,B_181,G_182] : k2_xboole_0(k2_tarski(A_180,B_181),k1_tarski(G_182)) = k2_enumset1(A_180,A_180,B_181,G_182) ),
    inference(superposition,[status(thm),theory(equality)],[c_15871,c_6])).

tff(c_15920,plain,(
    ! [B_181,G_182] : k2_xboole_0(k2_tarski(B_181,B_181),k1_tarski(G_182)) = k2_tarski(B_181,G_182) ),
    inference(superposition,[status(thm),theory(equality)],[c_15904,c_10])).

tff(c_15940,plain,(
    ! [B_181,G_182] : k2_xboole_0(k1_tarski(B_181),k1_tarski(G_182)) = k2_tarski(B_181,G_182) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_15920])).

tff(c_14,plain,(
    ! [A_28,C_30,B_29] : k2_xboole_0(k2_zfmisc_1(A_28,C_30),k2_zfmisc_1(B_29,C_30)) = k2_zfmisc_1(k2_xboole_0(A_28,B_29),C_30) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_16,plain,(
    ! [C_30,A_28,B_29] : k2_xboole_0(k2_zfmisc_1(C_30,A_28),k2_zfmisc_1(C_30,B_29)) = k2_zfmisc_1(C_30,k2_xboole_0(A_28,B_29)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_20,plain,
    ( k2_xboole_0(k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_6'),k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_6')) != k2_zfmisc_1(k2_tarski('#skF_4','#skF_5'),'#skF_6')
    | k2_xboole_0(k2_zfmisc_1('#skF_3',k1_tarski('#skF_1')),k2_zfmisc_1('#skF_3',k1_tarski('#skF_2'))) != k2_zfmisc_1('#skF_3',k2_tarski('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_21,plain,
    ( k2_xboole_0(k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_6'),k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_6')) != k2_zfmisc_1(k2_tarski('#skF_4','#skF_5'),'#skF_6')
    | k2_zfmisc_1('#skF_3',k2_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2'))) != k2_zfmisc_1('#skF_3',k2_tarski('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_20])).

tff(c_22,plain,
    ( k2_zfmisc_1(k2_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_5')),'#skF_6') != k2_zfmisc_1(k2_tarski('#skF_4','#skF_5'),'#skF_6')
    | k2_zfmisc_1('#skF_3',k2_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2'))) != k2_zfmisc_1('#skF_3',k2_tarski('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_21])).

tff(c_147,plain,(
    k2_zfmisc_1('#skF_3',k2_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2'))) != k2_zfmisc_1('#skF_3',k2_tarski('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_15948,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15940,c_147])).

tff(c_15949,plain,(
    k2_zfmisc_1(k2_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_5')),'#skF_6') != k2_zfmisc_1(k2_tarski('#skF_4','#skF_5'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_37595,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_37576,c_15949])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:25:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 21.11/11.67  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 21.11/11.68  
% 21.11/11.68  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 21.11/11.68  %$ k6_enumset1 > k5_enumset1 > k3_enumset1 > k2_enumset1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 21.11/11.68  
% 21.11/11.68  %Foreground sorts:
% 21.11/11.68  
% 21.11/11.68  
% 21.11/11.68  %Background operators:
% 21.11/11.68  
% 21.11/11.68  
% 21.11/11.68  %Foreground operators:
% 21.11/11.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 21.11/11.68  tff(k1_tarski, type, k1_tarski: $i > $i).
% 21.11/11.68  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 21.11/11.68  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 21.11/11.68  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 21.11/11.68  tff('#skF_5', type, '#skF_5': $i).
% 21.11/11.68  tff('#skF_6', type, '#skF_6': $i).
% 21.11/11.68  tff('#skF_2', type, '#skF_2': $i).
% 21.11/11.68  tff('#skF_3', type, '#skF_3': $i).
% 21.11/11.68  tff('#skF_1', type, '#skF_1': $i).
% 21.11/11.68  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 21.11/11.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 21.11/11.68  tff(k3_tarski, type, k3_tarski: $i > $i).
% 21.11/11.68  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 21.11/11.68  tff('#skF_4', type, '#skF_4': $i).
% 21.11/11.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 21.11/11.68  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 21.11/11.68  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 21.11/11.68  
% 21.16/11.69  tff(f_29, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 21.16/11.69  tff(f_35, axiom, (![A, B]: (k2_enumset1(A, A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_enumset1)).
% 21.16/11.69  tff(f_31, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 21.16/11.69  tff(f_33, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 21.16/11.69  tff(f_37, axiom, (![A, B, C, D, E]: (k5_enumset1(A, A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_enumset1)).
% 21.16/11.69  tff(f_27, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k5_enumset1(A, B, C, D, E, F, G), k1_tarski(H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_enumset1)).
% 21.16/11.69  tff(f_41, axiom, (![A, B, C]: ((k2_zfmisc_1(k2_xboole_0(A, B), C) = k2_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C))) & (k2_zfmisc_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t120_zfmisc_1)).
% 21.16/11.69  tff(f_48, negated_conjecture, ~(![A, B, C]: ((k2_zfmisc_1(k2_tarski(A, B), C) = k2_xboole_0(k2_zfmisc_1(k1_tarski(A), C), k2_zfmisc_1(k1_tarski(B), C))) & (k2_zfmisc_1(C, k2_tarski(A, B)) = k2_xboole_0(k2_zfmisc_1(C, k1_tarski(A)), k2_zfmisc_1(C, k1_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t132_zfmisc_1)).
% 21.16/11.69  tff(c_4, plain, (![A_9]: (k2_tarski(A_9, A_9)=k1_tarski(A_9))), inference(cnfTransformation, [status(thm)], [f_29])).
% 21.16/11.69  tff(c_10, plain, (![A_21, B_22]: (k2_enumset1(A_21, A_21, A_21, B_22)=k2_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_35])).
% 21.16/11.69  tff(c_6, plain, (![A_10, B_11, C_12, D_13]: (k3_enumset1(A_10, A_10, B_11, C_12, D_13)=k2_enumset1(A_10, B_11, C_12, D_13))), inference(cnfTransformation, [status(thm)], [f_31])).
% 21.16/11.69  tff(c_8, plain, (![G_20, E_18, C_16, D_17, F_19, A_14, B_15]: (k6_enumset1(A_14, A_14, B_15, C_16, D_17, E_18, F_19, G_20)=k5_enumset1(A_14, B_15, C_16, D_17, E_18, F_19, G_20))), inference(cnfTransformation, [status(thm)], [f_33])).
% 21.16/11.69  tff(c_12, plain, (![A_23, B_24, D_26, C_25, E_27]: (k5_enumset1(A_23, A_23, A_23, B_24, C_25, D_26, E_27)=k3_enumset1(A_23, B_24, C_25, D_26, E_27))), inference(cnfTransformation, [status(thm)], [f_37])).
% 21.16/11.69  tff(c_18988, plain, (![H_236, A_235, C_234, B_233, D_232, F_229, G_230, E_231]: (k2_xboole_0(k5_enumset1(A_235, B_233, C_234, D_232, E_231, F_229, G_230), k1_tarski(H_236))=k6_enumset1(A_235, B_233, C_234, D_232, E_231, F_229, G_230, H_236))), inference(cnfTransformation, [status(thm)], [f_27])).
% 21.16/11.69  tff(c_25406, plain, (![H_273, D_274, C_270, E_271, B_272, A_275]: (k6_enumset1(A_275, A_275, A_275, B_272, C_270, D_274, E_271, H_273)=k2_xboole_0(k3_enumset1(A_275, B_272, C_270, D_274, E_271), k1_tarski(H_273)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_18988])).
% 21.16/11.69  tff(c_37453, plain, (![E_317, B_322, C_321, D_319, G_320, F_318]: (k5_enumset1(B_322, B_322, C_321, D_319, E_317, F_318, G_320)=k2_xboole_0(k3_enumset1(B_322, C_321, D_319, E_317, F_318), k1_tarski(G_320)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_25406])).
% 21.16/11.69  tff(c_37469, plain, (![E_317, C_321, D_319, G_320, F_318]: (k2_xboole_0(k3_enumset1(C_321, C_321, D_319, E_317, F_318), k1_tarski(G_320))=k3_enumset1(C_321, D_319, E_317, F_318, G_320))), inference(superposition, [status(thm), theory('equality')], [c_37453, c_12])).
% 21.16/11.69  tff(c_37495, plain, (![C_323, D_326, F_324, G_325, E_327]: (k2_xboole_0(k2_enumset1(C_323, D_326, E_327, F_324), k1_tarski(G_325))=k3_enumset1(C_323, D_326, E_327, F_324, G_325))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_37469])).
% 21.16/11.69  tff(c_37507, plain, (![A_328, B_329, G_330]: (k3_enumset1(A_328, A_328, A_328, B_329, G_330)=k2_xboole_0(k2_tarski(A_328, B_329), k1_tarski(G_330)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_37495])).
% 21.16/11.69  tff(c_37540, plain, (![A_331, B_332, G_333]: (k2_xboole_0(k2_tarski(A_331, B_332), k1_tarski(G_333))=k2_enumset1(A_331, A_331, B_332, G_333))), inference(superposition, [status(thm), theory('equality')], [c_37507, c_6])).
% 21.16/11.69  tff(c_37556, plain, (![B_332, G_333]: (k2_xboole_0(k2_tarski(B_332, B_332), k1_tarski(G_333))=k2_tarski(B_332, G_333))), inference(superposition, [status(thm), theory('equality')], [c_37540, c_10])).
% 21.16/11.69  tff(c_37576, plain, (![B_332, G_333]: (k2_xboole_0(k1_tarski(B_332), k1_tarski(G_333))=k2_tarski(B_332, G_333))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_37556])).
% 21.16/11.69  tff(c_1147, plain, (![H_86, A_85, F_79, B_83, C_84, G_80, E_81, D_82]: (k2_xboole_0(k5_enumset1(A_85, B_83, C_84, D_82, E_81, F_79, G_80), k1_tarski(H_86))=k6_enumset1(A_85, B_83, C_84, D_82, E_81, F_79, G_80, H_86))), inference(cnfTransformation, [status(thm)], [f_27])).
% 21.16/11.69  tff(c_1163, plain, (![E_88, A_92, H_91, B_89, C_87, D_90]: (k6_enumset1(A_92, A_92, A_92, B_89, C_87, D_90, E_88, H_91)=k2_xboole_0(k3_enumset1(A_92, B_89, C_87, D_90, E_88), k1_tarski(H_91)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_1147])).
% 21.16/11.69  tff(c_14806, plain, (![G_166, E_163, D_165, C_167, B_168, F_164]: (k5_enumset1(B_168, B_168, C_167, D_165, E_163, F_164, G_166)=k2_xboole_0(k3_enumset1(B_168, C_167, D_165, E_163, F_164), k1_tarski(G_166)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_1163])).
% 21.16/11.69  tff(c_14837, plain, (![B_11, A_10, C_12, G_166, D_13]: (k5_enumset1(A_10, A_10, A_10, B_11, C_12, D_13, G_166)=k2_xboole_0(k2_enumset1(A_10, B_11, C_12, D_13), k1_tarski(G_166)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_14806])).
% 21.16/11.69  tff(c_15859, plain, (![C_176, B_172, A_174, G_173, D_175]: (k2_xboole_0(k2_enumset1(A_174, B_172, C_176, D_175), k1_tarski(G_173))=k3_enumset1(A_174, B_172, C_176, D_175, G_173))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_14837])).
% 21.16/11.69  tff(c_15871, plain, (![A_177, B_178, G_179]: (k3_enumset1(A_177, A_177, A_177, B_178, G_179)=k2_xboole_0(k2_tarski(A_177, B_178), k1_tarski(G_179)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_15859])).
% 21.16/11.69  tff(c_15904, plain, (![A_180, B_181, G_182]: (k2_xboole_0(k2_tarski(A_180, B_181), k1_tarski(G_182))=k2_enumset1(A_180, A_180, B_181, G_182))), inference(superposition, [status(thm), theory('equality')], [c_15871, c_6])).
% 21.16/11.69  tff(c_15920, plain, (![B_181, G_182]: (k2_xboole_0(k2_tarski(B_181, B_181), k1_tarski(G_182))=k2_tarski(B_181, G_182))), inference(superposition, [status(thm), theory('equality')], [c_15904, c_10])).
% 21.16/11.69  tff(c_15940, plain, (![B_181, G_182]: (k2_xboole_0(k1_tarski(B_181), k1_tarski(G_182))=k2_tarski(B_181, G_182))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_15920])).
% 21.16/11.69  tff(c_14, plain, (![A_28, C_30, B_29]: (k2_xboole_0(k2_zfmisc_1(A_28, C_30), k2_zfmisc_1(B_29, C_30))=k2_zfmisc_1(k2_xboole_0(A_28, B_29), C_30))), inference(cnfTransformation, [status(thm)], [f_41])).
% 21.16/11.69  tff(c_16, plain, (![C_30, A_28, B_29]: (k2_xboole_0(k2_zfmisc_1(C_30, A_28), k2_zfmisc_1(C_30, B_29))=k2_zfmisc_1(C_30, k2_xboole_0(A_28, B_29)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 21.16/11.69  tff(c_20, plain, (k2_xboole_0(k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_5'), '#skF_6'))!=k2_zfmisc_1(k2_tarski('#skF_4', '#skF_5'), '#skF_6') | k2_xboole_0(k2_zfmisc_1('#skF_3', k1_tarski('#skF_1')), k2_zfmisc_1('#skF_3', k1_tarski('#skF_2')))!=k2_zfmisc_1('#skF_3', k2_tarski('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_48])).
% 21.16/11.69  tff(c_21, plain, (k2_xboole_0(k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_5'), '#skF_6'))!=k2_zfmisc_1(k2_tarski('#skF_4', '#skF_5'), '#skF_6') | k2_zfmisc_1('#skF_3', k2_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2')))!=k2_zfmisc_1('#skF_3', k2_tarski('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_20])).
% 21.16/11.69  tff(c_22, plain, (k2_zfmisc_1(k2_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_5')), '#skF_6')!=k2_zfmisc_1(k2_tarski('#skF_4', '#skF_5'), '#skF_6') | k2_zfmisc_1('#skF_3', k2_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2')))!=k2_zfmisc_1('#skF_3', k2_tarski('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_21])).
% 21.16/11.69  tff(c_147, plain, (k2_zfmisc_1('#skF_3', k2_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2')))!=k2_zfmisc_1('#skF_3', k2_tarski('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_22])).
% 21.16/11.69  tff(c_15948, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15940, c_147])).
% 21.16/11.69  tff(c_15949, plain, (k2_zfmisc_1(k2_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_5')), '#skF_6')!=k2_zfmisc_1(k2_tarski('#skF_4', '#skF_5'), '#skF_6')), inference(splitRight, [status(thm)], [c_22])).
% 21.16/11.69  tff(c_37595, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_37576, c_15949])).
% 21.16/11.69  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 21.16/11.69  
% 21.16/11.69  Inference rules
% 21.16/11.69  ----------------------
% 21.16/11.69  #Ref     : 0
% 21.16/11.69  #Sup     : 8949
% 21.16/11.69  #Fact    : 0
% 21.16/11.69  #Define  : 0
% 21.16/11.69  #Split   : 1
% 21.16/11.69  #Chain   : 0
% 21.16/11.69  #Close   : 0
% 21.16/11.69  
% 21.16/11.69  Ordering : KBO
% 21.16/11.69  
% 21.16/11.69  Simplification rules
% 21.16/11.69  ----------------------
% 21.16/11.69  #Subsume      : 533
% 21.16/11.69  #Demod        : 12950
% 21.16/11.69  #Tautology    : 740
% 21.16/11.69  #SimpNegUnit  : 0
% 21.16/11.69  #BackRed      : 7
% 21.16/11.69  
% 21.16/11.69  #Partial instantiations: 0
% 21.16/11.69  #Strategies tried      : 1
% 21.16/11.69  
% 21.16/11.69  Timing (in seconds)
% 21.16/11.69  ----------------------
% 21.16/11.70  Preprocessing        : 0.29
% 21.16/11.70  Parsing              : 0.15
% 21.16/11.70  CNF conversion       : 0.02
% 21.16/11.70  Main loop            : 10.64
% 21.16/11.70  Inferencing          : 1.55
% 21.16/11.70  Reduction            : 7.79
% 21.16/11.70  Demodulation         : 7.36
% 21.16/11.70  BG Simplification    : 0.34
% 21.16/11.70  Subsumption          : 0.76
% 21.16/11.70  Abstraction          : 0.57
% 21.16/11.70  MUC search           : 0.00
% 21.16/11.70  Cooper               : 0.00
% 21.16/11.70  Total                : 10.96
% 21.16/11.70  Index Insertion      : 0.00
% 21.16/11.70  Index Deletion       : 0.00
% 21.16/11.70  Index Matching       : 0.00
% 21.16/11.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
