%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:42 EST 2020

% Result     : Theorem 2.16s
% Output     : CNFRefutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :   64 (  83 expanded)
%              Number of leaves         :   32 (  41 expanded)
%              Depth                    :   14
%              Number of atoms          :   52 (  77 expanded)
%              Number of equality atoms :   43 (  64 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_63,negated_conjecture,(
    ~ ! [A,B] :
        ( A != B
       => k5_xboole_0(k1_tarski(A),k1_tarski(B)) = k2_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_40,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_44,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_46,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_48,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_50,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_52,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_38,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k5_enumset1(A,B,C,D,E,F,G),k1_tarski(H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_enumset1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
    <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l33_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_40,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_22,plain,(
    ! [A_19,B_20] : k1_enumset1(A_19,A_19,B_20) = k2_tarski(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_20,plain,(
    ! [A_18] : k2_tarski(A_18,A_18) = k1_tarski(A_18) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_24,plain,(
    ! [A_21,B_22,C_23] : k2_enumset1(A_21,A_21,B_22,C_23) = k1_enumset1(A_21,B_22,C_23) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_26,plain,(
    ! [A_24,B_25,C_26,D_27] : k3_enumset1(A_24,A_24,B_25,C_26,D_27) = k2_enumset1(A_24,B_25,C_26,D_27) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_28,plain,(
    ! [C_30,E_32,D_31,B_29,A_28] : k4_enumset1(A_28,A_28,B_29,C_30,D_31,E_32) = k3_enumset1(A_28,B_29,C_30,D_31,E_32) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_30,plain,(
    ! [D_36,F_38,E_37,A_33,B_34,C_35] : k5_enumset1(A_33,A_33,B_34,C_35,D_36,E_37,F_38) = k4_enumset1(A_33,B_34,C_35,D_36,E_37,F_38) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_32,plain,(
    ! [E_43,G_45,F_44,D_42,A_39,C_41,B_40] : k6_enumset1(A_39,A_39,B_40,C_41,D_42,E_43,F_44,G_45) = k5_enumset1(A_39,B_40,C_41,D_42,E_43,F_44,G_45) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_197,plain,(
    ! [E_104,C_108,A_105,H_103,F_107,G_101,B_102,D_106] : k2_xboole_0(k5_enumset1(A_105,B_102,C_108,D_106,E_104,F_107,G_101),k1_tarski(H_103)) = k6_enumset1(A_105,B_102,C_108,D_106,E_104,F_107,G_101,H_103) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_206,plain,(
    ! [D_36,F_38,E_37,H_103,A_33,B_34,C_35] : k6_enumset1(A_33,A_33,B_34,C_35,D_36,E_37,F_38,H_103) = k2_xboole_0(k4_enumset1(A_33,B_34,C_35,D_36,E_37,F_38),k1_tarski(H_103)) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_197])).

tff(c_210,plain,(
    ! [B_115,F_113,E_111,A_109,H_110,D_114,C_112] : k2_xboole_0(k4_enumset1(A_109,B_115,C_112,D_114,E_111,F_113),k1_tarski(H_110)) = k5_enumset1(A_109,B_115,C_112,D_114,E_111,F_113,H_110) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_206])).

tff(c_219,plain,(
    ! [C_30,E_32,H_110,D_31,B_29,A_28] : k5_enumset1(A_28,A_28,B_29,C_30,D_31,E_32,H_110) = k2_xboole_0(k3_enumset1(A_28,B_29,C_30,D_31,E_32),k1_tarski(H_110)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_210])).

tff(c_223,plain,(
    ! [H_119,A_117,E_116,D_121,B_120,C_118] : k2_xboole_0(k3_enumset1(A_117,B_120,C_118,D_121,E_116),k1_tarski(H_119)) = k4_enumset1(A_117,B_120,C_118,D_121,E_116,H_119) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_219])).

tff(c_232,plain,(
    ! [A_24,H_119,B_25,D_27,C_26] : k4_enumset1(A_24,A_24,B_25,C_26,D_27,H_119) = k2_xboole_0(k2_enumset1(A_24,B_25,C_26,D_27),k1_tarski(H_119)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_223])).

tff(c_236,plain,(
    ! [H_124,D_126,C_122,A_125,B_123] : k2_xboole_0(k2_enumset1(A_125,B_123,C_122,D_126),k1_tarski(H_124)) = k3_enumset1(A_125,B_123,C_122,D_126,H_124) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_232])).

tff(c_245,plain,(
    ! [A_21,B_22,C_23,H_124] : k3_enumset1(A_21,A_21,B_22,C_23,H_124) = k2_xboole_0(k1_enumset1(A_21,B_22,C_23),k1_tarski(H_124)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_236])).

tff(c_249,plain,(
    ! [A_127,B_128,C_129,H_130] : k2_xboole_0(k1_enumset1(A_127,B_128,C_129),k1_tarski(H_130)) = k2_enumset1(A_127,B_128,C_129,H_130) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_245])).

tff(c_258,plain,(
    ! [A_19,B_20,H_130] : k2_xboole_0(k2_tarski(A_19,B_20),k1_tarski(H_130)) = k2_enumset1(A_19,A_19,B_20,H_130) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_249])).

tff(c_262,plain,(
    ! [A_131,B_132,H_133] : k2_xboole_0(k2_tarski(A_131,B_132),k1_tarski(H_133)) = k1_enumset1(A_131,B_132,H_133) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_258])).

tff(c_271,plain,(
    ! [A_18,H_133] : k2_xboole_0(k1_tarski(A_18),k1_tarski(H_133)) = k1_enumset1(A_18,A_18,H_133) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_262])).

tff(c_274,plain,(
    ! [A_18,H_133] : k2_xboole_0(k1_tarski(A_18),k1_tarski(H_133)) = k2_tarski(A_18,H_133) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_271])).

tff(c_94,plain,(
    ! [A_63,B_64] :
      ( k4_xboole_0(k1_tarski(A_63),B_64) = k1_tarski(A_63)
      | r2_hidden(A_63,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_4,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k4_xboole_0(B_4,A_3)) = k2_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_120,plain,(
    ! [B_71,A_72] :
      ( k5_xboole_0(B_71,k1_tarski(A_72)) = k2_xboole_0(B_71,k1_tarski(A_72))
      | r2_hidden(A_72,B_71) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_4])).

tff(c_38,plain,(
    k5_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) != k2_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_126,plain,
    ( k2_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) != k2_tarski('#skF_3','#skF_4')
    | r2_hidden('#skF_4',k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_38])).

tff(c_139,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) != k2_tarski('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_126])).

tff(c_277,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_274,c_139])).

tff(c_278,plain,(
    r2_hidden('#skF_4',k1_tarski('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_126])).

tff(c_6,plain,(
    ! [C_9,A_5] :
      ( C_9 = A_5
      | ~ r2_hidden(C_9,k1_tarski(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_282,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_278,c_6])).

tff(c_286,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_282])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:59:06 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.16/1.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.27  
% 2.16/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.27  %$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.16/1.27  
% 2.16/1.27  %Foreground sorts:
% 2.16/1.27  
% 2.16/1.27  
% 2.16/1.27  %Background operators:
% 2.16/1.27  
% 2.16/1.27  
% 2.16/1.27  %Foreground operators:
% 2.16/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.16/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.16/1.27  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.16/1.27  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.16/1.27  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.16/1.27  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.16/1.27  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.16/1.27  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.16/1.27  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.16/1.27  tff('#skF_3', type, '#skF_3': $i).
% 2.16/1.27  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.16/1.27  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.16/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.16/1.27  tff('#skF_4', type, '#skF_4': $i).
% 2.16/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.16/1.27  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.16/1.27  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.16/1.27  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.16/1.27  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.16/1.27  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.16/1.27  
% 2.16/1.29  tff(f_63, negated_conjecture, ~(![A, B]: (~(A = B) => (k5_xboole_0(k1_tarski(A), k1_tarski(B)) = k2_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_zfmisc_1)).
% 2.16/1.29  tff(f_42, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.16/1.29  tff(f_40, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.16/1.29  tff(f_44, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.16/1.29  tff(f_46, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 2.16/1.29  tff(f_48, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 2.16/1.29  tff(f_50, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 2.16/1.29  tff(f_52, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 2.16/1.29  tff(f_38, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k5_enumset1(A, B, C, D, E, F, G), k1_tarski(H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_enumset1)).
% 2.16/1.29  tff(f_57, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l33_zfmisc_1)).
% 2.16/1.29  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.16/1.29  tff(f_36, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.16/1.29  tff(c_40, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.16/1.29  tff(c_22, plain, (![A_19, B_20]: (k1_enumset1(A_19, A_19, B_20)=k2_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.16/1.29  tff(c_20, plain, (![A_18]: (k2_tarski(A_18, A_18)=k1_tarski(A_18))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.16/1.29  tff(c_24, plain, (![A_21, B_22, C_23]: (k2_enumset1(A_21, A_21, B_22, C_23)=k1_enumset1(A_21, B_22, C_23))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.16/1.29  tff(c_26, plain, (![A_24, B_25, C_26, D_27]: (k3_enumset1(A_24, A_24, B_25, C_26, D_27)=k2_enumset1(A_24, B_25, C_26, D_27))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.16/1.29  tff(c_28, plain, (![C_30, E_32, D_31, B_29, A_28]: (k4_enumset1(A_28, A_28, B_29, C_30, D_31, E_32)=k3_enumset1(A_28, B_29, C_30, D_31, E_32))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.16/1.29  tff(c_30, plain, (![D_36, F_38, E_37, A_33, B_34, C_35]: (k5_enumset1(A_33, A_33, B_34, C_35, D_36, E_37, F_38)=k4_enumset1(A_33, B_34, C_35, D_36, E_37, F_38))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.16/1.29  tff(c_32, plain, (![E_43, G_45, F_44, D_42, A_39, C_41, B_40]: (k6_enumset1(A_39, A_39, B_40, C_41, D_42, E_43, F_44, G_45)=k5_enumset1(A_39, B_40, C_41, D_42, E_43, F_44, G_45))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.16/1.29  tff(c_197, plain, (![E_104, C_108, A_105, H_103, F_107, G_101, B_102, D_106]: (k2_xboole_0(k5_enumset1(A_105, B_102, C_108, D_106, E_104, F_107, G_101), k1_tarski(H_103))=k6_enumset1(A_105, B_102, C_108, D_106, E_104, F_107, G_101, H_103))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.16/1.29  tff(c_206, plain, (![D_36, F_38, E_37, H_103, A_33, B_34, C_35]: (k6_enumset1(A_33, A_33, B_34, C_35, D_36, E_37, F_38, H_103)=k2_xboole_0(k4_enumset1(A_33, B_34, C_35, D_36, E_37, F_38), k1_tarski(H_103)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_197])).
% 2.16/1.29  tff(c_210, plain, (![B_115, F_113, E_111, A_109, H_110, D_114, C_112]: (k2_xboole_0(k4_enumset1(A_109, B_115, C_112, D_114, E_111, F_113), k1_tarski(H_110))=k5_enumset1(A_109, B_115, C_112, D_114, E_111, F_113, H_110))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_206])).
% 2.16/1.29  tff(c_219, plain, (![C_30, E_32, H_110, D_31, B_29, A_28]: (k5_enumset1(A_28, A_28, B_29, C_30, D_31, E_32, H_110)=k2_xboole_0(k3_enumset1(A_28, B_29, C_30, D_31, E_32), k1_tarski(H_110)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_210])).
% 2.16/1.29  tff(c_223, plain, (![H_119, A_117, E_116, D_121, B_120, C_118]: (k2_xboole_0(k3_enumset1(A_117, B_120, C_118, D_121, E_116), k1_tarski(H_119))=k4_enumset1(A_117, B_120, C_118, D_121, E_116, H_119))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_219])).
% 2.16/1.29  tff(c_232, plain, (![A_24, H_119, B_25, D_27, C_26]: (k4_enumset1(A_24, A_24, B_25, C_26, D_27, H_119)=k2_xboole_0(k2_enumset1(A_24, B_25, C_26, D_27), k1_tarski(H_119)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_223])).
% 2.16/1.29  tff(c_236, plain, (![H_124, D_126, C_122, A_125, B_123]: (k2_xboole_0(k2_enumset1(A_125, B_123, C_122, D_126), k1_tarski(H_124))=k3_enumset1(A_125, B_123, C_122, D_126, H_124))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_232])).
% 2.16/1.29  tff(c_245, plain, (![A_21, B_22, C_23, H_124]: (k3_enumset1(A_21, A_21, B_22, C_23, H_124)=k2_xboole_0(k1_enumset1(A_21, B_22, C_23), k1_tarski(H_124)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_236])).
% 2.16/1.29  tff(c_249, plain, (![A_127, B_128, C_129, H_130]: (k2_xboole_0(k1_enumset1(A_127, B_128, C_129), k1_tarski(H_130))=k2_enumset1(A_127, B_128, C_129, H_130))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_245])).
% 2.16/1.29  tff(c_258, plain, (![A_19, B_20, H_130]: (k2_xboole_0(k2_tarski(A_19, B_20), k1_tarski(H_130))=k2_enumset1(A_19, A_19, B_20, H_130))), inference(superposition, [status(thm), theory('equality')], [c_22, c_249])).
% 2.16/1.29  tff(c_262, plain, (![A_131, B_132, H_133]: (k2_xboole_0(k2_tarski(A_131, B_132), k1_tarski(H_133))=k1_enumset1(A_131, B_132, H_133))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_258])).
% 2.16/1.29  tff(c_271, plain, (![A_18, H_133]: (k2_xboole_0(k1_tarski(A_18), k1_tarski(H_133))=k1_enumset1(A_18, A_18, H_133))), inference(superposition, [status(thm), theory('equality')], [c_20, c_262])).
% 2.16/1.29  tff(c_274, plain, (![A_18, H_133]: (k2_xboole_0(k1_tarski(A_18), k1_tarski(H_133))=k2_tarski(A_18, H_133))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_271])).
% 2.16/1.29  tff(c_94, plain, (![A_63, B_64]: (k4_xboole_0(k1_tarski(A_63), B_64)=k1_tarski(A_63) | r2_hidden(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.16/1.29  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k4_xboole_0(B_4, A_3))=k2_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.16/1.29  tff(c_120, plain, (![B_71, A_72]: (k5_xboole_0(B_71, k1_tarski(A_72))=k2_xboole_0(B_71, k1_tarski(A_72)) | r2_hidden(A_72, B_71))), inference(superposition, [status(thm), theory('equality')], [c_94, c_4])).
% 2.16/1.29  tff(c_38, plain, (k5_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))!=k2_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.16/1.29  tff(c_126, plain, (k2_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))!=k2_tarski('#skF_3', '#skF_4') | r2_hidden('#skF_4', k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_120, c_38])).
% 2.16/1.29  tff(c_139, plain, (k2_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))!=k2_tarski('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_126])).
% 2.16/1.29  tff(c_277, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_274, c_139])).
% 2.16/1.29  tff(c_278, plain, (r2_hidden('#skF_4', k1_tarski('#skF_3'))), inference(splitRight, [status(thm)], [c_126])).
% 2.16/1.29  tff(c_6, plain, (![C_9, A_5]: (C_9=A_5 | ~r2_hidden(C_9, k1_tarski(A_5)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.16/1.29  tff(c_282, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_278, c_6])).
% 2.16/1.29  tff(c_286, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_282])).
% 2.16/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.29  
% 2.16/1.29  Inference rules
% 2.16/1.29  ----------------------
% 2.16/1.29  #Ref     : 0
% 2.16/1.29  #Sup     : 52
% 2.16/1.29  #Fact    : 0
% 2.16/1.29  #Define  : 0
% 2.16/1.29  #Split   : 1
% 2.16/1.29  #Chain   : 0
% 2.16/1.29  #Close   : 0
% 2.16/1.29  
% 2.16/1.29  Ordering : KBO
% 2.16/1.29  
% 2.16/1.29  Simplification rules
% 2.16/1.29  ----------------------
% 2.16/1.29  #Subsume      : 0
% 2.16/1.29  #Demod        : 9
% 2.16/1.29  #Tautology    : 41
% 2.16/1.29  #SimpNegUnit  : 1
% 2.16/1.29  #BackRed      : 1
% 2.16/1.29  
% 2.16/1.29  #Partial instantiations: 0
% 2.16/1.29  #Strategies tried      : 1
% 2.16/1.29  
% 2.16/1.29  Timing (in seconds)
% 2.16/1.29  ----------------------
% 2.16/1.29  Preprocessing        : 0.32
% 2.16/1.29  Parsing              : 0.17
% 2.16/1.29  CNF conversion       : 0.02
% 2.16/1.29  Main loop            : 0.20
% 2.16/1.29  Inferencing          : 0.08
% 2.16/1.29  Reduction            : 0.06
% 2.16/1.29  Demodulation         : 0.04
% 2.16/1.29  BG Simplification    : 0.02
% 2.16/1.29  Subsumption          : 0.03
% 2.16/1.29  Abstraction          : 0.01
% 2.16/1.29  MUC search           : 0.00
% 2.16/1.29  Cooper               : 0.00
% 2.16/1.29  Total                : 0.55
% 2.16/1.29  Index Insertion      : 0.00
% 2.16/1.29  Index Deletion       : 0.00
% 2.16/1.29  Index Matching       : 0.00
% 2.16/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
