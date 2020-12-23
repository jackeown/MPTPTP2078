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
% DateTime   : Thu Dec  3 10:09:30 EST 2020

% Result     : Theorem 3.26s
% Output     : CNFRefutation 3.29s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 128 expanded)
%              Number of leaves         :   34 (  58 expanded)
%              Depth                    :   11
%              Number of atoms          :   42 ( 110 expanded)
%              Number of equality atoms :   41 ( 109 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k3_enumset1 > k4_mcart_1 > k2_enumset1 > k3_zfmisc_1 > k3_mcart_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k4_mcart_1,type,(
    k4_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(f_49,axiom,(
    ! [A,B,C,D] : k4_mcart_1(A,B,C,D) = k4_tarski(k3_mcart_1(A,B,C),D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_mcart_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_51,axiom,(
    ! [A,B,C,D] : k4_mcart_1(A,B,C,D) = k4_tarski(k4_tarski(k4_tarski(A,B),C),D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_mcart_1)).

tff(f_29,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_35,axiom,(
    ! [A] : k2_enumset1(A,A,A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_enumset1(E,F,G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l68_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E] : k6_enumset1(A,A,A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_enumset1)).

tff(f_37,axiom,(
    ! [A,B] : k3_enumset1(A,A,A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k1_tarski(A),k2_tarski(B,C)) = k2_tarski(k4_tarski(A,B),k4_tarski(A,C))
      & k2_zfmisc_1(k2_tarski(A,B),k1_tarski(C)) = k2_tarski(k4_tarski(A,C),k4_tarski(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C] : k3_zfmisc_1(k1_tarski(A),k1_tarski(B),k1_tarski(C)) = k1_tarski(k3_mcart_1(A,B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_mcart_1)).

tff(c_119,plain,(
    ! [A_65,B_66,C_67,D_68] : k4_tarski(k3_mcart_1(A_65,B_66,C_67),D_68) = k4_mcart_1(A_65,B_66,C_67,D_68) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_28,plain,(
    ! [A_46,B_47] : k1_mcart_1(k4_tarski(A_46,B_47)) = A_46 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_125,plain,(
    ! [A_65,B_66,C_67,D_68] : k1_mcart_1(k4_mcart_1(A_65,B_66,C_67,D_68)) = k3_mcart_1(A_65,B_66,C_67) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_28])).

tff(c_152,plain,(
    ! [A_77,B_78,C_79,D_80] : k4_tarski(k4_tarski(k4_tarski(A_77,B_78),C_79),D_80) = k4_mcart_1(A_77,B_78,C_79,D_80) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_164,plain,(
    ! [A_77,B_78,C_79,D_80] : k4_tarski(k4_tarski(A_77,B_78),C_79) = k1_mcart_1(k4_mcart_1(A_77,B_78,C_79,D_80)) ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_28])).

tff(c_181,plain,(
    ! [A_77,B_78,C_79] : k4_tarski(k4_tarski(A_77,B_78),C_79) = k3_mcart_1(A_77,B_78,C_79) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_164])).

tff(c_4,plain,(
    ! [A_8,B_9,C_10,D_11] : k2_xboole_0(k1_tarski(A_8),k1_enumset1(B_9,C_10,D_11)) = k2_enumset1(A_8,B_9,C_10,D_11) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_10,plain,(
    ! [A_22] : k2_enumset1(A_22,A_22,A_22,A_22) = k1_tarski(A_22) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_699,plain,(
    ! [E_149,D_150,G_148,C_152,A_153,B_151,F_147] : k2_xboole_0(k2_enumset1(A_153,B_151,C_152,D_150),k1_enumset1(E_149,F_147,G_148)) = k5_enumset1(A_153,B_151,C_152,D_150,E_149,F_147,G_148) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_714,plain,(
    ! [A_22,E_149,F_147,G_148] : k5_enumset1(A_22,A_22,A_22,A_22,E_149,F_147,G_148) = k2_xboole_0(k1_tarski(A_22),k1_enumset1(E_149,F_147,G_148)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_699])).

tff(c_718,plain,(
    ! [A_154,E_155,F_156,G_157] : k5_enumset1(A_154,A_154,A_154,A_154,E_155,F_156,G_157) = k2_enumset1(A_154,E_155,F_156,G_157) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_714])).

tff(c_673,plain,(
    ! [E_138,B_136,C_141,A_137,G_135,F_140,D_139] : k6_enumset1(A_137,A_137,B_136,C_141,D_139,E_138,F_140,G_135) = k5_enumset1(A_137,B_136,C_141,D_139,E_138,F_140,G_135) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14,plain,(
    ! [A_25,E_29,C_27,D_28,B_26] : k6_enumset1(A_25,A_25,A_25,A_25,B_26,C_27,D_28,E_29) = k3_enumset1(A_25,B_26,C_27,D_28,E_29) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_680,plain,(
    ! [E_138,C_141,G_135,F_140,D_139] : k5_enumset1(C_141,C_141,C_141,D_139,E_138,F_140,G_135) = k3_enumset1(C_141,D_139,E_138,F_140,G_135) ),
    inference(superposition,[status(thm),theory(equality)],[c_673,c_14])).

tff(c_734,plain,(
    ! [A_158,E_159,F_160,G_161] : k3_enumset1(A_158,A_158,E_159,F_160,G_161) = k2_enumset1(A_158,E_159,F_160,G_161) ),
    inference(superposition,[status(thm),theory(equality)],[c_718,c_680])).

tff(c_12,plain,(
    ! [A_23,B_24] : k3_enumset1(A_23,A_23,A_23,A_23,B_24) = k2_tarski(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_757,plain,(
    ! [F_162,G_163] : k2_enumset1(F_162,F_162,F_162,G_163) = k2_tarski(F_162,G_163) ),
    inference(superposition,[status(thm),theory(equality)],[c_734,c_12])).

tff(c_770,plain,(
    ! [G_163] : k2_tarski(G_163,G_163) = k1_tarski(G_163) ),
    inference(superposition,[status(thm),theory(equality)],[c_757,c_10])).

tff(c_786,plain,(
    ! [G_164] : k2_tarski(G_164,G_164) = k1_tarski(G_164) ),
    inference(superposition,[status(thm),theory(equality)],[c_757,c_10])).

tff(c_18,plain,(
    ! [A_30,B_31,C_32] : k2_zfmisc_1(k2_tarski(A_30,B_31),k1_tarski(C_32)) = k2_tarski(k4_tarski(A_30,C_32),k4_tarski(B_31,C_32)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_808,plain,(
    ! [G_164,C_32] : k2_zfmisc_1(k1_tarski(G_164),k1_tarski(C_32)) = k2_tarski(k4_tarski(G_164,C_32),k4_tarski(G_164,C_32)) ),
    inference(superposition,[status(thm),theory(equality)],[c_786,c_18])).

tff(c_830,plain,(
    ! [G_164,C_32] : k2_zfmisc_1(k1_tarski(G_164),k1_tarski(C_32)) = k1_tarski(k4_tarski(G_164,C_32)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_770,c_808])).

tff(c_1197,plain,(
    ! [G_184,C_185] : k2_zfmisc_1(k1_tarski(G_184),k1_tarski(C_185)) = k1_tarski(k4_tarski(G_184,C_185)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_770,c_808])).

tff(c_22,plain,(
    ! [A_35,B_36,C_37] : k2_zfmisc_1(k2_zfmisc_1(A_35,B_36),C_37) = k3_zfmisc_1(A_35,B_36,C_37) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1206,plain,(
    ! [G_184,C_185,C_37] : k3_zfmisc_1(k1_tarski(G_184),k1_tarski(C_185),C_37) = k2_zfmisc_1(k1_tarski(k4_tarski(G_184,C_185)),C_37) ),
    inference(superposition,[status(thm),theory(equality)],[c_1197,c_22])).

tff(c_32,plain,(
    k3_zfmisc_1(k1_tarski('#skF_1'),k1_tarski('#skF_2'),k1_tarski('#skF_3')) != k1_tarski(k3_mcart_1('#skF_1','#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1299,plain,(
    k2_zfmisc_1(k1_tarski(k4_tarski('#skF_1','#skF_2')),k1_tarski('#skF_3')) != k1_tarski(k3_mcart_1('#skF_1','#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1206,c_32])).

tff(c_1302,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_830,c_1299])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:40:16 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.26/1.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.26/1.47  
% 3.26/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.29/1.47  %$ k6_enumset1 > k5_enumset1 > k3_enumset1 > k4_mcart_1 > k2_enumset1 > k3_zfmisc_1 > k3_mcart_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_2 > #skF_3 > #skF_1
% 3.29/1.47  
% 3.29/1.47  %Foreground sorts:
% 3.29/1.47  
% 3.29/1.47  
% 3.29/1.47  %Background operators:
% 3.29/1.47  
% 3.29/1.47  
% 3.29/1.47  %Foreground operators:
% 3.29/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.29/1.47  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.29/1.47  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.29/1.47  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 3.29/1.47  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.29/1.47  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.29/1.47  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.29/1.47  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.29/1.47  tff('#skF_2', type, '#skF_2': $i).
% 3.29/1.47  tff('#skF_3', type, '#skF_3': $i).
% 3.29/1.47  tff('#skF_1', type, '#skF_1': $i).
% 3.29/1.47  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 3.29/1.47  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.29/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.29/1.47  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 3.29/1.47  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.29/1.47  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.29/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.29/1.47  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 3.29/1.47  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.29/1.47  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.29/1.47  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 3.29/1.47  
% 3.29/1.48  tff(f_49, axiom, (![A, B, C, D]: (k4_mcart_1(A, B, C, D) = k4_tarski(k3_mcart_1(A, B, C), D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_mcart_1)).
% 3.29/1.48  tff(f_55, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 3.29/1.48  tff(f_51, axiom, (![A, B, C, D]: (k4_mcart_1(A, B, C, D) = k4_tarski(k4_tarski(k4_tarski(A, B), C), D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_mcart_1)).
% 3.29/1.48  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_enumset1)).
% 3.29/1.48  tff(f_35, axiom, (![A]: (k2_enumset1(A, A, A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t82_enumset1)).
% 3.29/1.48  tff(f_27, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_enumset1(E, F, G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l68_enumset1)).
% 3.29/1.48  tff(f_31, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 3.29/1.48  tff(f_39, axiom, (![A, B, C, D, E]: (k6_enumset1(A, A, A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_enumset1)).
% 3.29/1.48  tff(f_37, axiom, (![A, B]: (k3_enumset1(A, A, A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_enumset1)).
% 3.29/1.48  tff(f_43, axiom, (![A, B, C]: ((k2_zfmisc_1(k1_tarski(A), k2_tarski(B, C)) = k2_tarski(k4_tarski(A, B), k4_tarski(A, C))) & (k2_zfmisc_1(k2_tarski(A, B), k1_tarski(C)) = k2_tarski(k4_tarski(A, C), k4_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_zfmisc_1)).
% 3.29/1.48  tff(f_47, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 3.29/1.48  tff(f_58, negated_conjecture, ~(![A, B, C]: (k3_zfmisc_1(k1_tarski(A), k1_tarski(B), k1_tarski(C)) = k1_tarski(k3_mcart_1(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_mcart_1)).
% 3.29/1.48  tff(c_119, plain, (![A_65, B_66, C_67, D_68]: (k4_tarski(k3_mcart_1(A_65, B_66, C_67), D_68)=k4_mcart_1(A_65, B_66, C_67, D_68))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.29/1.48  tff(c_28, plain, (![A_46, B_47]: (k1_mcart_1(k4_tarski(A_46, B_47))=A_46)), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.29/1.48  tff(c_125, plain, (![A_65, B_66, C_67, D_68]: (k1_mcart_1(k4_mcart_1(A_65, B_66, C_67, D_68))=k3_mcart_1(A_65, B_66, C_67))), inference(superposition, [status(thm), theory('equality')], [c_119, c_28])).
% 3.29/1.48  tff(c_152, plain, (![A_77, B_78, C_79, D_80]: (k4_tarski(k4_tarski(k4_tarski(A_77, B_78), C_79), D_80)=k4_mcart_1(A_77, B_78, C_79, D_80))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.29/1.48  tff(c_164, plain, (![A_77, B_78, C_79, D_80]: (k4_tarski(k4_tarski(A_77, B_78), C_79)=k1_mcart_1(k4_mcart_1(A_77, B_78, C_79, D_80)))), inference(superposition, [status(thm), theory('equality')], [c_152, c_28])).
% 3.29/1.48  tff(c_181, plain, (![A_77, B_78, C_79]: (k4_tarski(k4_tarski(A_77, B_78), C_79)=k3_mcart_1(A_77, B_78, C_79))), inference(demodulation, [status(thm), theory('equality')], [c_125, c_164])).
% 3.29/1.48  tff(c_4, plain, (![A_8, B_9, C_10, D_11]: (k2_xboole_0(k1_tarski(A_8), k1_enumset1(B_9, C_10, D_11))=k2_enumset1(A_8, B_9, C_10, D_11))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.29/1.48  tff(c_10, plain, (![A_22]: (k2_enumset1(A_22, A_22, A_22, A_22)=k1_tarski(A_22))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.29/1.48  tff(c_699, plain, (![E_149, D_150, G_148, C_152, A_153, B_151, F_147]: (k2_xboole_0(k2_enumset1(A_153, B_151, C_152, D_150), k1_enumset1(E_149, F_147, G_148))=k5_enumset1(A_153, B_151, C_152, D_150, E_149, F_147, G_148))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.29/1.48  tff(c_714, plain, (![A_22, E_149, F_147, G_148]: (k5_enumset1(A_22, A_22, A_22, A_22, E_149, F_147, G_148)=k2_xboole_0(k1_tarski(A_22), k1_enumset1(E_149, F_147, G_148)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_699])).
% 3.29/1.48  tff(c_718, plain, (![A_154, E_155, F_156, G_157]: (k5_enumset1(A_154, A_154, A_154, A_154, E_155, F_156, G_157)=k2_enumset1(A_154, E_155, F_156, G_157))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_714])).
% 3.29/1.48  tff(c_673, plain, (![E_138, B_136, C_141, A_137, G_135, F_140, D_139]: (k6_enumset1(A_137, A_137, B_136, C_141, D_139, E_138, F_140, G_135)=k5_enumset1(A_137, B_136, C_141, D_139, E_138, F_140, G_135))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.29/1.48  tff(c_14, plain, (![A_25, E_29, C_27, D_28, B_26]: (k6_enumset1(A_25, A_25, A_25, A_25, B_26, C_27, D_28, E_29)=k3_enumset1(A_25, B_26, C_27, D_28, E_29))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.29/1.48  tff(c_680, plain, (![E_138, C_141, G_135, F_140, D_139]: (k5_enumset1(C_141, C_141, C_141, D_139, E_138, F_140, G_135)=k3_enumset1(C_141, D_139, E_138, F_140, G_135))), inference(superposition, [status(thm), theory('equality')], [c_673, c_14])).
% 3.29/1.48  tff(c_734, plain, (![A_158, E_159, F_160, G_161]: (k3_enumset1(A_158, A_158, E_159, F_160, G_161)=k2_enumset1(A_158, E_159, F_160, G_161))), inference(superposition, [status(thm), theory('equality')], [c_718, c_680])).
% 3.29/1.48  tff(c_12, plain, (![A_23, B_24]: (k3_enumset1(A_23, A_23, A_23, A_23, B_24)=k2_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.29/1.48  tff(c_757, plain, (![F_162, G_163]: (k2_enumset1(F_162, F_162, F_162, G_163)=k2_tarski(F_162, G_163))), inference(superposition, [status(thm), theory('equality')], [c_734, c_12])).
% 3.29/1.48  tff(c_770, plain, (![G_163]: (k2_tarski(G_163, G_163)=k1_tarski(G_163))), inference(superposition, [status(thm), theory('equality')], [c_757, c_10])).
% 3.29/1.48  tff(c_786, plain, (![G_164]: (k2_tarski(G_164, G_164)=k1_tarski(G_164))), inference(superposition, [status(thm), theory('equality')], [c_757, c_10])).
% 3.29/1.48  tff(c_18, plain, (![A_30, B_31, C_32]: (k2_zfmisc_1(k2_tarski(A_30, B_31), k1_tarski(C_32))=k2_tarski(k4_tarski(A_30, C_32), k4_tarski(B_31, C_32)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.29/1.48  tff(c_808, plain, (![G_164, C_32]: (k2_zfmisc_1(k1_tarski(G_164), k1_tarski(C_32))=k2_tarski(k4_tarski(G_164, C_32), k4_tarski(G_164, C_32)))), inference(superposition, [status(thm), theory('equality')], [c_786, c_18])).
% 3.29/1.48  tff(c_830, plain, (![G_164, C_32]: (k2_zfmisc_1(k1_tarski(G_164), k1_tarski(C_32))=k1_tarski(k4_tarski(G_164, C_32)))), inference(demodulation, [status(thm), theory('equality')], [c_770, c_808])).
% 3.29/1.48  tff(c_1197, plain, (![G_184, C_185]: (k2_zfmisc_1(k1_tarski(G_184), k1_tarski(C_185))=k1_tarski(k4_tarski(G_184, C_185)))), inference(demodulation, [status(thm), theory('equality')], [c_770, c_808])).
% 3.29/1.48  tff(c_22, plain, (![A_35, B_36, C_37]: (k2_zfmisc_1(k2_zfmisc_1(A_35, B_36), C_37)=k3_zfmisc_1(A_35, B_36, C_37))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.29/1.48  tff(c_1206, plain, (![G_184, C_185, C_37]: (k3_zfmisc_1(k1_tarski(G_184), k1_tarski(C_185), C_37)=k2_zfmisc_1(k1_tarski(k4_tarski(G_184, C_185)), C_37))), inference(superposition, [status(thm), theory('equality')], [c_1197, c_22])).
% 3.29/1.48  tff(c_32, plain, (k3_zfmisc_1(k1_tarski('#skF_1'), k1_tarski('#skF_2'), k1_tarski('#skF_3'))!=k1_tarski(k3_mcart_1('#skF_1', '#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.29/1.48  tff(c_1299, plain, (k2_zfmisc_1(k1_tarski(k4_tarski('#skF_1', '#skF_2')), k1_tarski('#skF_3'))!=k1_tarski(k3_mcart_1('#skF_1', '#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1206, c_32])).
% 3.29/1.48  tff(c_1302, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_181, c_830, c_1299])).
% 3.29/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.29/1.48  
% 3.29/1.48  Inference rules
% 3.29/1.48  ----------------------
% 3.29/1.48  #Ref     : 0
% 3.29/1.48  #Sup     : 312
% 3.29/1.48  #Fact    : 0
% 3.29/1.48  #Define  : 0
% 3.29/1.48  #Split   : 0
% 3.29/1.48  #Chain   : 0
% 3.29/1.48  #Close   : 0
% 3.29/1.48  
% 3.29/1.48  Ordering : KBO
% 3.29/1.48  
% 3.29/1.48  Simplification rules
% 3.29/1.48  ----------------------
% 3.29/1.48  #Subsume      : 8
% 3.29/1.48  #Demod        : 163
% 3.29/1.48  #Tautology    : 169
% 3.29/1.48  #SimpNegUnit  : 0
% 3.29/1.48  #BackRed      : 3
% 3.29/1.48  
% 3.29/1.48  #Partial instantiations: 0
% 3.29/1.48  #Strategies tried      : 1
% 3.29/1.48  
% 3.29/1.48  Timing (in seconds)
% 3.29/1.48  ----------------------
% 3.29/1.49  Preprocessing        : 0.30
% 3.29/1.49  Parsing              : 0.16
% 3.29/1.49  CNF conversion       : 0.02
% 3.29/1.49  Main loop            : 0.42
% 3.29/1.49  Inferencing          : 0.17
% 3.29/1.49  Reduction            : 0.15
% 3.29/1.49  Demodulation         : 0.12
% 3.29/1.49  BG Simplification    : 0.03
% 3.29/1.49  Subsumption          : 0.05
% 3.29/1.49  Abstraction          : 0.04
% 3.29/1.49  MUC search           : 0.00
% 3.29/1.49  Cooper               : 0.00
% 3.29/1.49  Total                : 0.75
% 3.29/1.49  Index Insertion      : 0.00
% 3.29/1.49  Index Deletion       : 0.00
% 3.29/1.49  Index Matching       : 0.00
% 3.29/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
