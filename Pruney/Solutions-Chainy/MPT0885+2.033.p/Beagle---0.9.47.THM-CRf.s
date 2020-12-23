%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:39 EST 2020

% Result     : Theorem 22.13s
% Output     : CNFRefutation 22.13s
% Verified   : 
% Statistics : Number of formulae       :   33 (  38 expanded)
%              Number of leaves         :   21 (  24 expanded)
%              Depth                    :    6
%              Number of atoms          :   18 (  23 expanded)
%              Number of equality atoms :   17 (  22 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k2_enumset1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_39,axiom,(
    ! [A,B,C,D] : k3_zfmisc_1(k1_tarski(A),k2_tarski(B,C),k1_tarski(D)) = k2_tarski(k3_mcart_1(A,B,D),k3_mcart_1(A,C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_mcart_1)).

tff(f_37,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k2_tarski(A,B),C) = k2_xboole_0(k2_zfmisc_1(k1_tarski(A),C),k2_zfmisc_1(k1_tarski(B),C))
      & k2_zfmisc_1(C,k2_tarski(A,B)) = k2_xboole_0(k2_zfmisc_1(C,k1_tarski(A)),k2_zfmisc_1(C,k1_tarski(B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_enumset1)).

tff(f_42,negated_conjecture,(
    ~ ! [A,B,C,D,E] : k3_zfmisc_1(k1_tarski(A),k2_tarski(B,C),k2_tarski(D,E)) = k2_enumset1(k3_mcart_1(A,B,D),k3_mcart_1(A,C,D),k3_mcart_1(A,B,E),k3_mcart_1(A,C,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_mcart_1)).

tff(c_14,plain,(
    ! [A_16,B_17,C_18,D_19] : k3_zfmisc_1(k1_tarski(A_16),k2_tarski(B_17,C_18),k1_tarski(D_19)) = k2_tarski(k3_mcart_1(A_16,B_17,D_19),k3_mcart_1(A_16,C_18,D_19)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_12,plain,(
    ! [A_13,B_14,C_15] : k2_zfmisc_1(k2_zfmisc_1(A_13,B_14),C_15) = k3_zfmisc_1(A_13,B_14,C_15) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_78,plain,(
    ! [C_36,A_37,B_38] : k2_xboole_0(k2_zfmisc_1(C_36,k1_tarski(A_37)),k2_zfmisc_1(C_36,k1_tarski(B_38))) = k2_zfmisc_1(C_36,k2_tarski(A_37,B_38)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_88,plain,(
    ! [A_13,B_14,A_37,B_38] : k2_xboole_0(k3_zfmisc_1(A_13,B_14,k1_tarski(A_37)),k2_zfmisc_1(k2_zfmisc_1(A_13,B_14),k1_tarski(B_38))) = k2_zfmisc_1(k2_zfmisc_1(A_13,B_14),k2_tarski(A_37,B_38)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_78])).

tff(c_378,plain,(
    ! [A_61,B_62,A_63,B_64] : k2_xboole_0(k3_zfmisc_1(A_61,B_62,k1_tarski(A_63)),k3_zfmisc_1(A_61,B_62,k1_tarski(B_64))) = k3_zfmisc_1(A_61,B_62,k2_tarski(A_63,B_64)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_12,c_88])).

tff(c_5578,plain,(
    ! [B_215,A_217,B_216,D_218,C_219] : k2_xboole_0(k2_tarski(k3_mcart_1(A_217,B_215,D_218),k3_mcart_1(A_217,C_219,D_218)),k3_zfmisc_1(k1_tarski(A_217),k2_tarski(B_215,C_219),k1_tarski(B_216))) = k3_zfmisc_1(k1_tarski(A_217),k2_tarski(B_215,C_219),k2_tarski(D_218,B_216)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_378])).

tff(c_240,plain,(
    ! [A_54,B_55,C_56,D_57] : k3_zfmisc_1(k1_tarski(A_54),k2_tarski(B_55,C_56),k1_tarski(D_57)) = k2_tarski(k3_mcart_1(A_54,B_55,D_57),k3_mcart_1(A_54,C_56,D_57)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4,plain,(
    ! [A_3,B_4,C_5,D_6] : k2_xboole_0(k2_tarski(A_3,B_4),k2_tarski(C_5,D_6)) = k2_enumset1(A_3,B_4,C_5,D_6) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_287,plain,(
    ! [A_3,C_56,D_57,B_55,B_4,A_54] : k2_xboole_0(k2_tarski(A_3,B_4),k3_zfmisc_1(k1_tarski(A_54),k2_tarski(B_55,C_56),k1_tarski(D_57))) = k2_enumset1(A_3,B_4,k3_mcart_1(A_54,B_55,D_57),k3_mcart_1(A_54,C_56,D_57)) ),
    inference(superposition,[status(thm),theory(equality)],[c_240,c_4])).

tff(c_5584,plain,(
    ! [B_215,A_217,B_216,D_218,C_219] : k2_enumset1(k3_mcart_1(A_217,B_215,D_218),k3_mcart_1(A_217,C_219,D_218),k3_mcart_1(A_217,B_215,B_216),k3_mcart_1(A_217,C_219,B_216)) = k3_zfmisc_1(k1_tarski(A_217),k2_tarski(B_215,C_219),k2_tarski(D_218,B_216)) ),
    inference(superposition,[status(thm),theory(equality)],[c_5578,c_287])).

tff(c_16,plain,(
    k2_enumset1(k3_mcart_1('#skF_1','#skF_2','#skF_4'),k3_mcart_1('#skF_1','#skF_3','#skF_4'),k3_mcart_1('#skF_1','#skF_2','#skF_5'),k3_mcart_1('#skF_1','#skF_3','#skF_5')) != k3_zfmisc_1(k1_tarski('#skF_1'),k2_tarski('#skF_2','#skF_3'),k2_tarski('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_29835,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5584,c_16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:38:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 22.13/12.72  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 22.13/12.72  
% 22.13/12.72  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 22.13/12.72  %$ k2_enumset1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 22.13/12.72  
% 22.13/12.72  %Foreground sorts:
% 22.13/12.72  
% 22.13/12.72  
% 22.13/12.72  %Background operators:
% 22.13/12.72  
% 22.13/12.72  
% 22.13/12.72  %Foreground operators:
% 22.13/12.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 22.13/12.72  tff(k1_tarski, type, k1_tarski: $i > $i).
% 22.13/12.72  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 22.13/12.72  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 22.13/12.72  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 22.13/12.72  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 22.13/12.72  tff('#skF_5', type, '#skF_5': $i).
% 22.13/12.72  tff('#skF_2', type, '#skF_2': $i).
% 22.13/12.72  tff('#skF_3', type, '#skF_3': $i).
% 22.13/12.72  tff('#skF_1', type, '#skF_1': $i).
% 22.13/12.72  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 22.13/12.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 22.13/12.72  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 22.13/12.72  tff('#skF_4', type, '#skF_4': $i).
% 22.13/12.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 22.13/12.72  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 22.13/12.72  
% 22.13/12.73  tff(f_39, axiom, (![A, B, C, D]: (k3_zfmisc_1(k1_tarski(A), k2_tarski(B, C), k1_tarski(D)) = k2_tarski(k3_mcart_1(A, B, D), k3_mcart_1(A, C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_mcart_1)).
% 22.13/12.73  tff(f_37, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 22.13/12.73  tff(f_33, axiom, (![A, B, C]: ((k2_zfmisc_1(k2_tarski(A, B), C) = k2_xboole_0(k2_zfmisc_1(k1_tarski(A), C), k2_zfmisc_1(k1_tarski(B), C))) & (k2_zfmisc_1(C, k2_tarski(A, B)) = k2_xboole_0(k2_zfmisc_1(C, k1_tarski(A)), k2_zfmisc_1(C, k1_tarski(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t132_zfmisc_1)).
% 22.13/12.73  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_enumset1)).
% 22.13/12.73  tff(f_42, negated_conjecture, ~(![A, B, C, D, E]: (k3_zfmisc_1(k1_tarski(A), k2_tarski(B, C), k2_tarski(D, E)) = k2_enumset1(k3_mcart_1(A, B, D), k3_mcart_1(A, C, D), k3_mcart_1(A, B, E), k3_mcart_1(A, C, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_mcart_1)).
% 22.13/12.73  tff(c_14, plain, (![A_16, B_17, C_18, D_19]: (k3_zfmisc_1(k1_tarski(A_16), k2_tarski(B_17, C_18), k1_tarski(D_19))=k2_tarski(k3_mcart_1(A_16, B_17, D_19), k3_mcart_1(A_16, C_18, D_19)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 22.13/12.73  tff(c_12, plain, (![A_13, B_14, C_15]: (k2_zfmisc_1(k2_zfmisc_1(A_13, B_14), C_15)=k3_zfmisc_1(A_13, B_14, C_15))), inference(cnfTransformation, [status(thm)], [f_37])).
% 22.13/12.73  tff(c_78, plain, (![C_36, A_37, B_38]: (k2_xboole_0(k2_zfmisc_1(C_36, k1_tarski(A_37)), k2_zfmisc_1(C_36, k1_tarski(B_38)))=k2_zfmisc_1(C_36, k2_tarski(A_37, B_38)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 22.13/12.73  tff(c_88, plain, (![A_13, B_14, A_37, B_38]: (k2_xboole_0(k3_zfmisc_1(A_13, B_14, k1_tarski(A_37)), k2_zfmisc_1(k2_zfmisc_1(A_13, B_14), k1_tarski(B_38)))=k2_zfmisc_1(k2_zfmisc_1(A_13, B_14), k2_tarski(A_37, B_38)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_78])).
% 22.13/12.73  tff(c_378, plain, (![A_61, B_62, A_63, B_64]: (k2_xboole_0(k3_zfmisc_1(A_61, B_62, k1_tarski(A_63)), k3_zfmisc_1(A_61, B_62, k1_tarski(B_64)))=k3_zfmisc_1(A_61, B_62, k2_tarski(A_63, B_64)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_12, c_88])).
% 22.13/12.73  tff(c_5578, plain, (![B_215, A_217, B_216, D_218, C_219]: (k2_xboole_0(k2_tarski(k3_mcart_1(A_217, B_215, D_218), k3_mcart_1(A_217, C_219, D_218)), k3_zfmisc_1(k1_tarski(A_217), k2_tarski(B_215, C_219), k1_tarski(B_216)))=k3_zfmisc_1(k1_tarski(A_217), k2_tarski(B_215, C_219), k2_tarski(D_218, B_216)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_378])).
% 22.13/12.73  tff(c_240, plain, (![A_54, B_55, C_56, D_57]: (k3_zfmisc_1(k1_tarski(A_54), k2_tarski(B_55, C_56), k1_tarski(D_57))=k2_tarski(k3_mcart_1(A_54, B_55, D_57), k3_mcart_1(A_54, C_56, D_57)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 22.13/12.73  tff(c_4, plain, (![A_3, B_4, C_5, D_6]: (k2_xboole_0(k2_tarski(A_3, B_4), k2_tarski(C_5, D_6))=k2_enumset1(A_3, B_4, C_5, D_6))), inference(cnfTransformation, [status(thm)], [f_29])).
% 22.13/12.73  tff(c_287, plain, (![A_3, C_56, D_57, B_55, B_4, A_54]: (k2_xboole_0(k2_tarski(A_3, B_4), k3_zfmisc_1(k1_tarski(A_54), k2_tarski(B_55, C_56), k1_tarski(D_57)))=k2_enumset1(A_3, B_4, k3_mcart_1(A_54, B_55, D_57), k3_mcart_1(A_54, C_56, D_57)))), inference(superposition, [status(thm), theory('equality')], [c_240, c_4])).
% 22.13/12.73  tff(c_5584, plain, (![B_215, A_217, B_216, D_218, C_219]: (k2_enumset1(k3_mcart_1(A_217, B_215, D_218), k3_mcart_1(A_217, C_219, D_218), k3_mcart_1(A_217, B_215, B_216), k3_mcart_1(A_217, C_219, B_216))=k3_zfmisc_1(k1_tarski(A_217), k2_tarski(B_215, C_219), k2_tarski(D_218, B_216)))), inference(superposition, [status(thm), theory('equality')], [c_5578, c_287])).
% 22.13/12.73  tff(c_16, plain, (k2_enumset1(k3_mcart_1('#skF_1', '#skF_2', '#skF_4'), k3_mcart_1('#skF_1', '#skF_3', '#skF_4'), k3_mcart_1('#skF_1', '#skF_2', '#skF_5'), k3_mcart_1('#skF_1', '#skF_3', '#skF_5'))!=k3_zfmisc_1(k1_tarski('#skF_1'), k2_tarski('#skF_2', '#skF_3'), k2_tarski('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_42])).
% 22.13/12.73  tff(c_29835, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5584, c_16])).
% 22.13/12.73  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 22.13/12.73  
% 22.13/12.73  Inference rules
% 22.13/12.73  ----------------------
% 22.13/12.73  #Ref     : 0
% 22.13/12.73  #Sup     : 7600
% 22.13/12.73  #Fact    : 0
% 22.13/12.73  #Define  : 0
% 22.13/12.73  #Split   : 0
% 22.13/12.73  #Chain   : 0
% 22.13/12.73  #Close   : 0
% 22.13/12.73  
% 22.13/12.73  Ordering : KBO
% 22.13/12.73  
% 22.13/12.73  Simplification rules
% 22.13/12.73  ----------------------
% 22.13/12.73  #Subsume      : 1172
% 22.13/12.73  #Demod        : 4313
% 22.13/12.73  #Tautology    : 931
% 22.13/12.73  #SimpNegUnit  : 0
% 22.13/12.73  #BackRed      : 1
% 22.13/12.73  
% 22.13/12.73  #Partial instantiations: 0
% 22.13/12.73  #Strategies tried      : 1
% 22.13/12.73  
% 22.13/12.73  Timing (in seconds)
% 22.13/12.73  ----------------------
% 22.13/12.73  Preprocessing        : 0.27
% 22.13/12.74  Parsing              : 0.15
% 22.13/12.74  CNF conversion       : 0.02
% 22.13/12.74  Main loop            : 11.67
% 22.13/12.74  Inferencing          : 2.89
% 22.13/12.74  Reduction            : 7.06
% 22.13/12.74  Demodulation         : 6.63
% 22.13/12.74  BG Simplification    : 0.48
% 22.13/12.74  Subsumption          : 0.99
% 22.13/12.74  Abstraction          : 0.86
% 22.13/12.74  MUC search           : 0.00
% 22.13/12.74  Cooper               : 0.00
% 22.13/12.74  Total                : 11.96
% 22.13/12.74  Index Insertion      : 0.00
% 22.13/12.74  Index Deletion       : 0.00
% 22.13/12.74  Index Matching       : 0.00
% 22.13/12.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
