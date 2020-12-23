%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:36 EST 2020

% Result     : Theorem 21.79s
% Output     : CNFRefutation 21.79s
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
    ! [A,B,C,D] : k3_zfmisc_1(k2_tarski(A,B),k1_tarski(C),k1_tarski(D)) = k2_tarski(k3_mcart_1(A,C,D),k3_mcart_1(B,C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_mcart_1)).

tff(f_29,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k2_tarski(A,B),C) = k2_xboole_0(k2_zfmisc_1(k1_tarski(A),C),k2_zfmisc_1(k1_tarski(B),C))
      & k2_zfmisc_1(C,k2_tarski(A,B)) = k2_xboole_0(k2_zfmisc_1(C,k1_tarski(A)),k2_zfmisc_1(C,k1_tarski(B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_zfmisc_1)).

tff(f_42,negated_conjecture,(
    ~ ! [A,B,C,D,E] : k3_zfmisc_1(k2_tarski(A,B),k1_tarski(C),k2_tarski(D,E)) = k2_enumset1(k3_mcart_1(A,C,D),k3_mcart_1(B,C,D),k3_mcart_1(A,C,E),k3_mcart_1(B,C,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_mcart_1)).

tff(c_240,plain,(
    ! [A_54,B_55,C_56,D_57] : k3_zfmisc_1(k2_tarski(A_54,B_55),k1_tarski(C_56),k1_tarski(D_57)) = k2_tarski(k3_mcart_1(A_54,C_56,D_57),k3_mcart_1(B_55,C_56,D_57)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4,plain,(
    ! [A_3,B_4,C_5,D_6] : k2_xboole_0(k2_tarski(A_3,B_4),k2_tarski(C_5,D_6)) = k2_enumset1(A_3,B_4,C_5,D_6) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_280,plain,(
    ! [C_56,D_6,C_5,D_57,B_55,A_54] : k2_xboole_0(k3_zfmisc_1(k2_tarski(A_54,B_55),k1_tarski(C_56),k1_tarski(D_57)),k2_tarski(C_5,D_6)) = k2_enumset1(k3_mcart_1(A_54,C_56,D_57),k3_mcart_1(B_55,C_56,D_57),C_5,D_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_240,c_4])).

tff(c_14,plain,(
    ! [A_16,B_17,C_18,D_19] : k3_zfmisc_1(k2_tarski(A_16,B_17),k1_tarski(C_18),k1_tarski(D_19)) = k2_tarski(k3_mcart_1(A_16,C_18,D_19),k3_mcart_1(B_17,C_18,D_19)) ),
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

tff(c_376,plain,(
    ! [A_61,B_62,A_63,B_64] : k2_xboole_0(k3_zfmisc_1(A_61,B_62,k1_tarski(A_63)),k3_zfmisc_1(A_61,B_62,k1_tarski(B_64))) = k3_zfmisc_1(A_61,B_62,k2_tarski(A_63,B_64)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_12,c_88])).

tff(c_6365,plain,(
    ! [A_258,D_260,C_261,A_259,B_257] : k2_xboole_0(k3_zfmisc_1(k2_tarski(A_258,B_257),k1_tarski(C_261),k1_tarski(A_259)),k2_tarski(k3_mcart_1(A_258,C_261,D_260),k3_mcart_1(B_257,C_261,D_260))) = k3_zfmisc_1(k2_tarski(A_258,B_257),k1_tarski(C_261),k2_tarski(A_259,D_260)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_376])).

tff(c_6423,plain,(
    ! [C_56,D_260,D_57,B_55,A_54] : k2_enumset1(k3_mcart_1(A_54,C_56,D_57),k3_mcart_1(B_55,C_56,D_57),k3_mcart_1(A_54,C_56,D_260),k3_mcart_1(B_55,C_56,D_260)) = k3_zfmisc_1(k2_tarski(A_54,B_55),k1_tarski(C_56),k2_tarski(D_57,D_260)) ),
    inference(superposition,[status(thm),theory(equality)],[c_280,c_6365])).

tff(c_16,plain,(
    k2_enumset1(k3_mcart_1('#skF_1','#skF_3','#skF_4'),k3_mcart_1('#skF_2','#skF_3','#skF_4'),k3_mcart_1('#skF_1','#skF_3','#skF_5'),k3_mcart_1('#skF_2','#skF_3','#skF_5')) != k3_zfmisc_1(k2_tarski('#skF_1','#skF_2'),k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_27931,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6423,c_16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:44:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 21.79/12.05  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 21.79/12.06  
% 21.79/12.06  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 21.79/12.06  %$ k2_enumset1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 21.79/12.06  
% 21.79/12.06  %Foreground sorts:
% 21.79/12.06  
% 21.79/12.06  
% 21.79/12.06  %Background operators:
% 21.79/12.06  
% 21.79/12.06  
% 21.79/12.06  %Foreground operators:
% 21.79/12.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 21.79/12.06  tff(k1_tarski, type, k1_tarski: $i > $i).
% 21.79/12.06  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 21.79/12.06  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 21.79/12.06  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 21.79/12.06  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 21.79/12.06  tff('#skF_5', type, '#skF_5': $i).
% 21.79/12.06  tff('#skF_2', type, '#skF_2': $i).
% 21.79/12.06  tff('#skF_3', type, '#skF_3': $i).
% 21.79/12.06  tff('#skF_1', type, '#skF_1': $i).
% 21.79/12.06  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 21.79/12.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 21.79/12.06  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 21.79/12.06  tff('#skF_4', type, '#skF_4': $i).
% 21.79/12.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 21.79/12.06  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 21.79/12.06  
% 21.79/12.07  tff(f_39, axiom, (![A, B, C, D]: (k3_zfmisc_1(k2_tarski(A, B), k1_tarski(C), k1_tarski(D)) = k2_tarski(k3_mcart_1(A, C, D), k3_mcart_1(B, C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_mcart_1)).
% 21.79/12.07  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_enumset1)).
% 21.79/12.07  tff(f_37, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 21.79/12.07  tff(f_33, axiom, (![A, B, C]: ((k2_zfmisc_1(k2_tarski(A, B), C) = k2_xboole_0(k2_zfmisc_1(k1_tarski(A), C), k2_zfmisc_1(k1_tarski(B), C))) & (k2_zfmisc_1(C, k2_tarski(A, B)) = k2_xboole_0(k2_zfmisc_1(C, k1_tarski(A)), k2_zfmisc_1(C, k1_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t132_zfmisc_1)).
% 21.79/12.07  tff(f_42, negated_conjecture, ~(![A, B, C, D, E]: (k3_zfmisc_1(k2_tarski(A, B), k1_tarski(C), k2_tarski(D, E)) = k2_enumset1(k3_mcart_1(A, C, D), k3_mcart_1(B, C, D), k3_mcart_1(A, C, E), k3_mcart_1(B, C, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_mcart_1)).
% 21.79/12.07  tff(c_240, plain, (![A_54, B_55, C_56, D_57]: (k3_zfmisc_1(k2_tarski(A_54, B_55), k1_tarski(C_56), k1_tarski(D_57))=k2_tarski(k3_mcart_1(A_54, C_56, D_57), k3_mcart_1(B_55, C_56, D_57)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 21.79/12.07  tff(c_4, plain, (![A_3, B_4, C_5, D_6]: (k2_xboole_0(k2_tarski(A_3, B_4), k2_tarski(C_5, D_6))=k2_enumset1(A_3, B_4, C_5, D_6))), inference(cnfTransformation, [status(thm)], [f_29])).
% 21.79/12.07  tff(c_280, plain, (![C_56, D_6, C_5, D_57, B_55, A_54]: (k2_xboole_0(k3_zfmisc_1(k2_tarski(A_54, B_55), k1_tarski(C_56), k1_tarski(D_57)), k2_tarski(C_5, D_6))=k2_enumset1(k3_mcart_1(A_54, C_56, D_57), k3_mcart_1(B_55, C_56, D_57), C_5, D_6))), inference(superposition, [status(thm), theory('equality')], [c_240, c_4])).
% 21.79/12.07  tff(c_14, plain, (![A_16, B_17, C_18, D_19]: (k3_zfmisc_1(k2_tarski(A_16, B_17), k1_tarski(C_18), k1_tarski(D_19))=k2_tarski(k3_mcart_1(A_16, C_18, D_19), k3_mcart_1(B_17, C_18, D_19)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 21.79/12.07  tff(c_12, plain, (![A_13, B_14, C_15]: (k2_zfmisc_1(k2_zfmisc_1(A_13, B_14), C_15)=k3_zfmisc_1(A_13, B_14, C_15))), inference(cnfTransformation, [status(thm)], [f_37])).
% 21.79/12.07  tff(c_78, plain, (![C_36, A_37, B_38]: (k2_xboole_0(k2_zfmisc_1(C_36, k1_tarski(A_37)), k2_zfmisc_1(C_36, k1_tarski(B_38)))=k2_zfmisc_1(C_36, k2_tarski(A_37, B_38)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 21.79/12.07  tff(c_88, plain, (![A_13, B_14, A_37, B_38]: (k2_xboole_0(k3_zfmisc_1(A_13, B_14, k1_tarski(A_37)), k2_zfmisc_1(k2_zfmisc_1(A_13, B_14), k1_tarski(B_38)))=k2_zfmisc_1(k2_zfmisc_1(A_13, B_14), k2_tarski(A_37, B_38)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_78])).
% 21.79/12.07  tff(c_376, plain, (![A_61, B_62, A_63, B_64]: (k2_xboole_0(k3_zfmisc_1(A_61, B_62, k1_tarski(A_63)), k3_zfmisc_1(A_61, B_62, k1_tarski(B_64)))=k3_zfmisc_1(A_61, B_62, k2_tarski(A_63, B_64)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_12, c_88])).
% 21.79/12.07  tff(c_6365, plain, (![A_258, D_260, C_261, A_259, B_257]: (k2_xboole_0(k3_zfmisc_1(k2_tarski(A_258, B_257), k1_tarski(C_261), k1_tarski(A_259)), k2_tarski(k3_mcart_1(A_258, C_261, D_260), k3_mcart_1(B_257, C_261, D_260)))=k3_zfmisc_1(k2_tarski(A_258, B_257), k1_tarski(C_261), k2_tarski(A_259, D_260)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_376])).
% 21.79/12.07  tff(c_6423, plain, (![C_56, D_260, D_57, B_55, A_54]: (k2_enumset1(k3_mcart_1(A_54, C_56, D_57), k3_mcart_1(B_55, C_56, D_57), k3_mcart_1(A_54, C_56, D_260), k3_mcart_1(B_55, C_56, D_260))=k3_zfmisc_1(k2_tarski(A_54, B_55), k1_tarski(C_56), k2_tarski(D_57, D_260)))), inference(superposition, [status(thm), theory('equality')], [c_280, c_6365])).
% 21.79/12.07  tff(c_16, plain, (k2_enumset1(k3_mcart_1('#skF_1', '#skF_3', '#skF_4'), k3_mcart_1('#skF_2', '#skF_3', '#skF_4'), k3_mcart_1('#skF_1', '#skF_3', '#skF_5'), k3_mcart_1('#skF_2', '#skF_3', '#skF_5'))!=k3_zfmisc_1(k2_tarski('#skF_1', '#skF_2'), k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_42])).
% 21.79/12.07  tff(c_27931, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6423, c_16])).
% 21.79/12.07  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 21.79/12.07  
% 21.79/12.07  Inference rules
% 21.79/12.07  ----------------------
% 21.79/12.07  #Ref     : 0
% 21.79/12.07  #Sup     : 7093
% 21.79/12.07  #Fact    : 0
% 21.79/12.07  #Define  : 0
% 21.79/12.07  #Split   : 0
% 21.79/12.07  #Chain   : 0
% 21.79/12.07  #Close   : 0
% 21.79/12.07  
% 21.79/12.07  Ordering : KBO
% 21.79/12.07  
% 21.79/12.07  Simplification rules
% 21.79/12.07  ----------------------
% 21.79/12.07  #Subsume      : 1139
% 21.79/12.07  #Demod        : 4680
% 21.79/12.07  #Tautology    : 970
% 21.79/12.07  #SimpNegUnit  : 0
% 21.79/12.07  #BackRed      : 1
% 21.79/12.07  
% 21.79/12.07  #Partial instantiations: 0
% 21.79/12.07  #Strategies tried      : 1
% 21.79/12.07  
% 21.79/12.07  Timing (in seconds)
% 21.79/12.07  ----------------------
% 21.79/12.07  Preprocessing        : 0.28
% 21.79/12.07  Parsing              : 0.16
% 21.79/12.07  CNF conversion       : 0.02
% 21.79/12.07  Main loop            : 11.03
% 21.79/12.07  Inferencing          : 2.66
% 21.79/12.07  Reduction            : 6.74
% 21.79/12.07  Demodulation         : 6.29
% 21.79/12.07  BG Simplification    : 0.46
% 21.79/12.07  Subsumption          : 0.94
% 21.79/12.07  Abstraction          : 0.85
% 21.79/12.07  MUC search           : 0.00
% 21.79/12.07  Cooper               : 0.00
% 21.79/12.07  Total                : 11.34
% 21.79/12.07  Index Insertion      : 0.00
% 21.79/12.07  Index Deletion       : 0.00
% 21.79/12.07  Index Matching       : 0.00
% 21.79/12.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------
