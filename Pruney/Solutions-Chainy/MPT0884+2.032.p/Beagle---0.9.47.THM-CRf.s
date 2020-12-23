%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:35 EST 2020

% Result     : Theorem 21.04s
% Output     : CNFRefutation 21.04s
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_mcart_1)).

tff(f_37,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k2_tarski(A,B),C) = k2_xboole_0(k2_zfmisc_1(k1_tarski(A),C),k2_zfmisc_1(k1_tarski(B),C))
      & k2_zfmisc_1(C,k2_tarski(A,B)) = k2_xboole_0(k2_zfmisc_1(C,k1_tarski(A)),k2_zfmisc_1(C,k1_tarski(B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_42,negated_conjecture,(
    ~ ! [A,B,C,D,E] : k3_zfmisc_1(k2_tarski(A,B),k1_tarski(C),k2_tarski(D,E)) = k2_enumset1(k3_mcart_1(A,C,D),k3_mcart_1(B,C,D),k3_mcart_1(A,C,E),k3_mcart_1(B,C,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_mcart_1)).

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

tff(c_6511,plain,(
    ! [A_263,C_266,B_262,D_265,A_264] : k2_xboole_0(k3_zfmisc_1(k2_tarski(A_263,B_262),k1_tarski(C_266),k1_tarski(A_264)),k2_tarski(k3_mcart_1(A_263,C_266,D_265),k3_mcart_1(B_262,C_266,D_265))) = k3_zfmisc_1(k2_tarski(A_263,B_262),k1_tarski(C_266),k2_tarski(A_264,D_265)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_376])).

tff(c_240,plain,(
    ! [A_54,B_55,C_56,D_57] : k3_zfmisc_1(k2_tarski(A_54,B_55),k1_tarski(C_56),k1_tarski(D_57)) = k2_tarski(k3_mcart_1(A_54,C_56,D_57),k3_mcart_1(B_55,C_56,D_57)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3,D_4] : k2_xboole_0(k2_tarski(A_1,B_2),k2_tarski(C_3,D_4)) = k2_enumset1(A_1,B_2,C_3,D_4) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_280,plain,(
    ! [C_56,C_3,D_4,D_57,B_55,A_54] : k2_xboole_0(k3_zfmisc_1(k2_tarski(A_54,B_55),k1_tarski(C_56),k1_tarski(D_57)),k2_tarski(C_3,D_4)) = k2_enumset1(k3_mcart_1(A_54,C_56,D_57),k3_mcart_1(B_55,C_56,D_57),C_3,D_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_240,c_2])).

tff(c_6525,plain,(
    ! [A_263,C_266,B_262,D_265,A_264] : k2_enumset1(k3_mcart_1(A_263,C_266,A_264),k3_mcart_1(B_262,C_266,A_264),k3_mcart_1(A_263,C_266,D_265),k3_mcart_1(B_262,C_266,D_265)) = k3_zfmisc_1(k2_tarski(A_263,B_262),k1_tarski(C_266),k2_tarski(A_264,D_265)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6511,c_280])).

tff(c_16,plain,(
    k2_enumset1(k3_mcart_1('#skF_1','#skF_3','#skF_4'),k3_mcart_1('#skF_2','#skF_3','#skF_4'),k3_mcart_1('#skF_1','#skF_3','#skF_5'),k3_mcart_1('#skF_2','#skF_3','#skF_5')) != k3_zfmisc_1(k2_tarski('#skF_1','#skF_2'),k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_27405,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6525,c_16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:25:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 21.04/11.83  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 21.04/11.83  
% 21.04/11.83  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 21.04/11.83  %$ k2_enumset1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 21.04/11.83  
% 21.04/11.83  %Foreground sorts:
% 21.04/11.83  
% 21.04/11.83  
% 21.04/11.83  %Background operators:
% 21.04/11.83  
% 21.04/11.83  
% 21.04/11.83  %Foreground operators:
% 21.04/11.83  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 21.04/11.83  tff(k1_tarski, type, k1_tarski: $i > $i).
% 21.04/11.83  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 21.04/11.83  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 21.04/11.83  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 21.04/11.83  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 21.04/11.83  tff('#skF_5', type, '#skF_5': $i).
% 21.04/11.83  tff('#skF_2', type, '#skF_2': $i).
% 21.04/11.83  tff('#skF_3', type, '#skF_3': $i).
% 21.04/11.83  tff('#skF_1', type, '#skF_1': $i).
% 21.04/11.83  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 21.04/11.83  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 21.04/11.83  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 21.04/11.83  tff('#skF_4', type, '#skF_4': $i).
% 21.04/11.83  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 21.04/11.83  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 21.04/11.83  
% 21.04/11.84  tff(f_39, axiom, (![A, B, C, D]: (k3_zfmisc_1(k2_tarski(A, B), k1_tarski(C), k1_tarski(D)) = k2_tarski(k3_mcart_1(A, C, D), k3_mcart_1(B, C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_mcart_1)).
% 21.04/11.84  tff(f_37, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 21.04/11.84  tff(f_33, axiom, (![A, B, C]: ((k2_zfmisc_1(k2_tarski(A, B), C) = k2_xboole_0(k2_zfmisc_1(k1_tarski(A), C), k2_zfmisc_1(k1_tarski(B), C))) & (k2_zfmisc_1(C, k2_tarski(A, B)) = k2_xboole_0(k2_zfmisc_1(C, k1_tarski(A)), k2_zfmisc_1(C, k1_tarski(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t132_zfmisc_1)).
% 21.04/11.84  tff(f_27, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l53_enumset1)).
% 21.04/11.84  tff(f_42, negated_conjecture, ~(![A, B, C, D, E]: (k3_zfmisc_1(k2_tarski(A, B), k1_tarski(C), k2_tarski(D, E)) = k2_enumset1(k3_mcart_1(A, C, D), k3_mcart_1(B, C, D), k3_mcart_1(A, C, E), k3_mcart_1(B, C, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_mcart_1)).
% 21.04/11.84  tff(c_14, plain, (![A_16, B_17, C_18, D_19]: (k3_zfmisc_1(k2_tarski(A_16, B_17), k1_tarski(C_18), k1_tarski(D_19))=k2_tarski(k3_mcart_1(A_16, C_18, D_19), k3_mcart_1(B_17, C_18, D_19)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 21.04/11.84  tff(c_12, plain, (![A_13, B_14, C_15]: (k2_zfmisc_1(k2_zfmisc_1(A_13, B_14), C_15)=k3_zfmisc_1(A_13, B_14, C_15))), inference(cnfTransformation, [status(thm)], [f_37])).
% 21.04/11.84  tff(c_78, plain, (![C_36, A_37, B_38]: (k2_xboole_0(k2_zfmisc_1(C_36, k1_tarski(A_37)), k2_zfmisc_1(C_36, k1_tarski(B_38)))=k2_zfmisc_1(C_36, k2_tarski(A_37, B_38)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 21.04/11.84  tff(c_88, plain, (![A_13, B_14, A_37, B_38]: (k2_xboole_0(k3_zfmisc_1(A_13, B_14, k1_tarski(A_37)), k2_zfmisc_1(k2_zfmisc_1(A_13, B_14), k1_tarski(B_38)))=k2_zfmisc_1(k2_zfmisc_1(A_13, B_14), k2_tarski(A_37, B_38)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_78])).
% 21.04/11.84  tff(c_376, plain, (![A_61, B_62, A_63, B_64]: (k2_xboole_0(k3_zfmisc_1(A_61, B_62, k1_tarski(A_63)), k3_zfmisc_1(A_61, B_62, k1_tarski(B_64)))=k3_zfmisc_1(A_61, B_62, k2_tarski(A_63, B_64)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_12, c_88])).
% 21.04/11.84  tff(c_6511, plain, (![A_263, C_266, B_262, D_265, A_264]: (k2_xboole_0(k3_zfmisc_1(k2_tarski(A_263, B_262), k1_tarski(C_266), k1_tarski(A_264)), k2_tarski(k3_mcart_1(A_263, C_266, D_265), k3_mcart_1(B_262, C_266, D_265)))=k3_zfmisc_1(k2_tarski(A_263, B_262), k1_tarski(C_266), k2_tarski(A_264, D_265)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_376])).
% 21.04/11.84  tff(c_240, plain, (![A_54, B_55, C_56, D_57]: (k3_zfmisc_1(k2_tarski(A_54, B_55), k1_tarski(C_56), k1_tarski(D_57))=k2_tarski(k3_mcart_1(A_54, C_56, D_57), k3_mcart_1(B_55, C_56, D_57)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 21.04/11.84  tff(c_2, plain, (![A_1, B_2, C_3, D_4]: (k2_xboole_0(k2_tarski(A_1, B_2), k2_tarski(C_3, D_4))=k2_enumset1(A_1, B_2, C_3, D_4))), inference(cnfTransformation, [status(thm)], [f_27])).
% 21.04/11.84  tff(c_280, plain, (![C_56, C_3, D_4, D_57, B_55, A_54]: (k2_xboole_0(k3_zfmisc_1(k2_tarski(A_54, B_55), k1_tarski(C_56), k1_tarski(D_57)), k2_tarski(C_3, D_4))=k2_enumset1(k3_mcart_1(A_54, C_56, D_57), k3_mcart_1(B_55, C_56, D_57), C_3, D_4))), inference(superposition, [status(thm), theory('equality')], [c_240, c_2])).
% 21.04/11.84  tff(c_6525, plain, (![A_263, C_266, B_262, D_265, A_264]: (k2_enumset1(k3_mcart_1(A_263, C_266, A_264), k3_mcart_1(B_262, C_266, A_264), k3_mcart_1(A_263, C_266, D_265), k3_mcart_1(B_262, C_266, D_265))=k3_zfmisc_1(k2_tarski(A_263, B_262), k1_tarski(C_266), k2_tarski(A_264, D_265)))), inference(superposition, [status(thm), theory('equality')], [c_6511, c_280])).
% 21.04/11.84  tff(c_16, plain, (k2_enumset1(k3_mcart_1('#skF_1', '#skF_3', '#skF_4'), k3_mcart_1('#skF_2', '#skF_3', '#skF_4'), k3_mcart_1('#skF_1', '#skF_3', '#skF_5'), k3_mcart_1('#skF_2', '#skF_3', '#skF_5'))!=k3_zfmisc_1(k2_tarski('#skF_1', '#skF_2'), k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_42])).
% 21.04/11.84  tff(c_27405, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6525, c_16])).
% 21.04/11.84  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 21.04/11.84  
% 21.04/11.84  Inference rules
% 21.04/11.84  ----------------------
% 21.04/11.84  #Ref     : 0
% 21.04/11.84  #Sup     : 6967
% 21.04/11.84  #Fact    : 0
% 21.04/11.84  #Define  : 0
% 21.04/11.84  #Split   : 0
% 21.04/11.84  #Chain   : 0
% 21.04/11.84  #Close   : 0
% 21.04/11.84  
% 21.04/11.84  Ordering : KBO
% 21.04/11.84  
% 21.04/11.84  Simplification rules
% 21.04/11.84  ----------------------
% 21.04/11.84  #Subsume      : 1126
% 21.04/11.84  #Demod        : 4591
% 21.04/11.84  #Tautology    : 958
% 21.04/11.84  #SimpNegUnit  : 0
% 21.04/11.84  #BackRed      : 1
% 21.04/11.84  
% 21.04/11.84  #Partial instantiations: 0
% 21.04/11.84  #Strategies tried      : 1
% 21.04/11.84  
% 21.04/11.84  Timing (in seconds)
% 21.04/11.84  ----------------------
% 21.20/11.84  Preprocessing        : 0.27
% 21.20/11.84  Parsing              : 0.15
% 21.20/11.84  CNF conversion       : 0.02
% 21.20/11.84  Main loop            : 10.81
% 21.20/11.84  Inferencing          : 2.60
% 21.20/11.84  Reduction            : 6.56
% 21.20/11.84  Demodulation         : 6.12
% 21.20/11.84  BG Simplification    : 0.44
% 21.20/11.85  Subsumption          : 0.98
% 21.20/11.85  Abstraction          : 0.80
% 21.20/11.85  MUC search           : 0.00
% 21.20/11.85  Cooper               : 0.00
% 21.20/11.85  Total                : 11.11
% 21.20/11.85  Index Insertion      : 0.00
% 21.20/11.85  Index Deletion       : 0.00
% 21.20/11.85  Index Matching       : 0.00
% 21.20/11.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
