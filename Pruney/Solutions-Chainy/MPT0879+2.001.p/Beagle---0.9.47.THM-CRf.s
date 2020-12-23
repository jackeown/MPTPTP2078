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
% DateTime   : Thu Dec  3 10:09:30 EST 2020

% Result     : Theorem 1.86s
% Output     : CNFRefutation 1.97s
% Verified   : 
% Statistics : Number of formulae       :   39 (  58 expanded)
%              Number of leaves         :   24 (  32 expanded)
%              Depth                    :    8
%              Number of atoms          :   22 (  41 expanded)
%              Number of equality atoms :   21 (  40 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k3_zfmisc_1 > k3_mcart_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_41,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D] : k2_zfmisc_1(k2_tarski(A,B),k2_tarski(C,D)) = k2_enumset1(k4_tarski(A,C),k4_tarski(A,D),k4_tarski(B,C),k4_tarski(B,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_29,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_46,negated_conjecture,(
    ~ ! [A,B,C] : k3_zfmisc_1(k1_tarski(A),k1_tarski(B),k1_tarski(C)) = k1_tarski(k3_mcart_1(A,B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_mcart_1)).

tff(c_16,plain,(
    ! [A_26,B_27,C_28] : k4_tarski(k4_tarski(A_26,B_27),C_28) = k3_mcart_1(A_26,B_27,C_28) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_133,plain,(
    ! [A_67,C_68,D_69,B_70] : k2_enumset1(k4_tarski(A_67,C_68),k4_tarski(A_67,D_69),k4_tarski(B_70,C_68),k4_tarski(B_70,D_69)) = k2_zfmisc_1(k2_tarski(A_67,B_70),k2_tarski(C_68,D_69)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6,plain,(
    ! [A_4,B_5,C_6] : k2_enumset1(A_4,A_4,B_5,C_6) = k1_enumset1(A_4,B_5,C_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_140,plain,(
    ! [A_67,D_69,B_70] : k1_enumset1(k4_tarski(A_67,D_69),k4_tarski(B_70,D_69),k4_tarski(B_70,D_69)) = k2_zfmisc_1(k2_tarski(A_67,B_70),k2_tarski(D_69,D_69)) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_6])).

tff(c_168,plain,(
    ! [A_71,D_72,B_73] : k1_enumset1(k4_tarski(A_71,D_72),k4_tarski(B_73,D_72),k4_tarski(B_73,D_72)) = k2_zfmisc_1(k2_tarski(A_71,B_73),k1_tarski(D_72)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_140])).

tff(c_4,plain,(
    ! [A_2,B_3] : k1_enumset1(A_2,A_2,B_3) = k2_tarski(A_2,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_175,plain,(
    ! [B_73,D_72] : k2_zfmisc_1(k2_tarski(B_73,B_73),k1_tarski(D_72)) = k2_tarski(k4_tarski(B_73,D_72),k4_tarski(B_73,D_72)) ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_4])).

tff(c_193,plain,(
    ! [B_73,D_72] : k2_zfmisc_1(k1_tarski(B_73),k1_tarski(D_72)) = k1_tarski(k4_tarski(B_73,D_72)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_175])).

tff(c_199,plain,(
    ! [B_74,D_75] : k2_zfmisc_1(k1_tarski(B_74),k1_tarski(D_75)) = k1_tarski(k4_tarski(B_74,D_75)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_175])).

tff(c_18,plain,(
    ! [A_29,B_30,C_31] : k2_zfmisc_1(k2_zfmisc_1(A_29,B_30),C_31) = k3_zfmisc_1(A_29,B_30,C_31) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_208,plain,(
    ! [B_74,D_75,C_31] : k3_zfmisc_1(k1_tarski(B_74),k1_tarski(D_75),C_31) = k2_zfmisc_1(k1_tarski(k4_tarski(B_74,D_75)),C_31) ),
    inference(superposition,[status(thm),theory(equality)],[c_199,c_18])).

tff(c_20,plain,(
    k3_zfmisc_1(k1_tarski('#skF_1'),k1_tarski('#skF_2'),k1_tarski('#skF_3')) != k1_tarski(k3_mcart_1('#skF_1','#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_215,plain,(
    k2_zfmisc_1(k1_tarski(k4_tarski('#skF_1','#skF_2')),k1_tarski('#skF_3')) != k1_tarski(k3_mcart_1('#skF_1','#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_20])).

tff(c_218,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_193,c_215])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:53:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.86/1.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.86/1.18  
% 1.86/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.86/1.18  %$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k3_zfmisc_1 > k3_mcart_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 1.86/1.18  
% 1.86/1.18  %Foreground sorts:
% 1.86/1.18  
% 1.86/1.18  
% 1.86/1.18  %Background operators:
% 1.86/1.18  
% 1.86/1.18  
% 1.86/1.18  %Foreground operators:
% 1.86/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.86/1.18  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.86/1.18  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.86/1.18  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 1.86/1.18  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.86/1.18  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.86/1.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.86/1.18  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.86/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.86/1.18  tff('#skF_3', type, '#skF_3': $i).
% 1.86/1.18  tff('#skF_1', type, '#skF_1': $i).
% 1.86/1.18  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.86/1.18  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 1.86/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.86/1.18  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.86/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.86/1.18  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.86/1.18  
% 1.97/1.19  tff(f_41, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 1.97/1.19  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.97/1.19  tff(f_39, axiom, (![A, B, C, D]: (k2_zfmisc_1(k2_tarski(A, B), k2_tarski(C, D)) = k2_enumset1(k4_tarski(A, C), k4_tarski(A, D), k4_tarski(B, C), k4_tarski(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_zfmisc_1)).
% 1.97/1.19  tff(f_31, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 1.97/1.19  tff(f_29, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 1.97/1.19  tff(f_43, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 1.97/1.19  tff(f_46, negated_conjecture, ~(![A, B, C]: (k3_zfmisc_1(k1_tarski(A), k1_tarski(B), k1_tarski(C)) = k1_tarski(k3_mcart_1(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_mcart_1)).
% 1.97/1.19  tff(c_16, plain, (![A_26, B_27, C_28]: (k4_tarski(k4_tarski(A_26, B_27), C_28)=k3_mcart_1(A_26, B_27, C_28))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.97/1.19  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.97/1.19  tff(c_133, plain, (![A_67, C_68, D_69, B_70]: (k2_enumset1(k4_tarski(A_67, C_68), k4_tarski(A_67, D_69), k4_tarski(B_70, C_68), k4_tarski(B_70, D_69))=k2_zfmisc_1(k2_tarski(A_67, B_70), k2_tarski(C_68, D_69)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.97/1.19  tff(c_6, plain, (![A_4, B_5, C_6]: (k2_enumset1(A_4, A_4, B_5, C_6)=k1_enumset1(A_4, B_5, C_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.97/1.19  tff(c_140, plain, (![A_67, D_69, B_70]: (k1_enumset1(k4_tarski(A_67, D_69), k4_tarski(B_70, D_69), k4_tarski(B_70, D_69))=k2_zfmisc_1(k2_tarski(A_67, B_70), k2_tarski(D_69, D_69)))), inference(superposition, [status(thm), theory('equality')], [c_133, c_6])).
% 1.97/1.19  tff(c_168, plain, (![A_71, D_72, B_73]: (k1_enumset1(k4_tarski(A_71, D_72), k4_tarski(B_73, D_72), k4_tarski(B_73, D_72))=k2_zfmisc_1(k2_tarski(A_71, B_73), k1_tarski(D_72)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_140])).
% 1.97/1.19  tff(c_4, plain, (![A_2, B_3]: (k1_enumset1(A_2, A_2, B_3)=k2_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.97/1.19  tff(c_175, plain, (![B_73, D_72]: (k2_zfmisc_1(k2_tarski(B_73, B_73), k1_tarski(D_72))=k2_tarski(k4_tarski(B_73, D_72), k4_tarski(B_73, D_72)))), inference(superposition, [status(thm), theory('equality')], [c_168, c_4])).
% 1.97/1.19  tff(c_193, plain, (![B_73, D_72]: (k2_zfmisc_1(k1_tarski(B_73), k1_tarski(D_72))=k1_tarski(k4_tarski(B_73, D_72)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2, c_175])).
% 1.97/1.19  tff(c_199, plain, (![B_74, D_75]: (k2_zfmisc_1(k1_tarski(B_74), k1_tarski(D_75))=k1_tarski(k4_tarski(B_74, D_75)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2, c_175])).
% 1.97/1.19  tff(c_18, plain, (![A_29, B_30, C_31]: (k2_zfmisc_1(k2_zfmisc_1(A_29, B_30), C_31)=k3_zfmisc_1(A_29, B_30, C_31))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.97/1.19  tff(c_208, plain, (![B_74, D_75, C_31]: (k3_zfmisc_1(k1_tarski(B_74), k1_tarski(D_75), C_31)=k2_zfmisc_1(k1_tarski(k4_tarski(B_74, D_75)), C_31))), inference(superposition, [status(thm), theory('equality')], [c_199, c_18])).
% 1.97/1.19  tff(c_20, plain, (k3_zfmisc_1(k1_tarski('#skF_1'), k1_tarski('#skF_2'), k1_tarski('#skF_3'))!=k1_tarski(k3_mcart_1('#skF_1', '#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.97/1.19  tff(c_215, plain, (k2_zfmisc_1(k1_tarski(k4_tarski('#skF_1', '#skF_2')), k1_tarski('#skF_3'))!=k1_tarski(k3_mcart_1('#skF_1', '#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_208, c_20])).
% 1.97/1.19  tff(c_218, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_193, c_215])).
% 1.97/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.19  
% 1.97/1.19  Inference rules
% 1.97/1.19  ----------------------
% 1.97/1.19  #Ref     : 0
% 1.97/1.19  #Sup     : 45
% 1.97/1.19  #Fact    : 0
% 1.97/1.19  #Define  : 0
% 1.97/1.19  #Split   : 0
% 1.97/1.19  #Chain   : 0
% 1.97/1.19  #Close   : 0
% 1.97/1.19  
% 1.97/1.19  Ordering : KBO
% 1.97/1.19  
% 1.97/1.19  Simplification rules
% 1.97/1.19  ----------------------
% 1.97/1.19  #Subsume      : 0
% 1.97/1.19  #Demod        : 23
% 1.97/1.19  #Tautology    : 32
% 1.97/1.19  #SimpNegUnit  : 0
% 1.97/1.19  #BackRed      : 1
% 1.97/1.19  
% 1.97/1.19  #Partial instantiations: 0
% 1.97/1.19  #Strategies tried      : 1
% 1.97/1.19  
% 1.97/1.19  Timing (in seconds)
% 1.97/1.19  ----------------------
% 1.97/1.20  Preprocessing        : 0.28
% 1.97/1.20  Parsing              : 0.14
% 1.97/1.20  CNF conversion       : 0.02
% 1.97/1.20  Main loop            : 0.15
% 1.97/1.20  Inferencing          : 0.06
% 1.97/1.20  Reduction            : 0.05
% 1.97/1.20  Demodulation         : 0.04
% 1.97/1.20  BG Simplification    : 0.01
% 1.97/1.20  Subsumption          : 0.02
% 1.97/1.20  Abstraction          : 0.02
% 1.97/1.20  MUC search           : 0.00
% 1.97/1.20  Cooper               : 0.00
% 1.97/1.20  Total                : 0.45
% 1.97/1.20  Index Insertion      : 0.00
% 1.97/1.20  Index Deletion       : 0.00
% 1.97/1.20  Index Matching       : 0.00
% 1.97/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
