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
% DateTime   : Thu Dec  3 10:09:53 EST 2020

% Result     : Theorem 2.15s
% Output     : CNFRefutation 2.15s
% Verified   : 
% Statistics : Number of formulae       :   39 (  40 expanded)
%              Number of leaves         :   27 (  28 expanded)
%              Depth                    :    6
%              Number of atoms          :   18 (  19 expanded)
%              Number of equality atoms :   17 (  18 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k4_zfmisc_1 > k4_mcart_1 > k2_enumset1 > k3_zfmisc_1 > k3_mcart_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k4_zfmisc_1,type,(
    k4_zfmisc_1: ( $i * $i * $i * $i ) > $i )).

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

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k4_mcart_1,type,(
    k4_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(f_49,axiom,(
    ! [A,B,C,D] : k4_mcart_1(A,B,C,D) = k3_mcart_1(k4_tarski(A,B),C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_mcart_1)).

tff(f_51,axiom,(
    ! [A,B,C] : k3_zfmisc_1(k1_tarski(A),k1_tarski(B),k1_tarski(C)) = k1_tarski(k3_mcart_1(A,B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_mcart_1)).

tff(f_45,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_zfmisc_1(k1_tarski(A),k1_tarski(B)) = k1_tarski(k4_tarski(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B,C,D] : k4_zfmisc_1(A,B,C,D) = k2_zfmisc_1(k3_zfmisc_1(A,B,C),D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C,D] : k4_zfmisc_1(k1_tarski(A),k1_tarski(B),k1_tarski(C),k1_tarski(D)) = k1_tarski(k4_mcart_1(A,B,C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_mcart_1)).

tff(c_24,plain,(
    ! [A_41,B_42,C_43,D_44] : k3_mcart_1(k4_tarski(A_41,B_42),C_43,D_44) = k4_mcart_1(A_41,B_42,C_43,D_44) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_26,plain,(
    ! [A_45,B_46,C_47] : k3_zfmisc_1(k1_tarski(A_45),k1_tarski(B_46),k1_tarski(C_47)) = k1_tarski(k3_mcart_1(A_45,B_46,C_47)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_20,plain,(
    ! [A_34,B_35,C_36] : k2_zfmisc_1(k2_zfmisc_1(A_34,B_35),C_36) = k3_zfmisc_1(A_34,B_35,C_36) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_16,plain,(
    ! [A_29,B_30] : k2_zfmisc_1(k1_tarski(A_29),k1_tarski(B_30)) = k1_tarski(k4_tarski(A_29,B_30)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_80,plain,(
    ! [A_59,B_60,C_61] : k2_zfmisc_1(k2_zfmisc_1(A_59,B_60),C_61) = k3_zfmisc_1(A_59,B_60,C_61) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_143,plain,(
    ! [A_77,B_78,C_79] : k3_zfmisc_1(k1_tarski(A_77),k1_tarski(B_78),C_79) = k2_zfmisc_1(k1_tarski(k4_tarski(A_77,B_78)),C_79) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_80])).

tff(c_22,plain,(
    ! [A_37,B_38,C_39,D_40] : k2_zfmisc_1(k3_zfmisc_1(A_37,B_38,C_39),D_40) = k4_zfmisc_1(A_37,B_38,C_39,D_40) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_153,plain,(
    ! [A_77,B_78,C_79,D_40] : k2_zfmisc_1(k2_zfmisc_1(k1_tarski(k4_tarski(A_77,B_78)),C_79),D_40) = k4_zfmisc_1(k1_tarski(A_77),k1_tarski(B_78),C_79,D_40) ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_22])).

tff(c_161,plain,(
    ! [A_77,B_78,C_79,D_40] : k4_zfmisc_1(k1_tarski(A_77),k1_tarski(B_78),C_79,D_40) = k3_zfmisc_1(k1_tarski(k4_tarski(A_77,B_78)),C_79,D_40) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_153])).

tff(c_28,plain,(
    k4_zfmisc_1(k1_tarski('#skF_1'),k1_tarski('#skF_2'),k1_tarski('#skF_3'),k1_tarski('#skF_4')) != k1_tarski(k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_361,plain,(
    k3_zfmisc_1(k1_tarski(k4_tarski('#skF_1','#skF_2')),k1_tarski('#skF_3'),k1_tarski('#skF_4')) != k1_tarski(k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_28])).

tff(c_364,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_26,c_361])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:40:05 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.15/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.28  
% 2.15/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.28  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k4_zfmisc_1 > k4_mcart_1 > k2_enumset1 > k3_zfmisc_1 > k3_mcart_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.15/1.28  
% 2.15/1.28  %Foreground sorts:
% 2.15/1.28  
% 2.15/1.28  
% 2.15/1.28  %Background operators:
% 2.15/1.28  
% 2.15/1.28  
% 2.15/1.28  %Foreground operators:
% 2.15/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.15/1.28  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.15/1.28  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.15/1.28  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 2.15/1.28  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 2.15/1.28  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.15/1.28  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.15/1.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.15/1.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.15/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.15/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.15/1.28  tff('#skF_1', type, '#skF_1': $i).
% 2.15/1.28  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.15/1.28  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 2.15/1.28  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.15/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.15/1.28  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.15/1.28  tff('#skF_4', type, '#skF_4': $i).
% 2.15/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.15/1.28  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.15/1.28  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 2.15/1.28  
% 2.15/1.29  tff(f_49, axiom, (![A, B, C, D]: (k4_mcart_1(A, B, C, D) = k3_mcart_1(k4_tarski(A, B), C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_mcart_1)).
% 2.15/1.29  tff(f_51, axiom, (![A, B, C]: (k3_zfmisc_1(k1_tarski(A), k1_tarski(B), k1_tarski(C)) = k1_tarski(k3_mcart_1(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_mcart_1)).
% 2.15/1.29  tff(f_45, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 2.15/1.29  tff(f_41, axiom, (![A, B]: (k2_zfmisc_1(k1_tarski(A), k1_tarski(B)) = k1_tarski(k4_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_zfmisc_1)).
% 2.15/1.29  tff(f_47, axiom, (![A, B, C, D]: (k4_zfmisc_1(A, B, C, D) = k2_zfmisc_1(k3_zfmisc_1(A, B, C), D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 2.15/1.29  tff(f_54, negated_conjecture, ~(![A, B, C, D]: (k4_zfmisc_1(k1_tarski(A), k1_tarski(B), k1_tarski(C), k1_tarski(D)) = k1_tarski(k4_mcart_1(A, B, C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_mcart_1)).
% 2.15/1.29  tff(c_24, plain, (![A_41, B_42, C_43, D_44]: (k3_mcart_1(k4_tarski(A_41, B_42), C_43, D_44)=k4_mcart_1(A_41, B_42, C_43, D_44))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.15/1.29  tff(c_26, plain, (![A_45, B_46, C_47]: (k3_zfmisc_1(k1_tarski(A_45), k1_tarski(B_46), k1_tarski(C_47))=k1_tarski(k3_mcart_1(A_45, B_46, C_47)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.15/1.29  tff(c_20, plain, (![A_34, B_35, C_36]: (k2_zfmisc_1(k2_zfmisc_1(A_34, B_35), C_36)=k3_zfmisc_1(A_34, B_35, C_36))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.15/1.29  tff(c_16, plain, (![A_29, B_30]: (k2_zfmisc_1(k1_tarski(A_29), k1_tarski(B_30))=k1_tarski(k4_tarski(A_29, B_30)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.15/1.29  tff(c_80, plain, (![A_59, B_60, C_61]: (k2_zfmisc_1(k2_zfmisc_1(A_59, B_60), C_61)=k3_zfmisc_1(A_59, B_60, C_61))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.15/1.29  tff(c_143, plain, (![A_77, B_78, C_79]: (k3_zfmisc_1(k1_tarski(A_77), k1_tarski(B_78), C_79)=k2_zfmisc_1(k1_tarski(k4_tarski(A_77, B_78)), C_79))), inference(superposition, [status(thm), theory('equality')], [c_16, c_80])).
% 2.15/1.29  tff(c_22, plain, (![A_37, B_38, C_39, D_40]: (k2_zfmisc_1(k3_zfmisc_1(A_37, B_38, C_39), D_40)=k4_zfmisc_1(A_37, B_38, C_39, D_40))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.15/1.29  tff(c_153, plain, (![A_77, B_78, C_79, D_40]: (k2_zfmisc_1(k2_zfmisc_1(k1_tarski(k4_tarski(A_77, B_78)), C_79), D_40)=k4_zfmisc_1(k1_tarski(A_77), k1_tarski(B_78), C_79, D_40))), inference(superposition, [status(thm), theory('equality')], [c_143, c_22])).
% 2.15/1.29  tff(c_161, plain, (![A_77, B_78, C_79, D_40]: (k4_zfmisc_1(k1_tarski(A_77), k1_tarski(B_78), C_79, D_40)=k3_zfmisc_1(k1_tarski(k4_tarski(A_77, B_78)), C_79, D_40))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_153])).
% 2.15/1.29  tff(c_28, plain, (k4_zfmisc_1(k1_tarski('#skF_1'), k1_tarski('#skF_2'), k1_tarski('#skF_3'), k1_tarski('#skF_4'))!=k1_tarski(k4_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.15/1.29  tff(c_361, plain, (k3_zfmisc_1(k1_tarski(k4_tarski('#skF_1', '#skF_2')), k1_tarski('#skF_3'), k1_tarski('#skF_4'))!=k1_tarski(k4_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_161, c_28])).
% 2.15/1.29  tff(c_364, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_26, c_361])).
% 2.15/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.29  
% 2.15/1.29  Inference rules
% 2.15/1.29  ----------------------
% 2.15/1.29  #Ref     : 0
% 2.15/1.29  #Sup     : 82
% 2.15/1.29  #Fact    : 0
% 2.15/1.29  #Define  : 0
% 2.15/1.29  #Split   : 0
% 2.15/1.29  #Chain   : 0
% 2.15/1.29  #Close   : 0
% 2.15/1.29  
% 2.15/1.29  Ordering : KBO
% 2.15/1.29  
% 2.15/1.29  Simplification rules
% 2.15/1.29  ----------------------
% 2.15/1.29  #Subsume      : 0
% 2.15/1.29  #Demod        : 30
% 2.15/1.29  #Tautology    : 49
% 2.15/1.29  #SimpNegUnit  : 0
% 2.15/1.29  #BackRed      : 2
% 2.15/1.29  
% 2.15/1.29  #Partial instantiations: 0
% 2.15/1.29  #Strategies tried      : 1
% 2.15/1.29  
% 2.15/1.29  Timing (in seconds)
% 2.15/1.29  ----------------------
% 2.15/1.29  Preprocessing        : 0.30
% 2.15/1.29  Parsing              : 0.16
% 2.15/1.29  CNF conversion       : 0.02
% 2.15/1.29  Main loop            : 0.22
% 2.15/1.29  Inferencing          : 0.10
% 2.15/1.29  Reduction            : 0.07
% 2.15/1.29  Demodulation         : 0.06
% 2.15/1.29  BG Simplification    : 0.02
% 2.15/1.29  Subsumption          : 0.02
% 2.15/1.29  Abstraction          : 0.02
% 2.15/1.29  MUC search           : 0.00
% 2.15/1.29  Cooper               : 0.00
% 2.15/1.29  Total                : 0.55
% 2.15/1.29  Index Insertion      : 0.00
% 2.15/1.29  Index Deletion       : 0.00
% 2.15/1.30  Index Matching       : 0.00
% 2.15/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
