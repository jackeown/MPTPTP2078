%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:51 EST 2020

% Result     : Theorem 5.67s
% Output     : CNFRefutation 5.71s
% Verified   : 
% Statistics : Number of formulae       :   28 (  29 expanded)
%              Number of leaves         :   19 (  20 expanded)
%              Depth                    :    4
%              Number of atoms          :   15 (  17 expanded)
%              Number of equality atoms :   14 (  16 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k2_enumset1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(f_41,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k1_tarski(A),k2_tarski(B,C)) = k2_tarski(k4_tarski(A,B),k4_tarski(A,C))
      & k2_zfmisc_1(k2_tarski(A,B),k1_tarski(C)) = k2_tarski(k4_tarski(A,C),k4_tarski(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k2_tarski(A,B),C) = k2_xboole_0(k2_zfmisc_1(k1_tarski(A),C),k2_zfmisc_1(k1_tarski(B),C))
      & k2_zfmisc_1(C,k2_tarski(A,B)) = k2_xboole_0(k2_zfmisc_1(C,k1_tarski(A)),k2_zfmisc_1(C,k1_tarski(B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_enumset1)).

tff(f_46,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_zfmisc_1(k2_tarski(A,B),k2_tarski(C,D)) = k2_enumset1(k4_tarski(A,C),k4_tarski(A,D),k4_tarski(B,C),k4_tarski(B,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_zfmisc_1)).

tff(c_12,plain,(
    ! [A_11,B_12,C_13] : k2_zfmisc_1(k1_tarski(A_11),k2_tarski(B_12,C_13)) = k2_tarski(k4_tarski(A_11,B_12),k4_tarski(A_11,C_13)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_412,plain,(
    ! [A_45,C_46,B_47] : k2_xboole_0(k2_zfmisc_1(k1_tarski(A_45),C_46),k2_zfmisc_1(k1_tarski(B_47),C_46)) = k2_zfmisc_1(k2_tarski(A_45,B_47),C_46) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_3527,plain,(
    ! [A_167,B_168,C_169,A_170] : k2_xboole_0(k2_zfmisc_1(k1_tarski(A_167),k2_tarski(B_168,C_169)),k2_tarski(k4_tarski(A_170,B_168),k4_tarski(A_170,C_169))) = k2_zfmisc_1(k2_tarski(A_167,A_170),k2_tarski(B_168,C_169)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_412])).

tff(c_283,plain,(
    ! [A_39,B_40,C_41] : k2_zfmisc_1(k1_tarski(A_39),k2_tarski(B_40,C_41)) = k2_tarski(k4_tarski(A_39,B_40),k4_tarski(A_39,C_41)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4,plain,(
    ! [A_3,B_4,C_5,D_6] : k2_xboole_0(k2_tarski(A_3,B_4),k2_tarski(C_5,D_6)) = k2_enumset1(A_3,B_4,C_5,D_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_305,plain,(
    ! [D_6,C_5,A_39,C_41,B_40] : k2_xboole_0(k2_zfmisc_1(k1_tarski(A_39),k2_tarski(B_40,C_41)),k2_tarski(C_5,D_6)) = k2_enumset1(k4_tarski(A_39,B_40),k4_tarski(A_39,C_41),C_5,D_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_283,c_4])).

tff(c_3533,plain,(
    ! [A_167,B_168,C_169,A_170] : k2_enumset1(k4_tarski(A_167,B_168),k4_tarski(A_167,C_169),k4_tarski(A_170,B_168),k4_tarski(A_170,C_169)) = k2_zfmisc_1(k2_tarski(A_167,A_170),k2_tarski(B_168,C_169)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3527,c_305])).

tff(c_18,plain,(
    k2_enumset1(k4_tarski('#skF_1','#skF_3'),k4_tarski('#skF_1','#skF_4'),k4_tarski('#skF_2','#skF_3'),k4_tarski('#skF_2','#skF_4')) != k2_zfmisc_1(k2_tarski('#skF_1','#skF_2'),k2_tarski('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_3696,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3533,c_18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:51:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.67/2.09  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.67/2.09  
% 5.67/2.09  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.67/2.09  %$ k2_enumset1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.67/2.09  
% 5.67/2.09  %Foreground sorts:
% 5.67/2.09  
% 5.67/2.09  
% 5.67/2.09  %Background operators:
% 5.67/2.09  
% 5.67/2.09  
% 5.67/2.09  %Foreground operators:
% 5.67/2.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.67/2.09  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.67/2.09  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.67/2.09  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.67/2.09  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.67/2.09  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.67/2.09  tff('#skF_2', type, '#skF_2': $i).
% 5.67/2.09  tff('#skF_3', type, '#skF_3': $i).
% 5.67/2.09  tff('#skF_1', type, '#skF_1': $i).
% 5.67/2.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.67/2.09  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.67/2.09  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.67/2.09  tff('#skF_4', type, '#skF_4': $i).
% 5.67/2.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.67/2.09  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.67/2.09  
% 5.71/2.10  tff(f_41, axiom, (![A, B, C]: ((k2_zfmisc_1(k1_tarski(A), k2_tarski(B, C)) = k2_tarski(k4_tarski(A, B), k4_tarski(A, C))) & (k2_zfmisc_1(k2_tarski(A, B), k1_tarski(C)) = k2_tarski(k4_tarski(A, C), k4_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_zfmisc_1)).
% 5.71/2.10  tff(f_37, axiom, (![A, B, C]: ((k2_zfmisc_1(k2_tarski(A, B), C) = k2_xboole_0(k2_zfmisc_1(k1_tarski(A), C), k2_zfmisc_1(k1_tarski(B), C))) & (k2_zfmisc_1(C, k2_tarski(A, B)) = k2_xboole_0(k2_zfmisc_1(C, k1_tarski(A)), k2_zfmisc_1(C, k1_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t132_zfmisc_1)).
% 5.71/2.10  tff(f_31, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_enumset1)).
% 5.71/2.10  tff(f_46, negated_conjecture, ~(![A, B, C, D]: (k2_zfmisc_1(k2_tarski(A, B), k2_tarski(C, D)) = k2_enumset1(k4_tarski(A, C), k4_tarski(A, D), k4_tarski(B, C), k4_tarski(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_zfmisc_1)).
% 5.71/2.10  tff(c_12, plain, (![A_11, B_12, C_13]: (k2_zfmisc_1(k1_tarski(A_11), k2_tarski(B_12, C_13))=k2_tarski(k4_tarski(A_11, B_12), k4_tarski(A_11, C_13)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.71/2.10  tff(c_412, plain, (![A_45, C_46, B_47]: (k2_xboole_0(k2_zfmisc_1(k1_tarski(A_45), C_46), k2_zfmisc_1(k1_tarski(B_47), C_46))=k2_zfmisc_1(k2_tarski(A_45, B_47), C_46))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.71/2.10  tff(c_3527, plain, (![A_167, B_168, C_169, A_170]: (k2_xboole_0(k2_zfmisc_1(k1_tarski(A_167), k2_tarski(B_168, C_169)), k2_tarski(k4_tarski(A_170, B_168), k4_tarski(A_170, C_169)))=k2_zfmisc_1(k2_tarski(A_167, A_170), k2_tarski(B_168, C_169)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_412])).
% 5.71/2.10  tff(c_283, plain, (![A_39, B_40, C_41]: (k2_zfmisc_1(k1_tarski(A_39), k2_tarski(B_40, C_41))=k2_tarski(k4_tarski(A_39, B_40), k4_tarski(A_39, C_41)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.71/2.10  tff(c_4, plain, (![A_3, B_4, C_5, D_6]: (k2_xboole_0(k2_tarski(A_3, B_4), k2_tarski(C_5, D_6))=k2_enumset1(A_3, B_4, C_5, D_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.71/2.10  tff(c_305, plain, (![D_6, C_5, A_39, C_41, B_40]: (k2_xboole_0(k2_zfmisc_1(k1_tarski(A_39), k2_tarski(B_40, C_41)), k2_tarski(C_5, D_6))=k2_enumset1(k4_tarski(A_39, B_40), k4_tarski(A_39, C_41), C_5, D_6))), inference(superposition, [status(thm), theory('equality')], [c_283, c_4])).
% 5.71/2.10  tff(c_3533, plain, (![A_167, B_168, C_169, A_170]: (k2_enumset1(k4_tarski(A_167, B_168), k4_tarski(A_167, C_169), k4_tarski(A_170, B_168), k4_tarski(A_170, C_169))=k2_zfmisc_1(k2_tarski(A_167, A_170), k2_tarski(B_168, C_169)))), inference(superposition, [status(thm), theory('equality')], [c_3527, c_305])).
% 5.71/2.10  tff(c_18, plain, (k2_enumset1(k4_tarski('#skF_1', '#skF_3'), k4_tarski('#skF_1', '#skF_4'), k4_tarski('#skF_2', '#skF_3'), k4_tarski('#skF_2', '#skF_4'))!=k2_zfmisc_1(k2_tarski('#skF_1', '#skF_2'), k2_tarski('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.71/2.10  tff(c_3696, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3533, c_18])).
% 5.71/2.10  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.71/2.10  
% 5.71/2.10  Inference rules
% 5.71/2.10  ----------------------
% 5.71/2.10  #Ref     : 1
% 5.71/2.10  #Sup     : 938
% 5.71/2.10  #Fact    : 0
% 5.71/2.10  #Define  : 0
% 5.71/2.10  #Split   : 0
% 5.71/2.10  #Chain   : 0
% 5.71/2.10  #Close   : 0
% 5.71/2.10  
% 5.71/2.10  Ordering : KBO
% 5.71/2.10  
% 5.71/2.10  Simplification rules
% 5.71/2.10  ----------------------
% 5.71/2.10  #Subsume      : 74
% 5.71/2.10  #Demod        : 878
% 5.71/2.10  #Tautology    : 457
% 5.71/2.10  #SimpNegUnit  : 0
% 5.71/2.10  #BackRed      : 1
% 5.71/2.10  
% 5.71/2.10  #Partial instantiations: 0
% 5.71/2.10  #Strategies tried      : 1
% 5.71/2.10  
% 5.71/2.10  Timing (in seconds)
% 5.71/2.10  ----------------------
% 5.71/2.10  Preprocessing        : 0.29
% 5.71/2.10  Parsing              : 0.15
% 5.71/2.10  CNF conversion       : 0.02
% 5.71/2.10  Main loop            : 1.03
% 5.71/2.10  Inferencing          : 0.40
% 5.71/2.10  Reduction            : 0.41
% 5.71/2.10  Demodulation         : 0.35
% 5.71/2.10  BG Simplification    : 0.07
% 5.71/2.10  Subsumption          : 0.11
% 5.71/2.10  Abstraction          : 0.08
% 5.71/2.10  MUC search           : 0.00
% 5.71/2.10  Cooper               : 0.00
% 5.71/2.10  Total                : 1.34
% 5.71/2.10  Index Insertion      : 0.00
% 5.71/2.10  Index Deletion       : 0.00
% 5.71/2.10  Index Matching       : 0.00
% 5.71/2.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
