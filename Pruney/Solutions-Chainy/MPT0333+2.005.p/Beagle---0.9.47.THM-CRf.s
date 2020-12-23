%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:51 EST 2020

% Result     : Theorem 4.90s
% Output     : CNFRefutation 5.24s
% Verified   : 
% Statistics : Number of formulae       :   27 (  28 expanded)
%              Number of leaves         :   18 (  19 expanded)
%              Depth                    :    4
%              Number of atoms          :   15 (  17 expanded)
%              Number of equality atoms :   14 (  16 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

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
    ! [A,B,C] :
      ( k2_zfmisc_1(k1_tarski(A),k2_tarski(B,C)) = k2_tarski(k4_tarski(A,B),k4_tarski(A,C))
      & k2_zfmisc_1(k2_tarski(A,B),k1_tarski(C)) = k2_tarski(k4_tarski(A,C),k4_tarski(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k2_tarski(A,B),C) = k2_xboole_0(k2_zfmisc_1(k1_tarski(A),C),k2_zfmisc_1(k1_tarski(B),C))
      & k2_zfmisc_1(C,k2_tarski(A,B)) = k2_xboole_0(k2_zfmisc_1(C,k1_tarski(A)),k2_zfmisc_1(C,k1_tarski(B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_42,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_zfmisc_1(k2_tarski(A,B),k2_tarski(C,D)) = k2_enumset1(k4_tarski(A,C),k4_tarski(A,D),k4_tarski(B,C),k4_tarski(B,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_zfmisc_1)).

tff(c_12,plain,(
    ! [A_11,B_12,C_13] : k2_zfmisc_1(k1_tarski(A_11),k2_tarski(B_12,C_13)) = k2_tarski(k4_tarski(A_11,B_12),k4_tarski(A_11,C_13)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_260,plain,(
    ! [A_37,C_38,B_39] : k2_xboole_0(k2_zfmisc_1(k1_tarski(A_37),C_38),k2_zfmisc_1(k1_tarski(B_39),C_38)) = k2_zfmisc_1(k2_tarski(A_37,B_39),C_38) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2804,plain,(
    ! [A_141,B_142,C_143,B_144] : k2_xboole_0(k2_tarski(k4_tarski(A_141,B_142),k4_tarski(A_141,C_143)),k2_zfmisc_1(k1_tarski(B_144),k2_tarski(B_142,C_143))) = k2_zfmisc_1(k2_tarski(A_141,B_144),k2_tarski(B_142,C_143)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_260])).

tff(c_96,plain,(
    ! [A_26,B_27,C_28] : k2_zfmisc_1(k1_tarski(A_26),k2_tarski(B_27,C_28)) = k2_tarski(k4_tarski(A_26,B_27),k4_tarski(A_26,C_28)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3,D_4] : k2_xboole_0(k2_tarski(A_1,B_2),k2_tarski(C_3,D_4)) = k2_enumset1(A_1,B_2,C_3,D_4) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_114,plain,(
    ! [B_27,B_2,A_1,A_26,C_28] : k2_xboole_0(k2_tarski(A_1,B_2),k2_zfmisc_1(k1_tarski(A_26),k2_tarski(B_27,C_28))) = k2_enumset1(A_1,B_2,k4_tarski(A_26,B_27),k4_tarski(A_26,C_28)) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_2])).

tff(c_2810,plain,(
    ! [A_141,B_142,C_143,B_144] : k2_enumset1(k4_tarski(A_141,B_142),k4_tarski(A_141,C_143),k4_tarski(B_144,B_142),k4_tarski(B_144,C_143)) = k2_zfmisc_1(k2_tarski(A_141,B_144),k2_tarski(B_142,C_143)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2804,c_114])).

tff(c_16,plain,(
    k2_enumset1(k4_tarski('#skF_1','#skF_3'),k4_tarski('#skF_1','#skF_4'),k4_tarski('#skF_2','#skF_3'),k4_tarski('#skF_2','#skF_4')) != k2_zfmisc_1(k2_tarski('#skF_1','#skF_2'),k2_tarski('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2884,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2810,c_16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:12:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.90/1.93  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.90/1.94  
% 4.90/1.94  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.24/1.94  %$ k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.24/1.94  
% 5.24/1.94  %Foreground sorts:
% 5.24/1.94  
% 5.24/1.94  
% 5.24/1.94  %Background operators:
% 5.24/1.94  
% 5.24/1.94  
% 5.24/1.94  %Foreground operators:
% 5.24/1.94  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.24/1.94  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.24/1.94  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.24/1.94  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.24/1.94  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.24/1.94  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.24/1.94  tff('#skF_2', type, '#skF_2': $i).
% 5.24/1.94  tff('#skF_3', type, '#skF_3': $i).
% 5.24/1.94  tff('#skF_1', type, '#skF_1': $i).
% 5.24/1.94  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.24/1.94  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.24/1.94  tff('#skF_4', type, '#skF_4': $i).
% 5.24/1.94  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.24/1.94  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.24/1.94  
% 5.24/1.95  tff(f_39, axiom, (![A, B, C]: ((k2_zfmisc_1(k1_tarski(A), k2_tarski(B, C)) = k2_tarski(k4_tarski(A, B), k4_tarski(A, C))) & (k2_zfmisc_1(k2_tarski(A, B), k1_tarski(C)) = k2_tarski(k4_tarski(A, C), k4_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_zfmisc_1)).
% 5.24/1.95  tff(f_35, axiom, (![A, B, C]: ((k2_zfmisc_1(k2_tarski(A, B), C) = k2_xboole_0(k2_zfmisc_1(k1_tarski(A), C), k2_zfmisc_1(k1_tarski(B), C))) & (k2_zfmisc_1(C, k2_tarski(A, B)) = k2_xboole_0(k2_zfmisc_1(C, k1_tarski(A)), k2_zfmisc_1(C, k1_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t132_zfmisc_1)).
% 5.24/1.95  tff(f_27, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l53_enumset1)).
% 5.24/1.95  tff(f_42, negated_conjecture, ~(![A, B, C, D]: (k2_zfmisc_1(k2_tarski(A, B), k2_tarski(C, D)) = k2_enumset1(k4_tarski(A, C), k4_tarski(A, D), k4_tarski(B, C), k4_tarski(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_zfmisc_1)).
% 5.24/1.95  tff(c_12, plain, (![A_11, B_12, C_13]: (k2_zfmisc_1(k1_tarski(A_11), k2_tarski(B_12, C_13))=k2_tarski(k4_tarski(A_11, B_12), k4_tarski(A_11, C_13)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.24/1.95  tff(c_260, plain, (![A_37, C_38, B_39]: (k2_xboole_0(k2_zfmisc_1(k1_tarski(A_37), C_38), k2_zfmisc_1(k1_tarski(B_39), C_38))=k2_zfmisc_1(k2_tarski(A_37, B_39), C_38))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.24/1.95  tff(c_2804, plain, (![A_141, B_142, C_143, B_144]: (k2_xboole_0(k2_tarski(k4_tarski(A_141, B_142), k4_tarski(A_141, C_143)), k2_zfmisc_1(k1_tarski(B_144), k2_tarski(B_142, C_143)))=k2_zfmisc_1(k2_tarski(A_141, B_144), k2_tarski(B_142, C_143)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_260])).
% 5.24/1.95  tff(c_96, plain, (![A_26, B_27, C_28]: (k2_zfmisc_1(k1_tarski(A_26), k2_tarski(B_27, C_28))=k2_tarski(k4_tarski(A_26, B_27), k4_tarski(A_26, C_28)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.24/1.95  tff(c_2, plain, (![A_1, B_2, C_3, D_4]: (k2_xboole_0(k2_tarski(A_1, B_2), k2_tarski(C_3, D_4))=k2_enumset1(A_1, B_2, C_3, D_4))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.24/1.95  tff(c_114, plain, (![B_27, B_2, A_1, A_26, C_28]: (k2_xboole_0(k2_tarski(A_1, B_2), k2_zfmisc_1(k1_tarski(A_26), k2_tarski(B_27, C_28)))=k2_enumset1(A_1, B_2, k4_tarski(A_26, B_27), k4_tarski(A_26, C_28)))), inference(superposition, [status(thm), theory('equality')], [c_96, c_2])).
% 5.24/1.95  tff(c_2810, plain, (![A_141, B_142, C_143, B_144]: (k2_enumset1(k4_tarski(A_141, B_142), k4_tarski(A_141, C_143), k4_tarski(B_144, B_142), k4_tarski(B_144, C_143))=k2_zfmisc_1(k2_tarski(A_141, B_144), k2_tarski(B_142, C_143)))), inference(superposition, [status(thm), theory('equality')], [c_2804, c_114])).
% 5.24/1.95  tff(c_16, plain, (k2_enumset1(k4_tarski('#skF_1', '#skF_3'), k4_tarski('#skF_1', '#skF_4'), k4_tarski('#skF_2', '#skF_3'), k4_tarski('#skF_2', '#skF_4'))!=k2_zfmisc_1(k2_tarski('#skF_1', '#skF_2'), k2_tarski('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.24/1.95  tff(c_2884, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2810, c_16])).
% 5.24/1.95  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.24/1.95  
% 5.24/1.95  Inference rules
% 5.24/1.95  ----------------------
% 5.24/1.95  #Ref     : 0
% 5.24/1.95  #Sup     : 744
% 5.24/1.95  #Fact    : 0
% 5.24/1.95  #Define  : 0
% 5.24/1.95  #Split   : 0
% 5.24/1.95  #Chain   : 0
% 5.24/1.95  #Close   : 0
% 5.24/1.95  
% 5.24/1.95  Ordering : KBO
% 5.24/1.95  
% 5.24/1.95  Simplification rules
% 5.24/1.95  ----------------------
% 5.24/1.95  #Subsume      : 71
% 5.24/1.95  #Demod        : 591
% 5.24/1.95  #Tautology    : 338
% 5.24/1.95  #SimpNegUnit  : 0
% 5.24/1.95  #BackRed      : 1
% 5.24/1.95  
% 5.24/1.95  #Partial instantiations: 0
% 5.24/1.95  #Strategies tried      : 1
% 5.24/1.95  
% 5.24/1.95  Timing (in seconds)
% 5.24/1.95  ----------------------
% 5.24/1.95  Preprocessing        : 0.28
% 5.24/1.95  Parsing              : 0.15
% 5.24/1.95  CNF conversion       : 0.01
% 5.24/1.95  Main loop            : 0.91
% 5.24/1.95  Inferencing          : 0.37
% 5.24/1.95  Reduction            : 0.36
% 5.24/1.95  Demodulation         : 0.31
% 5.24/1.95  BG Simplification    : 0.05
% 5.24/1.95  Subsumption          : 0.10
% 5.24/1.95  Abstraction          : 0.08
% 5.24/1.95  MUC search           : 0.00
% 5.24/1.95  Cooper               : 0.00
% 5.24/1.95  Total                : 1.22
% 5.24/1.95  Index Insertion      : 0.00
% 5.24/1.95  Index Deletion       : 0.00
% 5.24/1.95  Index Matching       : 0.00
% 5.24/1.95  BG Taut test         : 0.00
%------------------------------------------------------------------------------
