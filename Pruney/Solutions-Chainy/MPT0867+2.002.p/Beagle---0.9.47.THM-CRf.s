%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:23 EST 2020

% Result     : Theorem 4.96s
% Output     : CNFRefutation 4.96s
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k2_tarski(A,B),C) = k2_xboole_0(k2_zfmisc_1(k1_tarski(A),C),k2_zfmisc_1(k1_tarski(B),C))
      & k2_zfmisc_1(C,k2_tarski(A,B)) = k2_xboole_0(k2_zfmisc_1(C,k1_tarski(A)),k2_zfmisc_1(C,k1_tarski(B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_42,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_zfmisc_1(k2_tarski(A,B),k2_tarski(C,D)) = k2_enumset1(k4_tarski(A,C),k4_tarski(A,D),k4_tarski(B,C),k4_tarski(B,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_mcart_1)).

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
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:53:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.96/1.96  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.96/1.96  
% 4.96/1.96  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.96/1.96  %$ k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.96/1.96  
% 4.96/1.96  %Foreground sorts:
% 4.96/1.96  
% 4.96/1.96  
% 4.96/1.96  %Background operators:
% 4.96/1.96  
% 4.96/1.96  
% 4.96/1.96  %Foreground operators:
% 4.96/1.96  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.96/1.96  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.96/1.96  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.96/1.96  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.96/1.96  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.96/1.96  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.96/1.96  tff('#skF_2', type, '#skF_2': $i).
% 4.96/1.96  tff('#skF_3', type, '#skF_3': $i).
% 4.96/1.96  tff('#skF_1', type, '#skF_1': $i).
% 4.96/1.96  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.96/1.96  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.96/1.96  tff('#skF_4', type, '#skF_4': $i).
% 4.96/1.96  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.96/1.96  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.96/1.96  
% 4.96/1.97  tff(f_39, axiom, (![A, B, C]: ((k2_zfmisc_1(k1_tarski(A), k2_tarski(B, C)) = k2_tarski(k4_tarski(A, B), k4_tarski(A, C))) & (k2_zfmisc_1(k2_tarski(A, B), k1_tarski(C)) = k2_tarski(k4_tarski(A, C), k4_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_zfmisc_1)).
% 4.96/1.97  tff(f_35, axiom, (![A, B, C]: ((k2_zfmisc_1(k2_tarski(A, B), C) = k2_xboole_0(k2_zfmisc_1(k1_tarski(A), C), k2_zfmisc_1(k1_tarski(B), C))) & (k2_zfmisc_1(C, k2_tarski(A, B)) = k2_xboole_0(k2_zfmisc_1(C, k1_tarski(A)), k2_zfmisc_1(C, k1_tarski(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t132_zfmisc_1)).
% 4.96/1.97  tff(f_27, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l53_enumset1)).
% 4.96/1.97  tff(f_42, negated_conjecture, ~(![A, B, C, D]: (k2_zfmisc_1(k2_tarski(A, B), k2_tarski(C, D)) = k2_enumset1(k4_tarski(A, C), k4_tarski(A, D), k4_tarski(B, C), k4_tarski(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_mcart_1)).
% 4.96/1.97  tff(c_12, plain, (![A_11, B_12, C_13]: (k2_zfmisc_1(k1_tarski(A_11), k2_tarski(B_12, C_13))=k2_tarski(k4_tarski(A_11, B_12), k4_tarski(A_11, C_13)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.96/1.97  tff(c_260, plain, (![A_37, C_38, B_39]: (k2_xboole_0(k2_zfmisc_1(k1_tarski(A_37), C_38), k2_zfmisc_1(k1_tarski(B_39), C_38))=k2_zfmisc_1(k2_tarski(A_37, B_39), C_38))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.96/1.97  tff(c_2804, plain, (![A_141, B_142, C_143, B_144]: (k2_xboole_0(k2_tarski(k4_tarski(A_141, B_142), k4_tarski(A_141, C_143)), k2_zfmisc_1(k1_tarski(B_144), k2_tarski(B_142, C_143)))=k2_zfmisc_1(k2_tarski(A_141, B_144), k2_tarski(B_142, C_143)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_260])).
% 4.96/1.97  tff(c_96, plain, (![A_26, B_27, C_28]: (k2_zfmisc_1(k1_tarski(A_26), k2_tarski(B_27, C_28))=k2_tarski(k4_tarski(A_26, B_27), k4_tarski(A_26, C_28)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.96/1.97  tff(c_2, plain, (![A_1, B_2, C_3, D_4]: (k2_xboole_0(k2_tarski(A_1, B_2), k2_tarski(C_3, D_4))=k2_enumset1(A_1, B_2, C_3, D_4))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.96/1.97  tff(c_114, plain, (![B_27, B_2, A_1, A_26, C_28]: (k2_xboole_0(k2_tarski(A_1, B_2), k2_zfmisc_1(k1_tarski(A_26), k2_tarski(B_27, C_28)))=k2_enumset1(A_1, B_2, k4_tarski(A_26, B_27), k4_tarski(A_26, C_28)))), inference(superposition, [status(thm), theory('equality')], [c_96, c_2])).
% 4.96/1.97  tff(c_2810, plain, (![A_141, B_142, C_143, B_144]: (k2_enumset1(k4_tarski(A_141, B_142), k4_tarski(A_141, C_143), k4_tarski(B_144, B_142), k4_tarski(B_144, C_143))=k2_zfmisc_1(k2_tarski(A_141, B_144), k2_tarski(B_142, C_143)))), inference(superposition, [status(thm), theory('equality')], [c_2804, c_114])).
% 4.96/1.97  tff(c_16, plain, (k2_enumset1(k4_tarski('#skF_1', '#skF_3'), k4_tarski('#skF_1', '#skF_4'), k4_tarski('#skF_2', '#skF_3'), k4_tarski('#skF_2', '#skF_4'))!=k2_zfmisc_1(k2_tarski('#skF_1', '#skF_2'), k2_tarski('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.96/1.97  tff(c_2884, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2810, c_16])).
% 4.96/1.97  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.96/1.97  
% 4.96/1.97  Inference rules
% 4.96/1.97  ----------------------
% 4.96/1.97  #Ref     : 0
% 4.96/1.97  #Sup     : 744
% 4.96/1.97  #Fact    : 0
% 4.96/1.97  #Define  : 0
% 4.96/1.97  #Split   : 0
% 4.96/1.97  #Chain   : 0
% 4.96/1.97  #Close   : 0
% 4.96/1.97  
% 4.96/1.97  Ordering : KBO
% 4.96/1.97  
% 4.96/1.97  Simplification rules
% 4.96/1.97  ----------------------
% 4.96/1.97  #Subsume      : 71
% 4.96/1.97  #Demod        : 591
% 4.96/1.97  #Tautology    : 338
% 4.96/1.97  #SimpNegUnit  : 0
% 4.96/1.97  #BackRed      : 1
% 4.96/1.97  
% 4.96/1.97  #Partial instantiations: 0
% 4.96/1.97  #Strategies tried      : 1
% 4.96/1.97  
% 4.96/1.97  Timing (in seconds)
% 4.96/1.97  ----------------------
% 4.96/1.97  Preprocessing        : 0.28
% 4.96/1.97  Parsing              : 0.15
% 4.96/1.97  CNF conversion       : 0.01
% 4.96/1.97  Main loop            : 0.92
% 4.96/1.97  Inferencing          : 0.38
% 4.96/1.97  Reduction            : 0.36
% 4.96/1.97  Demodulation         : 0.31
% 4.96/1.97  BG Simplification    : 0.05
% 4.96/1.97  Subsumption          : 0.10
% 4.96/1.97  Abstraction          : 0.08
% 4.96/1.97  MUC search           : 0.00
% 4.96/1.97  Cooper               : 0.00
% 4.96/1.97  Total                : 1.23
% 4.96/1.97  Index Insertion      : 0.00
% 4.96/1.97  Index Deletion       : 0.00
% 4.96/1.97  Index Matching       : 0.00
% 4.96/1.97  BG Taut test         : 0.00
%------------------------------------------------------------------------------
