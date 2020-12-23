%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:51 EST 2020

% Result     : Theorem 6.19s
% Output     : CNFRefutation 6.19s
% Verified   : 
% Statistics : Number of formulae       :   26 (  27 expanded)
%              Number of leaves         :   17 (  18 expanded)
%              Depth                    :    4
%              Number of atoms          :   15 (  17 expanded)
%              Number of equality atoms :   14 (  16 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k2_enumset1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_37,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k1_tarski(A),k2_tarski(B,C)) = k2_tarski(k4_tarski(A,B),k4_tarski(A,C))
      & k2_zfmisc_1(k2_tarski(A,B),k1_tarski(C)) = k2_tarski(k4_tarski(A,C),k4_tarski(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k2_tarski(A,B),C) = k2_xboole_0(k2_zfmisc_1(k1_tarski(A),C),k2_zfmisc_1(k1_tarski(B),C))
      & k2_zfmisc_1(C,k2_tarski(A,B)) = k2_xboole_0(k2_zfmisc_1(C,k1_tarski(A)),k2_zfmisc_1(C,k1_tarski(B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_zfmisc_1)).

tff(f_40,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_zfmisc_1(k2_tarski(A,B),k2_tarski(C,D)) = k2_enumset1(k4_tarski(A,C),k4_tarski(A,D),k4_tarski(B,C),k4_tarski(B,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_zfmisc_1)).

tff(c_33,plain,(
    ! [A_19,B_20,C_21] : k2_zfmisc_1(k1_tarski(A_19),k2_tarski(B_20,C_21)) = k2_tarski(k4_tarski(A_19,B_20),k4_tarski(A_19,C_21)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3,D_4] : k2_xboole_0(k2_tarski(A_1,B_2),k2_tarski(C_3,D_4)) = k2_enumset1(A_1,B_2,C_3,D_4) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_45,plain,(
    ! [A_19,C_3,D_4,C_21,B_20] : k2_xboole_0(k2_zfmisc_1(k1_tarski(A_19),k2_tarski(B_20,C_21)),k2_tarski(C_3,D_4)) = k2_enumset1(k4_tarski(A_19,B_20),k4_tarski(A_19,C_21),C_3,D_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_33,c_2])).

tff(c_10,plain,(
    ! [A_10,B_11,C_12] : k2_zfmisc_1(k1_tarski(A_10),k2_tarski(B_11,C_12)) = k2_tarski(k4_tarski(A_10,B_11),k4_tarski(A_10,C_12)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_173,plain,(
    ! [A_30,C_31,B_32] : k2_xboole_0(k2_zfmisc_1(k1_tarski(A_30),C_31),k2_zfmisc_1(k1_tarski(B_32),C_31)) = k2_zfmisc_1(k2_tarski(A_30,B_32),C_31) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2630,plain,(
    ! [A_108,B_109,C_110,A_111] : k2_xboole_0(k2_zfmisc_1(k1_tarski(A_108),k2_tarski(B_109,C_110)),k2_tarski(k4_tarski(A_111,B_109),k4_tarski(A_111,C_110))) = k2_zfmisc_1(k2_tarski(A_108,A_111),k2_tarski(B_109,C_110)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_173])).

tff(c_2675,plain,(
    ! [A_19,B_20,C_21,A_111] : k2_enumset1(k4_tarski(A_19,B_20),k4_tarski(A_19,C_21),k4_tarski(A_111,B_20),k4_tarski(A_111,C_21)) = k2_zfmisc_1(k2_tarski(A_19,A_111),k2_tarski(B_20,C_21)) ),
    inference(superposition,[status(thm),theory(equality)],[c_45,c_2630])).

tff(c_14,plain,(
    k2_enumset1(k4_tarski('#skF_1','#skF_3'),k4_tarski('#skF_1','#skF_4'),k4_tarski('#skF_2','#skF_3'),k4_tarski('#skF_2','#skF_4')) != k2_zfmisc_1(k2_tarski('#skF_1','#skF_2'),k2_tarski('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_3101,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2675,c_14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:16:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.19/2.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.19/2.18  
% 6.19/2.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.19/2.18  %$ k2_enumset1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.19/2.18  
% 6.19/2.18  %Foreground sorts:
% 6.19/2.18  
% 6.19/2.18  
% 6.19/2.18  %Background operators:
% 6.19/2.18  
% 6.19/2.18  
% 6.19/2.18  %Foreground operators:
% 6.19/2.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.19/2.18  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.19/2.18  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 6.19/2.18  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.19/2.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.19/2.18  tff('#skF_2', type, '#skF_2': $i).
% 6.19/2.18  tff('#skF_3', type, '#skF_3': $i).
% 6.19/2.18  tff('#skF_1', type, '#skF_1': $i).
% 6.19/2.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.19/2.18  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.19/2.18  tff('#skF_4', type, '#skF_4': $i).
% 6.19/2.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.19/2.18  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.19/2.18  
% 6.19/2.19  tff(f_37, axiom, (![A, B, C]: ((k2_zfmisc_1(k1_tarski(A), k2_tarski(B, C)) = k2_tarski(k4_tarski(A, B), k4_tarski(A, C))) & (k2_zfmisc_1(k2_tarski(A, B), k1_tarski(C)) = k2_tarski(k4_tarski(A, C), k4_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_zfmisc_1)).
% 6.19/2.19  tff(f_27, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l53_enumset1)).
% 6.19/2.19  tff(f_33, axiom, (![A, B, C]: ((k2_zfmisc_1(k2_tarski(A, B), C) = k2_xboole_0(k2_zfmisc_1(k1_tarski(A), C), k2_zfmisc_1(k1_tarski(B), C))) & (k2_zfmisc_1(C, k2_tarski(A, B)) = k2_xboole_0(k2_zfmisc_1(C, k1_tarski(A)), k2_zfmisc_1(C, k1_tarski(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t132_zfmisc_1)).
% 6.19/2.19  tff(f_40, negated_conjecture, ~(![A, B, C, D]: (k2_zfmisc_1(k2_tarski(A, B), k2_tarski(C, D)) = k2_enumset1(k4_tarski(A, C), k4_tarski(A, D), k4_tarski(B, C), k4_tarski(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_zfmisc_1)).
% 6.19/2.19  tff(c_33, plain, (![A_19, B_20, C_21]: (k2_zfmisc_1(k1_tarski(A_19), k2_tarski(B_20, C_21))=k2_tarski(k4_tarski(A_19, B_20), k4_tarski(A_19, C_21)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.19/2.19  tff(c_2, plain, (![A_1, B_2, C_3, D_4]: (k2_xboole_0(k2_tarski(A_1, B_2), k2_tarski(C_3, D_4))=k2_enumset1(A_1, B_2, C_3, D_4))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.19/2.19  tff(c_45, plain, (![A_19, C_3, D_4, C_21, B_20]: (k2_xboole_0(k2_zfmisc_1(k1_tarski(A_19), k2_tarski(B_20, C_21)), k2_tarski(C_3, D_4))=k2_enumset1(k4_tarski(A_19, B_20), k4_tarski(A_19, C_21), C_3, D_4))), inference(superposition, [status(thm), theory('equality')], [c_33, c_2])).
% 6.19/2.19  tff(c_10, plain, (![A_10, B_11, C_12]: (k2_zfmisc_1(k1_tarski(A_10), k2_tarski(B_11, C_12))=k2_tarski(k4_tarski(A_10, B_11), k4_tarski(A_10, C_12)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.19/2.19  tff(c_173, plain, (![A_30, C_31, B_32]: (k2_xboole_0(k2_zfmisc_1(k1_tarski(A_30), C_31), k2_zfmisc_1(k1_tarski(B_32), C_31))=k2_zfmisc_1(k2_tarski(A_30, B_32), C_31))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.19/2.19  tff(c_2630, plain, (![A_108, B_109, C_110, A_111]: (k2_xboole_0(k2_zfmisc_1(k1_tarski(A_108), k2_tarski(B_109, C_110)), k2_tarski(k4_tarski(A_111, B_109), k4_tarski(A_111, C_110)))=k2_zfmisc_1(k2_tarski(A_108, A_111), k2_tarski(B_109, C_110)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_173])).
% 6.19/2.19  tff(c_2675, plain, (![A_19, B_20, C_21, A_111]: (k2_enumset1(k4_tarski(A_19, B_20), k4_tarski(A_19, C_21), k4_tarski(A_111, B_20), k4_tarski(A_111, C_21))=k2_zfmisc_1(k2_tarski(A_19, A_111), k2_tarski(B_20, C_21)))), inference(superposition, [status(thm), theory('equality')], [c_45, c_2630])).
% 6.19/2.19  tff(c_14, plain, (k2_enumset1(k4_tarski('#skF_1', '#skF_3'), k4_tarski('#skF_1', '#skF_4'), k4_tarski('#skF_2', '#skF_3'), k4_tarski('#skF_2', '#skF_4'))!=k2_zfmisc_1(k2_tarski('#skF_1', '#skF_2'), k2_tarski('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.19/2.19  tff(c_3101, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2675, c_14])).
% 6.19/2.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.19/2.19  
% 6.19/2.19  Inference rules
% 6.19/2.19  ----------------------
% 6.19/2.19  #Ref     : 0
% 6.19/2.19  #Sup     : 852
% 6.19/2.19  #Fact    : 0
% 6.19/2.19  #Define  : 0
% 6.19/2.19  #Split   : 0
% 6.19/2.19  #Chain   : 0
% 6.19/2.19  #Close   : 0
% 6.19/2.19  
% 6.19/2.19  Ordering : KBO
% 6.19/2.19  
% 6.19/2.19  Simplification rules
% 6.19/2.19  ----------------------
% 6.19/2.19  #Subsume      : 157
% 6.19/2.19  #Demod        : 53
% 6.19/2.19  #Tautology    : 147
% 6.19/2.19  #SimpNegUnit  : 0
% 6.19/2.19  #BackRed      : 1
% 6.19/2.19  
% 6.19/2.19  #Partial instantiations: 0
% 6.19/2.19  #Strategies tried      : 1
% 6.19/2.19  
% 6.19/2.19  Timing (in seconds)
% 6.19/2.19  ----------------------
% 6.19/2.19  Preprocessing        : 0.27
% 6.19/2.19  Parsing              : 0.15
% 6.19/2.19  CNF conversion       : 0.01
% 6.19/2.19  Main loop            : 1.16
% 6.19/2.19  Inferencing          : 0.43
% 6.19/2.19  Reduction            : 0.48
% 6.19/2.19  Demodulation         : 0.43
% 6.19/2.19  BG Simplification    : 0.07
% 6.19/2.19  Subsumption          : 0.13
% 6.19/2.19  Abstraction          : 0.09
% 6.19/2.19  MUC search           : 0.00
% 6.19/2.19  Cooper               : 0.00
% 6.19/2.19  Total                : 1.46
% 6.19/2.19  Index Insertion      : 0.00
% 6.19/2.19  Index Deletion       : 0.00
% 6.19/2.19  Index Matching       : 0.00
% 6.19/2.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
