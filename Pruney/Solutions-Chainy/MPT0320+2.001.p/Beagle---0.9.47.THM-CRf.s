%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:12 EST 2020

% Result     : Theorem 1.78s
% Output     : CNFRefutation 1.83s
% Verified   : 
% Statistics : Number of formulae       :   31 (  40 expanded)
%              Number of leaves         :   20 (  24 expanded)
%              Depth                    :    4
%              Number of atoms          :   21 (  31 expanded)
%              Number of equality atoms :   20 (  30 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k1_enumset1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(f_31,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_29,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k2_tarski(A,B),k1_tarski(C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k2_xboole_0(A,B),C) = k2_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
      & k2_zfmisc_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_zfmisc_1)).

tff(f_42,negated_conjecture,(
    ~ ! [A,B,C] :
        ( k2_zfmisc_1(k2_tarski(A,B),C) = k2_xboole_0(k2_zfmisc_1(k1_tarski(A),C),k2_zfmisc_1(k1_tarski(B),C))
        & k2_zfmisc_1(C,k2_tarski(A,B)) = k2_xboole_0(k2_zfmisc_1(C,k1_tarski(A)),k2_zfmisc_1(C,k1_tarski(B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_zfmisc_1)).

tff(c_6,plain,(
    ! [A_5,B_6] : k1_enumset1(A_5,A_5,B_6) = k2_tarski(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_4] : k2_tarski(A_4,A_4) = k1_tarski(A_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_64,plain,(
    ! [A_18,B_19,C_20] : k2_xboole_0(k2_tarski(A_18,B_19),k1_tarski(C_20)) = k1_enumset1(A_18,B_19,C_20) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_73,plain,(
    ! [A_4,C_20] : k2_xboole_0(k1_tarski(A_4),k1_tarski(C_20)) = k1_enumset1(A_4,A_4,C_20) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_64])).

tff(c_76,plain,(
    ! [A_4,C_20] : k2_xboole_0(k1_tarski(A_4),k1_tarski(C_20)) = k2_tarski(A_4,C_20) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_73])).

tff(c_10,plain,(
    ! [A_9,C_11,B_10] : k2_xboole_0(k2_zfmisc_1(A_9,C_11),k2_zfmisc_1(B_10,C_11)) = k2_zfmisc_1(k2_xboole_0(A_9,B_10),C_11) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_12,plain,(
    ! [C_11,A_9,B_10] : k2_xboole_0(k2_zfmisc_1(C_11,A_9),k2_zfmisc_1(C_11,B_10)) = k2_zfmisc_1(C_11,k2_xboole_0(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,
    ( k2_xboole_0(k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_6'),k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_6')) != k2_zfmisc_1(k2_tarski('#skF_4','#skF_5'),'#skF_6')
    | k2_xboole_0(k2_zfmisc_1('#skF_3',k1_tarski('#skF_1')),k2_zfmisc_1('#skF_3',k1_tarski('#skF_2'))) != k2_zfmisc_1('#skF_3',k2_tarski('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_15,plain,
    ( k2_xboole_0(k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_6'),k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_6')) != k2_zfmisc_1(k2_tarski('#skF_4','#skF_5'),'#skF_6')
    | k2_zfmisc_1('#skF_3',k2_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2'))) != k2_zfmisc_1('#skF_3',k2_tarski('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_14])).

tff(c_16,plain,
    ( k2_zfmisc_1(k2_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_5')),'#skF_6') != k2_zfmisc_1(k2_tarski('#skF_4','#skF_5'),'#skF_6')
    | k2_zfmisc_1('#skF_3',k2_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2'))) != k2_zfmisc_1('#skF_3',k2_tarski('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_15])).

tff(c_124,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_76,c_16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n008.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:06:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.78/1.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.78/1.17  
% 1.78/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.78/1.17  %$ k1_enumset1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.78/1.17  
% 1.78/1.17  %Foreground sorts:
% 1.78/1.17  
% 1.78/1.17  
% 1.78/1.17  %Background operators:
% 1.78/1.17  
% 1.78/1.17  
% 1.78/1.17  %Foreground operators:
% 1.78/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.78/1.17  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.78/1.17  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.78/1.17  tff('#skF_5', type, '#skF_5': $i).
% 1.78/1.17  tff('#skF_6', type, '#skF_6': $i).
% 1.78/1.17  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.78/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.78/1.17  tff('#skF_3', type, '#skF_3': $i).
% 1.78/1.17  tff('#skF_1', type, '#skF_1': $i).
% 1.78/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.78/1.17  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.78/1.17  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.78/1.17  tff('#skF_4', type, '#skF_4': $i).
% 1.78/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.78/1.17  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.78/1.17  
% 1.83/1.18  tff(f_31, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 1.83/1.18  tff(f_29, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.83/1.18  tff(f_27, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k2_tarski(A, B), k1_tarski(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_enumset1)).
% 1.83/1.18  tff(f_37, axiom, (![A, B, C]: ((k2_zfmisc_1(k2_xboole_0(A, B), C) = k2_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C))) & (k2_zfmisc_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t120_zfmisc_1)).
% 1.83/1.18  tff(f_42, negated_conjecture, ~(![A, B, C]: ((k2_zfmisc_1(k2_tarski(A, B), C) = k2_xboole_0(k2_zfmisc_1(k1_tarski(A), C), k2_zfmisc_1(k1_tarski(B), C))) & (k2_zfmisc_1(C, k2_tarski(A, B)) = k2_xboole_0(k2_zfmisc_1(C, k1_tarski(A)), k2_zfmisc_1(C, k1_tarski(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t132_zfmisc_1)).
% 1.83/1.18  tff(c_6, plain, (![A_5, B_6]: (k1_enumset1(A_5, A_5, B_6)=k2_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.83/1.18  tff(c_4, plain, (![A_4]: (k2_tarski(A_4, A_4)=k1_tarski(A_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.83/1.18  tff(c_64, plain, (![A_18, B_19, C_20]: (k2_xboole_0(k2_tarski(A_18, B_19), k1_tarski(C_20))=k1_enumset1(A_18, B_19, C_20))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.83/1.18  tff(c_73, plain, (![A_4, C_20]: (k2_xboole_0(k1_tarski(A_4), k1_tarski(C_20))=k1_enumset1(A_4, A_4, C_20))), inference(superposition, [status(thm), theory('equality')], [c_4, c_64])).
% 1.83/1.18  tff(c_76, plain, (![A_4, C_20]: (k2_xboole_0(k1_tarski(A_4), k1_tarski(C_20))=k2_tarski(A_4, C_20))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_73])).
% 1.83/1.18  tff(c_10, plain, (![A_9, C_11, B_10]: (k2_xboole_0(k2_zfmisc_1(A_9, C_11), k2_zfmisc_1(B_10, C_11))=k2_zfmisc_1(k2_xboole_0(A_9, B_10), C_11))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.83/1.18  tff(c_12, plain, (![C_11, A_9, B_10]: (k2_xboole_0(k2_zfmisc_1(C_11, A_9), k2_zfmisc_1(C_11, B_10))=k2_zfmisc_1(C_11, k2_xboole_0(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.83/1.18  tff(c_14, plain, (k2_xboole_0(k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_5'), '#skF_6'))!=k2_zfmisc_1(k2_tarski('#skF_4', '#skF_5'), '#skF_6') | k2_xboole_0(k2_zfmisc_1('#skF_3', k1_tarski('#skF_1')), k2_zfmisc_1('#skF_3', k1_tarski('#skF_2')))!=k2_zfmisc_1('#skF_3', k2_tarski('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.83/1.18  tff(c_15, plain, (k2_xboole_0(k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_5'), '#skF_6'))!=k2_zfmisc_1(k2_tarski('#skF_4', '#skF_5'), '#skF_6') | k2_zfmisc_1('#skF_3', k2_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2')))!=k2_zfmisc_1('#skF_3', k2_tarski('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_14])).
% 1.83/1.18  tff(c_16, plain, (k2_zfmisc_1(k2_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_5')), '#skF_6')!=k2_zfmisc_1(k2_tarski('#skF_4', '#skF_5'), '#skF_6') | k2_zfmisc_1('#skF_3', k2_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2')))!=k2_zfmisc_1('#skF_3', k2_tarski('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_15])).
% 1.83/1.18  tff(c_124, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_76, c_16])).
% 1.83/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.83/1.18  
% 1.83/1.18  Inference rules
% 1.83/1.18  ----------------------
% 1.83/1.18  #Ref     : 0
% 1.83/1.18  #Sup     : 24
% 1.83/1.18  #Fact    : 0
% 1.83/1.18  #Define  : 0
% 1.83/1.18  #Split   : 0
% 1.83/1.18  #Chain   : 0
% 1.83/1.18  #Close   : 0
% 1.83/1.18  
% 1.83/1.18  Ordering : KBO
% 1.83/1.18  
% 1.83/1.18  Simplification rules
% 1.83/1.18  ----------------------
% 1.83/1.18  #Subsume      : 0
% 1.83/1.18  #Demod        : 8
% 1.83/1.18  #Tautology    : 19
% 1.83/1.18  #SimpNegUnit  : 0
% 1.83/1.18  #BackRed      : 0
% 1.83/1.18  
% 1.83/1.18  #Partial instantiations: 0
% 1.83/1.18  #Strategies tried      : 1
% 1.83/1.18  
% 1.83/1.18  Timing (in seconds)
% 1.83/1.18  ----------------------
% 1.83/1.18  Preprocessing        : 0.29
% 1.83/1.18  Parsing              : 0.16
% 1.83/1.18  CNF conversion       : 0.02
% 1.83/1.18  Main loop            : 0.10
% 1.83/1.18  Inferencing          : 0.04
% 1.83/1.18  Reduction            : 0.03
% 1.83/1.18  Demodulation         : 0.03
% 1.83/1.18  BG Simplification    : 0.01
% 1.83/1.18  Subsumption          : 0.01
% 1.83/1.18  Abstraction          : 0.01
% 1.83/1.18  MUC search           : 0.00
% 1.83/1.18  Cooper               : 0.00
% 1.83/1.18  Total                : 0.41
% 1.83/1.18  Index Insertion      : 0.00
% 1.83/1.19  Index Deletion       : 0.00
% 1.83/1.19  Index Matching       : 0.00
% 1.83/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
