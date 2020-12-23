%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:13 EST 2020

% Result     : Theorem 1.44s
% Output     : CNFRefutation 1.54s
% Verified   : 
% Statistics : Number of formulae       :   23 (  26 expanded)
%              Number of leaves         :   16 (  18 expanded)
%              Depth                    :    4
%              Number of atoms          :   15 (  19 expanded)
%              Number of equality atoms :   14 (  18 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_27,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k2_xboole_0(A,B),C) = k2_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
      & k2_zfmisc_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).

tff(f_36,negated_conjecture,(
    ~ ! [A,B,C] :
        ( k2_zfmisc_1(k2_tarski(A,B),C) = k2_xboole_0(k2_zfmisc_1(k1_tarski(A),C),k2_zfmisc_1(k1_tarski(B),C))
        & k2_zfmisc_1(C,k2_tarski(A,B)) = k2_xboole_0(k2_zfmisc_1(C,k1_tarski(A)),k2_zfmisc_1(C,k1_tarski(B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_zfmisc_1)).

tff(c_2,plain,(
    ! [A_1,B_2] : k2_xboole_0(k1_tarski(A_1),k1_tarski(B_2)) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] : k2_xboole_0(k2_zfmisc_1(A_3,C_5),k2_zfmisc_1(B_4,C_5)) = k2_zfmisc_1(k2_xboole_0(A_3,B_4),C_5) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6,plain,(
    ! [C_5,A_3,B_4] : k2_xboole_0(k2_zfmisc_1(C_5,A_3),k2_zfmisc_1(C_5,B_4)) = k2_zfmisc_1(C_5,k2_xboole_0(A_3,B_4)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,
    ( k2_xboole_0(k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_6'),k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_6')) != k2_zfmisc_1(k2_tarski('#skF_4','#skF_5'),'#skF_6')
    | k2_xboole_0(k2_zfmisc_1('#skF_3',k1_tarski('#skF_1')),k2_zfmisc_1('#skF_3',k1_tarski('#skF_2'))) != k2_zfmisc_1('#skF_3',k2_tarski('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_9,plain,
    ( k2_xboole_0(k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_6'),k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_6')) != k2_zfmisc_1(k2_tarski('#skF_4','#skF_5'),'#skF_6')
    | k2_zfmisc_1('#skF_3',k2_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2'))) != k2_zfmisc_1('#skF_3',k2_tarski('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8])).

tff(c_10,plain,
    ( k2_zfmisc_1(k2_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_5')),'#skF_6') != k2_zfmisc_1(k2_tarski('#skF_4','#skF_5'),'#skF_6')
    | k2_zfmisc_1('#skF_3',k2_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2'))) != k2_zfmisc_1('#skF_3',k2_tarski('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_9])).

tff(c_12,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:41:24 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.44/1.02  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.44/1.02  
% 1.44/1.02  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.54/1.03  %$ k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.54/1.03  
% 1.54/1.03  %Foreground sorts:
% 1.54/1.03  
% 1.54/1.03  
% 1.54/1.03  %Background operators:
% 1.54/1.03  
% 1.54/1.03  
% 1.54/1.03  %Foreground operators:
% 1.54/1.03  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.54/1.03  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.54/1.03  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.54/1.03  tff('#skF_5', type, '#skF_5': $i).
% 1.54/1.03  tff('#skF_6', type, '#skF_6': $i).
% 1.54/1.03  tff('#skF_2', type, '#skF_2': $i).
% 1.54/1.03  tff('#skF_3', type, '#skF_3': $i).
% 1.54/1.03  tff('#skF_1', type, '#skF_1': $i).
% 1.54/1.03  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.54/1.03  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.54/1.03  tff('#skF_4', type, '#skF_4': $i).
% 1.54/1.03  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.54/1.03  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.54/1.03  
% 1.54/1.04  tff(f_27, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 1.54/1.04  tff(f_31, axiom, (![A, B, C]: ((k2_zfmisc_1(k2_xboole_0(A, B), C) = k2_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C))) & (k2_zfmisc_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t120_zfmisc_1)).
% 1.54/1.04  tff(f_36, negated_conjecture, ~(![A, B, C]: ((k2_zfmisc_1(k2_tarski(A, B), C) = k2_xboole_0(k2_zfmisc_1(k1_tarski(A), C), k2_zfmisc_1(k1_tarski(B), C))) & (k2_zfmisc_1(C, k2_tarski(A, B)) = k2_xboole_0(k2_zfmisc_1(C, k1_tarski(A)), k2_zfmisc_1(C, k1_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t132_zfmisc_1)).
% 1.54/1.04  tff(c_2, plain, (![A_1, B_2]: (k2_xboole_0(k1_tarski(A_1), k1_tarski(B_2))=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.54/1.04  tff(c_4, plain, (![A_3, C_5, B_4]: (k2_xboole_0(k2_zfmisc_1(A_3, C_5), k2_zfmisc_1(B_4, C_5))=k2_zfmisc_1(k2_xboole_0(A_3, B_4), C_5))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.54/1.04  tff(c_6, plain, (![C_5, A_3, B_4]: (k2_xboole_0(k2_zfmisc_1(C_5, A_3), k2_zfmisc_1(C_5, B_4))=k2_zfmisc_1(C_5, k2_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.54/1.04  tff(c_8, plain, (k2_xboole_0(k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_5'), '#skF_6'))!=k2_zfmisc_1(k2_tarski('#skF_4', '#skF_5'), '#skF_6') | k2_xboole_0(k2_zfmisc_1('#skF_3', k1_tarski('#skF_1')), k2_zfmisc_1('#skF_3', k1_tarski('#skF_2')))!=k2_zfmisc_1('#skF_3', k2_tarski('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.54/1.04  tff(c_9, plain, (k2_xboole_0(k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_5'), '#skF_6'))!=k2_zfmisc_1(k2_tarski('#skF_4', '#skF_5'), '#skF_6') | k2_zfmisc_1('#skF_3', k2_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2')))!=k2_zfmisc_1('#skF_3', k2_tarski('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_8])).
% 1.54/1.04  tff(c_10, plain, (k2_zfmisc_1(k2_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_5')), '#skF_6')!=k2_zfmisc_1(k2_tarski('#skF_4', '#skF_5'), '#skF_6') | k2_zfmisc_1('#skF_3', k2_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2')))!=k2_zfmisc_1('#skF_3', k2_tarski('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_9])).
% 1.54/1.04  tff(c_12, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_2, c_10])).
% 1.54/1.04  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.54/1.04  
% 1.54/1.04  Inference rules
% 1.54/1.04  ----------------------
% 1.54/1.04  #Ref     : 0
% 1.54/1.04  #Sup     : 0
% 1.54/1.04  #Fact    : 0
% 1.54/1.04  #Define  : 0
% 1.54/1.04  #Split   : 0
% 1.54/1.04  #Chain   : 0
% 1.54/1.04  #Close   : 0
% 1.54/1.04  
% 1.54/1.04  Ordering : KBO
% 1.54/1.04  
% 1.54/1.04  Simplification rules
% 1.54/1.04  ----------------------
% 1.54/1.04  #Subsume      : 3
% 1.54/1.04  #Demod        : 4
% 1.54/1.04  #Tautology    : 0
% 1.54/1.04  #SimpNegUnit  : 0
% 1.54/1.04  #BackRed      : 0
% 1.54/1.04  
% 1.54/1.04  #Partial instantiations: 0
% 1.54/1.04  #Strategies tried      : 1
% 1.54/1.04  
% 1.54/1.04  Timing (in seconds)
% 1.54/1.04  ----------------------
% 1.54/1.04  Preprocessing        : 0.25
% 1.54/1.04  Parsing              : 0.14
% 1.54/1.04  CNF conversion       : 0.01
% 1.54/1.04  Main loop            : 0.03
% 1.54/1.04  Inferencing          : 0.00
% 1.54/1.04  Reduction            : 0.02
% 1.54/1.04  Demodulation         : 0.02
% 1.54/1.04  BG Simplification    : 0.01
% 1.54/1.04  Subsumption          : 0.01
% 1.54/1.04  Abstraction          : 0.00
% 1.54/1.04  MUC search           : 0.00
% 1.54/1.04  Cooper               : 0.00
% 1.54/1.04  Total                : 0.31
% 1.54/1.04  Index Insertion      : 0.00
% 1.54/1.04  Index Deletion       : 0.00
% 1.54/1.04  Index Matching       : 0.00
% 1.54/1.04  BG Taut test         : 0.00
%------------------------------------------------------------------------------
