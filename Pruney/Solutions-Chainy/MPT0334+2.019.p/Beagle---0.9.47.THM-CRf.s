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
% DateTime   : Thu Dec  3 09:54:53 EST 2020

% Result     : Theorem 1.65s
% Output     : CNFRefutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :   21 (  22 expanded)
%              Number of leaves         :   14 (  15 expanded)
%              Depth                    :    4
%              Number of atoms          :   14 (  16 expanded)
%              Number of equality atoms :   13 (  15 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_42,negated_conjecture,(
    ~ ! [A,B,C] :
        ( A != B
       => k4_xboole_0(k2_xboole_0(C,k1_tarski(A)),k1_tarski(B)) = k2_xboole_0(k4_xboole_0(C,k1_tarski(B)),k1_tarski(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_zfmisc_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B,C] : k4_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(k4_xboole_0(A,C),k4_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_xboole_1)).

tff(c_14,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( k4_xboole_0(k1_tarski(A_7),k1_tarski(B_8)) = k1_tarski(A_7)
      | B_8 = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_53,plain,(
    ! [A_15,C_16,B_17] : k2_xboole_0(k4_xboole_0(A_15,C_16),k4_xboole_0(B_17,C_16)) = k4_xboole_0(k2_xboole_0(A_15,B_17),C_16) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_95,plain,(
    ! [A_23,A_24,B_25] :
      ( k4_xboole_0(k2_xboole_0(A_23,k1_tarski(A_24)),k1_tarski(B_25)) = k2_xboole_0(k4_xboole_0(A_23,k1_tarski(B_25)),k1_tarski(A_24))
      | B_25 = A_24 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_53])).

tff(c_12,plain,(
    k4_xboole_0(k2_xboole_0('#skF_3',k1_tarski('#skF_1')),k1_tarski('#skF_2')) != k2_xboole_0(k4_xboole_0('#skF_3',k1_tarski('#skF_2')),k1_tarski('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_105,plain,(
    '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_12])).

tff(c_126,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_105])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n013.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 13:56:09 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.65/1.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.65/1.13  
% 1.65/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.65/1.13  %$ k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 1.65/1.13  
% 1.65/1.13  %Foreground sorts:
% 1.65/1.13  
% 1.65/1.13  
% 1.65/1.13  %Background operators:
% 1.65/1.13  
% 1.65/1.13  
% 1.65/1.13  %Foreground operators:
% 1.65/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.65/1.13  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.65/1.13  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.65/1.13  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.65/1.13  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.65/1.13  tff('#skF_2', type, '#skF_2': $i).
% 1.65/1.13  tff('#skF_3', type, '#skF_3': $i).
% 1.65/1.13  tff('#skF_1', type, '#skF_1': $i).
% 1.65/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.65/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.65/1.13  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.65/1.13  
% 1.65/1.14  tff(f_42, negated_conjecture, ~(![A, B, C]: (~(A = B) => (k4_xboole_0(k2_xboole_0(C, k1_tarski(A)), k1_tarski(B)) = k2_xboole_0(k4_xboole_0(C, k1_tarski(B)), k1_tarski(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_zfmisc_1)).
% 1.65/1.14  tff(f_36, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 1.65/1.14  tff(f_27, axiom, (![A, B, C]: (k4_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(k4_xboole_0(A, C), k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_xboole_1)).
% 1.65/1.14  tff(c_14, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.65/1.14  tff(c_10, plain, (![A_7, B_8]: (k4_xboole_0(k1_tarski(A_7), k1_tarski(B_8))=k1_tarski(A_7) | B_8=A_7)), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.65/1.14  tff(c_53, plain, (![A_15, C_16, B_17]: (k2_xboole_0(k4_xboole_0(A_15, C_16), k4_xboole_0(B_17, C_16))=k4_xboole_0(k2_xboole_0(A_15, B_17), C_16))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.65/1.14  tff(c_95, plain, (![A_23, A_24, B_25]: (k4_xboole_0(k2_xboole_0(A_23, k1_tarski(A_24)), k1_tarski(B_25))=k2_xboole_0(k4_xboole_0(A_23, k1_tarski(B_25)), k1_tarski(A_24)) | B_25=A_24)), inference(superposition, [status(thm), theory('equality')], [c_10, c_53])).
% 1.65/1.14  tff(c_12, plain, (k4_xboole_0(k2_xboole_0('#skF_3', k1_tarski('#skF_1')), k1_tarski('#skF_2'))!=k2_xboole_0(k4_xboole_0('#skF_3', k1_tarski('#skF_2')), k1_tarski('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.65/1.14  tff(c_105, plain, ('#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_95, c_12])).
% 1.65/1.14  tff(c_126, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14, c_105])).
% 1.65/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.65/1.14  
% 1.65/1.14  Inference rules
% 1.65/1.14  ----------------------
% 1.65/1.14  #Ref     : 0
% 1.65/1.14  #Sup     : 27
% 1.65/1.14  #Fact    : 0
% 1.65/1.14  #Define  : 0
% 1.65/1.14  #Split   : 0
% 1.65/1.14  #Chain   : 0
% 1.65/1.14  #Close   : 0
% 1.65/1.14  
% 1.65/1.14  Ordering : KBO
% 1.65/1.14  
% 1.65/1.14  Simplification rules
% 1.65/1.14  ----------------------
% 1.65/1.14  #Subsume      : 0
% 1.65/1.14  #Demod        : 0
% 1.65/1.14  #Tautology    : 14
% 1.65/1.14  #SimpNegUnit  : 1
% 1.65/1.14  #BackRed      : 0
% 1.65/1.14  
% 1.65/1.14  #Partial instantiations: 0
% 1.65/1.14  #Strategies tried      : 1
% 1.65/1.14  
% 1.65/1.14  Timing (in seconds)
% 1.65/1.14  ----------------------
% 1.65/1.14  Preprocessing        : 0.26
% 1.65/1.14  Parsing              : 0.13
% 1.65/1.14  CNF conversion       : 0.01
% 1.65/1.14  Main loop            : 0.11
% 1.65/1.14  Inferencing          : 0.05
% 1.65/1.14  Reduction            : 0.03
% 1.65/1.14  Demodulation         : 0.02
% 1.65/1.14  BG Simplification    : 0.01
% 1.65/1.14  Subsumption          : 0.01
% 1.65/1.14  Abstraction          : 0.01
% 1.65/1.14  MUC search           : 0.00
% 1.65/1.14  Cooper               : 0.00
% 1.65/1.14  Total                : 0.39
% 1.65/1.14  Index Insertion      : 0.00
% 1.65/1.14  Index Deletion       : 0.00
% 1.65/1.14  Index Matching       : 0.00
% 1.65/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
