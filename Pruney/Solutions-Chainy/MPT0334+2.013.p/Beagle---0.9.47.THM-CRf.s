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
% DateTime   : Thu Dec  3 09:54:52 EST 2020

% Result     : Theorem 1.78s
% Output     : CNFRefutation 1.78s
% Verified   : 
% Statistics : Number of formulae       :   26 (  29 expanded)
%              Number of leaves         :   16 (  18 expanded)
%              Depth                    :    6
%              Number of atoms          :   20 (  24 expanded)
%              Number of equality atoms :   13 (  17 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k2_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(f_46,negated_conjecture,(
    ~ ! [A,B,C] :
        ( A != B
       => k4_xboole_0(k2_xboole_0(C,k1_tarski(A)),k1_tarski(B)) = k2_xboole_0(k4_xboole_0(C,k1_tarski(B)),k1_tarski(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_zfmisc_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( A != B
     => r1_xboole_0(k1_tarski(A),k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_xboole_0(A,B)
     => k2_xboole_0(k4_xboole_0(C,A),B) = k4_xboole_0(k2_xboole_0(C,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_xboole_1)).

tff(c_14,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_10,plain,(
    ! [A_9,B_10] :
      ( r1_xboole_0(k1_tarski(A_9),k1_tarski(B_10))
      | B_10 = A_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [C_5,B_4,A_3] :
      ( k4_xboole_0(k2_xboole_0(C_5,B_4),A_3) = k2_xboole_0(k4_xboole_0(C_5,A_3),B_4)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    k4_xboole_0(k2_xboole_0('#skF_3',k1_tarski('#skF_1')),k1_tarski('#skF_2')) != k2_xboole_0(k4_xboole_0('#skF_3',k1_tarski('#skF_2')),k1_tarski('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_15,plain,(
    k4_xboole_0(k2_xboole_0('#skF_3',k1_tarski('#skF_1')),k1_tarski('#skF_2')) != k2_xboole_0(k1_tarski('#skF_1'),k4_xboole_0('#skF_3',k1_tarski('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_12])).

tff(c_115,plain,
    ( k2_xboole_0(k4_xboole_0('#skF_3',k1_tarski('#skF_2')),k1_tarski('#skF_1')) != k2_xboole_0(k1_tarski('#skF_1'),k4_xboole_0('#skF_3',k1_tarski('#skF_2')))
    | ~ r1_xboole_0(k1_tarski('#skF_2'),k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_15])).

tff(c_118,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_2'),k1_tarski('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_115])).

tff(c_121,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_10,c_118])).

tff(c_125,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_121])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n025.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:36:50 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.78/1.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.78/1.21  
% 1.78/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.78/1.21  %$ r1_xboole_0 > k2_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 1.78/1.21  
% 1.78/1.21  %Foreground sorts:
% 1.78/1.21  
% 1.78/1.21  
% 1.78/1.21  %Background operators:
% 1.78/1.21  
% 1.78/1.21  
% 1.78/1.21  %Foreground operators:
% 1.78/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.78/1.21  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.78/1.21  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.78/1.21  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.78/1.21  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.78/1.21  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.78/1.21  tff('#skF_2', type, '#skF_2': $i).
% 1.78/1.21  tff('#skF_3', type, '#skF_3': $i).
% 1.78/1.21  tff('#skF_1', type, '#skF_1': $i).
% 1.78/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.78/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.78/1.21  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.78/1.21  
% 1.78/1.22  tff(f_46, negated_conjecture, ~(![A, B, C]: (~(A = B) => (k4_xboole_0(k2_xboole_0(C, k1_tarski(A)), k1_tarski(B)) = k2_xboole_0(k4_xboole_0(C, k1_tarski(B)), k1_tarski(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_zfmisc_1)).
% 1.78/1.22  tff(f_40, axiom, (![A, B]: (~(A = B) => r1_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 1.78/1.22  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.78/1.22  tff(f_31, axiom, (![A, B, C]: (r1_xboole_0(A, B) => (k2_xboole_0(k4_xboole_0(C, A), B) = k4_xboole_0(k2_xboole_0(C, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_xboole_1)).
% 1.78/1.22  tff(c_14, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.78/1.22  tff(c_10, plain, (![A_9, B_10]: (r1_xboole_0(k1_tarski(A_9), k1_tarski(B_10)) | B_10=A_9)), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.78/1.22  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.78/1.22  tff(c_4, plain, (![C_5, B_4, A_3]: (k4_xboole_0(k2_xboole_0(C_5, B_4), A_3)=k2_xboole_0(k4_xboole_0(C_5, A_3), B_4) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.78/1.22  tff(c_12, plain, (k4_xboole_0(k2_xboole_0('#skF_3', k1_tarski('#skF_1')), k1_tarski('#skF_2'))!=k2_xboole_0(k4_xboole_0('#skF_3', k1_tarski('#skF_2')), k1_tarski('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.78/1.22  tff(c_15, plain, (k4_xboole_0(k2_xboole_0('#skF_3', k1_tarski('#skF_1')), k1_tarski('#skF_2'))!=k2_xboole_0(k1_tarski('#skF_1'), k4_xboole_0('#skF_3', k1_tarski('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_12])).
% 1.78/1.22  tff(c_115, plain, (k2_xboole_0(k4_xboole_0('#skF_3', k1_tarski('#skF_2')), k1_tarski('#skF_1'))!=k2_xboole_0(k1_tarski('#skF_1'), k4_xboole_0('#skF_3', k1_tarski('#skF_2'))) | ~r1_xboole_0(k1_tarski('#skF_2'), k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_4, c_15])).
% 1.78/1.22  tff(c_118, plain, (~r1_xboole_0(k1_tarski('#skF_2'), k1_tarski('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_115])).
% 1.78/1.22  tff(c_121, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_10, c_118])).
% 1.78/1.22  tff(c_125, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14, c_121])).
% 1.78/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.78/1.22  
% 1.78/1.22  Inference rules
% 1.78/1.22  ----------------------
% 1.78/1.22  #Ref     : 0
% 1.78/1.22  #Sup     : 27
% 1.78/1.22  #Fact    : 0
% 1.78/1.22  #Define  : 0
% 1.78/1.22  #Split   : 0
% 1.78/1.22  #Chain   : 0
% 1.78/1.22  #Close   : 0
% 1.78/1.22  
% 1.78/1.22  Ordering : KBO
% 1.78/1.22  
% 1.78/1.22  Simplification rules
% 1.78/1.22  ----------------------
% 1.78/1.22  #Subsume      : 3
% 1.78/1.22  #Demod        : 3
% 1.78/1.22  #Tautology    : 16
% 1.78/1.22  #SimpNegUnit  : 1
% 1.78/1.22  #BackRed      : 0
% 1.78/1.22  
% 1.78/1.22  #Partial instantiations: 0
% 1.78/1.22  #Strategies tried      : 1
% 1.78/1.22  
% 1.78/1.22  Timing (in seconds)
% 1.78/1.22  ----------------------
% 1.78/1.22  Preprocessing        : 0.29
% 1.78/1.22  Parsing              : 0.16
% 1.78/1.22  CNF conversion       : 0.02
% 1.78/1.22  Main loop            : 0.12
% 1.78/1.22  Inferencing          : 0.05
% 1.78/1.22  Reduction            : 0.04
% 1.78/1.22  Demodulation         : 0.03
% 1.78/1.22  BG Simplification    : 0.01
% 1.78/1.22  Subsumption          : 0.02
% 1.78/1.22  Abstraction          : 0.01
% 1.78/1.22  MUC search           : 0.00
% 1.78/1.22  Cooper               : 0.00
% 1.78/1.22  Total                : 0.44
% 1.78/1.22  Index Insertion      : 0.00
% 1.78/1.22  Index Deletion       : 0.00
% 1.78/1.22  Index Matching       : 0.00
% 1.78/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
