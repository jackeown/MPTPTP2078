%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:50 EST 2020

% Result     : Theorem 1.94s
% Output     : CNFRefutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :   26 (  28 expanded)
%              Number of leaves         :   14 (  16 expanded)
%              Depth                    :    5
%              Number of atoms          :   20 (  23 expanded)
%              Number of equality atoms :   15 (  17 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_40,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,B)
       => B = k2_xboole_0(A,k4_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_33,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(c_10,plain,(
    ! [A_6,B_7] : k2_xboole_0(A_6,k4_xboole_0(B_7,A_6)) = k2_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    k2_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_1')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_15,plain,(
    k2_xboole_0('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_12])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_14,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_113,plain,(
    ! [A_14,B_15] :
      ( k4_xboole_0(A_14,B_15) = k1_xboole_0
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_121,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_113])).

tff(c_126,plain,(
    ! [A_16,B_17] : k2_xboole_0(A_16,k4_xboole_0(B_17,A_16)) = k2_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_139,plain,(
    k2_xboole_0('#skF_2',k1_xboole_0) = k2_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_126])).

tff(c_147,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_8,c_139])).

tff(c_149,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_15,c_147])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:34:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.94/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.37  
% 1.94/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.38  %$ r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 1.94/1.38  
% 1.94/1.38  %Foreground sorts:
% 1.94/1.38  
% 1.94/1.38  
% 1.94/1.38  %Background operators:
% 1.94/1.38  
% 1.94/1.38  
% 1.94/1.38  %Foreground operators:
% 1.94/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.94/1.38  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.94/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.94/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.94/1.38  tff('#skF_2', type, '#skF_2': $i).
% 1.94/1.38  tff('#skF_1', type, '#skF_1': $i).
% 1.94/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.94/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.94/1.38  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.94/1.38  
% 1.94/1.39  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 1.94/1.39  tff(f_40, negated_conjecture, ~(![A, B]: (r1_tarski(A, B) => (B = k2_xboole_0(A, k4_xboole_0(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_xboole_1)).
% 1.94/1.39  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.94/1.39  tff(f_33, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 1.94/1.39  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 1.94/1.39  tff(c_10, plain, (![A_6, B_7]: (k2_xboole_0(A_6, k4_xboole_0(B_7, A_6))=k2_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.94/1.39  tff(c_12, plain, (k2_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_1'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.94/1.39  tff(c_15, plain, (k2_xboole_0('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_10, c_12])).
% 1.94/1.39  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.94/1.39  tff(c_8, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.94/1.39  tff(c_14, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.94/1.39  tff(c_113, plain, (![A_14, B_15]: (k4_xboole_0(A_14, B_15)=k1_xboole_0 | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.94/1.39  tff(c_121, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_14, c_113])).
% 1.94/1.39  tff(c_126, plain, (![A_16, B_17]: (k2_xboole_0(A_16, k4_xboole_0(B_17, A_16))=k2_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.94/1.39  tff(c_139, plain, (k2_xboole_0('#skF_2', k1_xboole_0)=k2_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_121, c_126])).
% 1.94/1.39  tff(c_147, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_8, c_139])).
% 1.94/1.39  tff(c_149, plain, $false, inference(negUnitSimplification, [status(thm)], [c_15, c_147])).
% 1.94/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.39  
% 1.94/1.39  Inference rules
% 1.94/1.39  ----------------------
% 1.94/1.39  #Ref     : 0
% 1.94/1.39  #Sup     : 31
% 1.94/1.39  #Fact    : 0
% 1.94/1.39  #Define  : 0
% 1.94/1.39  #Split   : 0
% 1.94/1.39  #Chain   : 0
% 1.94/1.39  #Close   : 0
% 1.94/1.39  
% 1.94/1.39  Ordering : KBO
% 1.94/1.39  
% 1.94/1.39  Simplification rules
% 1.94/1.39  ----------------------
% 1.94/1.39  #Subsume      : 0
% 1.94/1.39  #Demod        : 11
% 1.94/1.39  #Tautology    : 26
% 1.94/1.39  #SimpNegUnit  : 1
% 1.94/1.39  #BackRed      : 0
% 1.94/1.39  
% 1.94/1.39  #Partial instantiations: 0
% 1.94/1.39  #Strategies tried      : 1
% 1.94/1.39  
% 1.94/1.39  Timing (in seconds)
% 1.94/1.39  ----------------------
% 2.04/1.39  Preprocessing        : 0.40
% 2.04/1.39  Parsing              : 0.22
% 2.04/1.39  CNF conversion       : 0.02
% 2.04/1.39  Main loop            : 0.19
% 2.04/1.39  Inferencing          : 0.07
% 2.04/1.39  Reduction            : 0.07
% 2.04/1.39  Demodulation         : 0.06
% 2.04/1.39  BG Simplification    : 0.01
% 2.04/1.39  Subsumption          : 0.02
% 2.04/1.39  Abstraction          : 0.01
% 2.04/1.39  MUC search           : 0.00
% 2.04/1.40  Cooper               : 0.00
% 2.04/1.40  Total                : 0.63
% 2.04/1.40  Index Insertion      : 0.00
% 2.04/1.40  Index Deletion       : 0.00
% 2.04/1.40  Index Matching       : 0.00
% 2.04/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
