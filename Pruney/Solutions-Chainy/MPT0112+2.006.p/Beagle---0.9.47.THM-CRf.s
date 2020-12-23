%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:09 EST 2020

% Result     : Theorem 1.68s
% Output     : CNFRefutation 1.68s
% Verified   : 
% Statistics : Number of formulae       :   31 (  35 expanded)
%              Number of leaves         :   17 (  20 expanded)
%              Depth                    :    6
%              Number of atoms          :   26 (  34 expanded)
%              Number of equality atoms :   14 (  17 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_34,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_57,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( r2_xboole_0(A,B)
          & k4_xboole_0(B,A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_44,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_46,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(c_6,plain,(
    ! [B_4] : ~ r2_xboole_0(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_24,plain,(
    r2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_46,plain,(
    ! [A_18,B_19] :
      ( r1_tarski(A_18,B_19)
      | ~ r2_xboole_0(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_50,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_46])).

tff(c_139,plain,(
    ! [A_25,B_26] :
      ( k3_xboole_0(A_25,B_26) = A_25
      | ~ r1_tarski(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_143,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_50,c_139])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_16,plain,(
    ! [A_10] : k4_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_22,plain,(
    k4_xboole_0('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_219,plain,(
    ! [A_33,B_34] : k4_xboole_0(A_33,k4_xboole_0(A_33,B_34)) = k3_xboole_0(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_248,plain,(
    k4_xboole_0('#skF_2',k1_xboole_0) = k3_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_219])).

tff(c_255,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_2,c_16,c_248])).

tff(c_261,plain,(
    r2_xboole_0('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_255,c_24])).

tff(c_263,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6,c_261])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:11:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.68/1.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.68/1.17  
% 1.68/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.68/1.17  %$ r2_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 1.68/1.17  
% 1.68/1.17  %Foreground sorts:
% 1.68/1.17  
% 1.68/1.17  
% 1.68/1.17  %Background operators:
% 1.68/1.17  
% 1.68/1.17  
% 1.68/1.17  %Foreground operators:
% 1.68/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.68/1.17  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.68/1.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.68/1.17  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.68/1.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.68/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.68/1.17  tff('#skF_1', type, '#skF_1': $i).
% 1.68/1.17  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 1.68/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.68/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.68/1.17  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.68/1.17  
% 1.68/1.18  tff(f_34, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 1.68/1.18  tff(f_57, negated_conjecture, ~(![A, B]: ~(r2_xboole_0(A, B) & (k4_xboole_0(B, A) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t105_xboole_1)).
% 1.68/1.18  tff(f_40, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.68/1.18  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.68/1.18  tff(f_44, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 1.68/1.18  tff(f_46, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.68/1.18  tff(c_6, plain, (![B_4]: (~r2_xboole_0(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.68/1.18  tff(c_24, plain, (r2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.68/1.18  tff(c_46, plain, (![A_18, B_19]: (r1_tarski(A_18, B_19) | ~r2_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.68/1.18  tff(c_50, plain, (r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_24, c_46])).
% 1.68/1.18  tff(c_139, plain, (![A_25, B_26]: (k3_xboole_0(A_25, B_26)=A_25 | ~r1_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.68/1.18  tff(c_143, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_50, c_139])).
% 1.68/1.18  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.68/1.18  tff(c_16, plain, (![A_10]: (k4_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.68/1.18  tff(c_22, plain, (k4_xboole_0('#skF_2', '#skF_1')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.68/1.18  tff(c_219, plain, (![A_33, B_34]: (k4_xboole_0(A_33, k4_xboole_0(A_33, B_34))=k3_xboole_0(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.68/1.18  tff(c_248, plain, (k4_xboole_0('#skF_2', k1_xboole_0)=k3_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_22, c_219])).
% 1.68/1.18  tff(c_255, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_143, c_2, c_16, c_248])).
% 1.68/1.18  tff(c_261, plain, (r2_xboole_0('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_255, c_24])).
% 1.68/1.18  tff(c_263, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6, c_261])).
% 1.68/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.68/1.18  
% 1.68/1.18  Inference rules
% 1.68/1.18  ----------------------
% 1.68/1.18  #Ref     : 0
% 1.68/1.18  #Sup     : 58
% 1.68/1.18  #Fact    : 0
% 1.68/1.18  #Define  : 0
% 1.68/1.18  #Split   : 0
% 1.68/1.18  #Chain   : 0
% 1.68/1.18  #Close   : 0
% 1.68/1.18  
% 1.68/1.18  Ordering : KBO
% 1.68/1.18  
% 1.68/1.18  Simplification rules
% 1.68/1.18  ----------------------
% 1.68/1.18  #Subsume      : 0
% 1.68/1.18  #Demod        : 23
% 1.68/1.18  #Tautology    : 44
% 1.68/1.18  #SimpNegUnit  : 1
% 1.68/1.18  #BackRed      : 6
% 1.68/1.18  
% 1.68/1.18  #Partial instantiations: 0
% 1.68/1.18  #Strategies tried      : 1
% 1.68/1.18  
% 1.68/1.18  Timing (in seconds)
% 1.68/1.18  ----------------------
% 1.93/1.18  Preprocessing        : 0.27
% 1.93/1.18  Parsing              : 0.15
% 1.93/1.18  CNF conversion       : 0.02
% 1.93/1.18  Main loop            : 0.16
% 1.93/1.18  Inferencing          : 0.07
% 1.93/1.18  Reduction            : 0.06
% 1.93/1.18  Demodulation         : 0.04
% 1.93/1.18  BG Simplification    : 0.01
% 1.93/1.18  Subsumption          : 0.02
% 1.93/1.18  Abstraction          : 0.01
% 1.93/1.18  MUC search           : 0.00
% 1.93/1.18  Cooper               : 0.00
% 1.93/1.18  Total                : 0.45
% 1.93/1.18  Index Insertion      : 0.00
% 1.93/1.18  Index Deletion       : 0.00
% 1.93/1.18  Index Matching       : 0.00
% 1.93/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
