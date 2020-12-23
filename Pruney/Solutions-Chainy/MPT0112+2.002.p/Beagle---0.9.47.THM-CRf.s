%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:09 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   29 (  30 expanded)
%              Number of leaves         :   16 (  17 expanded)
%              Depth                    :    5
%              Number of atoms          :   22 (  24 expanded)
%              Number of equality atoms :   10 (  11 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

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

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_44,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( r2_xboole_0(A,B)
          & k4_xboole_0(B,A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_xboole_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ~ ( r1_tarski(A,B)
        & r2_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_xboole_1)).

tff(f_29,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(c_14,plain,(
    r2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_128,plain,(
    ! [B_18,A_19] :
      ( ~ r2_xboole_0(B_18,A_19)
      | ~ r1_tarski(A_19,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_132,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_128])).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_12,plain,(
    k4_xboole_0('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_153,plain,(
    ! [A_22,B_23] : k2_xboole_0(A_22,k4_xboole_0(B_23,A_22)) = k2_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_176,plain,(
    k2_xboole_0('#skF_1',k1_xboole_0) = k2_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_153])).

tff(c_182,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_176])).

tff(c_33,plain,(
    ! [B_14,A_15] : k2_xboole_0(B_14,A_15) = k2_xboole_0(A_15,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_8,B_9] : r1_tarski(A_8,k2_xboole_0(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_48,plain,(
    ! [A_15,B_14] : r1_tarski(A_15,k2_xboole_0(B_14,A_15)) ),
    inference(superposition,[status(thm),theory(equality)],[c_33,c_10])).

tff(c_186,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_182,c_48])).

tff(c_193,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_132,c_186])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:04:44 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.93/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.43  
% 1.93/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.43  %$ r2_xboole_0 > r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 1.93/1.43  
% 1.93/1.43  %Foreground sorts:
% 1.93/1.43  
% 1.93/1.43  
% 1.93/1.43  %Background operators:
% 1.93/1.43  
% 1.93/1.43  
% 1.93/1.43  %Foreground operators:
% 1.93/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.93/1.43  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.93/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.93/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.93/1.43  tff('#skF_2', type, '#skF_2': $i).
% 1.93/1.43  tff('#skF_1', type, '#skF_1': $i).
% 1.93/1.43  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 1.93/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.93/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.93/1.43  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.93/1.43  
% 1.93/1.44  tff(f_44, negated_conjecture, ~(![A, B]: ~(r2_xboole_0(A, B) & (k4_xboole_0(B, A) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t105_xboole_1)).
% 1.93/1.44  tff(f_36, axiom, (![A, B]: ~(r1_tarski(A, B) & r2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_xboole_1)).
% 1.93/1.44  tff(f_29, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 1.93/1.44  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 1.93/1.44  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.93/1.44  tff(f_38, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.93/1.44  tff(c_14, plain, (r2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.93/1.44  tff(c_128, plain, (![B_18, A_19]: (~r2_xboole_0(B_18, A_19) | ~r1_tarski(A_19, B_18))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.93/1.44  tff(c_132, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_14, c_128])).
% 1.93/1.44  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.93/1.44  tff(c_12, plain, (k4_xboole_0('#skF_2', '#skF_1')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.93/1.44  tff(c_153, plain, (![A_22, B_23]: (k2_xboole_0(A_22, k4_xboole_0(B_23, A_22))=k2_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.93/1.44  tff(c_176, plain, (k2_xboole_0('#skF_1', k1_xboole_0)=k2_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_12, c_153])).
% 1.93/1.44  tff(c_182, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4, c_176])).
% 1.93/1.44  tff(c_33, plain, (![B_14, A_15]: (k2_xboole_0(B_14, A_15)=k2_xboole_0(A_15, B_14))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.93/1.44  tff(c_10, plain, (![A_8, B_9]: (r1_tarski(A_8, k2_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.93/1.44  tff(c_48, plain, (![A_15, B_14]: (r1_tarski(A_15, k2_xboole_0(B_14, A_15)))), inference(superposition, [status(thm), theory('equality')], [c_33, c_10])).
% 1.93/1.44  tff(c_186, plain, (r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_182, c_48])).
% 1.93/1.44  tff(c_193, plain, $false, inference(negUnitSimplification, [status(thm)], [c_132, c_186])).
% 1.93/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.44  
% 1.93/1.44  Inference rules
% 1.93/1.44  ----------------------
% 1.93/1.44  #Ref     : 0
% 1.93/1.44  #Sup     : 44
% 1.93/1.44  #Fact    : 0
% 1.93/1.44  #Define  : 0
% 1.93/1.44  #Split   : 0
% 1.93/1.44  #Chain   : 0
% 1.93/1.44  #Close   : 0
% 1.93/1.44  
% 1.93/1.44  Ordering : KBO
% 1.93/1.44  
% 1.93/1.44  Simplification rules
% 1.93/1.44  ----------------------
% 1.93/1.44  #Subsume      : 0
% 1.93/1.44  #Demod        : 16
% 1.93/1.44  #Tautology    : 32
% 1.93/1.44  #SimpNegUnit  : 1
% 1.93/1.44  #BackRed      : 0
% 1.93/1.44  
% 1.93/1.44  #Partial instantiations: 0
% 1.93/1.44  #Strategies tried      : 1
% 1.93/1.44  
% 1.93/1.44  Timing (in seconds)
% 1.93/1.44  ----------------------
% 1.93/1.44  Preprocessing        : 0.37
% 1.93/1.44  Parsing              : 0.20
% 2.09/1.44  CNF conversion       : 0.02
% 2.09/1.44  Main loop            : 0.16
% 2.09/1.44  Inferencing          : 0.07
% 2.09/1.44  Reduction            : 0.05
% 2.09/1.44  Demodulation         : 0.04
% 2.09/1.44  BG Simplification    : 0.01
% 2.09/1.44  Subsumption          : 0.02
% 2.09/1.44  Abstraction          : 0.01
% 2.09/1.44  MUC search           : 0.00
% 2.09/1.44  Cooper               : 0.00
% 2.09/1.44  Total                : 0.56
% 2.09/1.44  Index Insertion      : 0.00
% 2.09/1.44  Index Deletion       : 0.00
% 2.09/1.44  Index Matching       : 0.00
% 2.09/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
