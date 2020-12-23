%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:50 EST 2020

% Result     : Theorem 2.08s
% Output     : CNFRefutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :   40 (  43 expanded)
%              Number of leaves         :   19 (  22 expanded)
%              Depth                    :    7
%              Number of atoms          :   35 (  42 expanded)
%              Number of equality atoms :   19 (  20 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_50,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,C) )
       => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_37,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_39,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k2_xboole_0(B,C)) = k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(c_18,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_83,plain,(
    ! [B_22,A_23] : k2_xboole_0(B_22,A_23) = k2_xboole_0(A_23,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_9] : k2_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_99,plain,(
    ! [A_23] : k2_xboole_0(k1_xboole_0,A_23) = A_23 ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_12])).

tff(c_20,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_211,plain,(
    ! [A_29,B_30] :
      ( k3_xboole_0(A_29,B_30) = k1_xboole_0
      | ~ r1_xboole_0(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_219,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_211])).

tff(c_289,plain,(
    ! [A_31,B_32,C_33] : k2_xboole_0(k3_xboole_0(A_31,B_32),k3_xboole_0(A_31,C_33)) = k3_xboole_0(A_31,k2_xboole_0(B_32,C_33)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_316,plain,(
    ! [C_33] : k3_xboole_0('#skF_1',k2_xboole_0('#skF_3',C_33)) = k2_xboole_0(k1_xboole_0,k3_xboole_0('#skF_1',C_33)) ),
    inference(superposition,[status(thm),theory(equality)],[c_219,c_289])).

tff(c_401,plain,(
    ! [C_34] : k3_xboole_0('#skF_1',k2_xboole_0('#skF_3',C_34)) = k3_xboole_0('#skF_1',C_34) ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_316])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_22,plain,(
    r1_tarski('#skF_1',k2_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_23,plain,(
    r1_tarski('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_22])).

tff(c_130,plain,(
    ! [A_24,B_25] :
      ( k3_xboole_0(A_24,B_25) = A_24
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_142,plain,(
    k3_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_23,c_130])).

tff(c_413,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_401,c_142])).

tff(c_34,plain,(
    ! [B_18,A_19] : k3_xboole_0(B_18,A_19) = k3_xboole_0(A_19,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_10,plain,(
    ! [A_7,B_8] : r1_tarski(k3_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_49,plain,(
    ! [B_18,A_19] : r1_tarski(k3_xboole_0(B_18,A_19),A_19) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_10])).

tff(c_453,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_413,c_49])).

tff(c_461,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_453])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:15:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.08/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.28  
% 2.08/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.29  %$ r1_xboole_0 > r1_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.08/1.29  
% 2.08/1.29  %Foreground sorts:
% 2.08/1.29  
% 2.08/1.29  
% 2.08/1.29  %Background operators:
% 2.08/1.29  
% 2.08/1.29  
% 2.08/1.29  %Foreground operators:
% 2.08/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.08/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.08/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.08/1.29  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.08/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.08/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.08/1.29  tff('#skF_1', type, '#skF_1': $i).
% 2.08/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.08/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.08/1.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.08/1.29  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.08/1.29  
% 2.08/1.30  tff(f_50, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, k2_xboole_0(B, C)) & r1_xboole_0(A, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_xboole_1)).
% 2.08/1.30  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.08/1.30  tff(f_37, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 2.08/1.30  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.08/1.30  tff(f_39, axiom, (![A, B, C]: (k3_xboole_0(A, k2_xboole_0(B, C)) = k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_xboole_1)).
% 2.08/1.30  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.08/1.30  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.08/1.30  tff(f_35, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.08/1.30  tff(c_18, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.08/1.30  tff(c_83, plain, (![B_22, A_23]: (k2_xboole_0(B_22, A_23)=k2_xboole_0(A_23, B_22))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.08/1.30  tff(c_12, plain, (![A_9]: (k2_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.08/1.30  tff(c_99, plain, (![A_23]: (k2_xboole_0(k1_xboole_0, A_23)=A_23)), inference(superposition, [status(thm), theory('equality')], [c_83, c_12])).
% 2.08/1.30  tff(c_20, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.08/1.30  tff(c_211, plain, (![A_29, B_30]: (k3_xboole_0(A_29, B_30)=k1_xboole_0 | ~r1_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.08/1.30  tff(c_219, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_20, c_211])).
% 2.08/1.30  tff(c_289, plain, (![A_31, B_32, C_33]: (k2_xboole_0(k3_xboole_0(A_31, B_32), k3_xboole_0(A_31, C_33))=k3_xboole_0(A_31, k2_xboole_0(B_32, C_33)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.08/1.30  tff(c_316, plain, (![C_33]: (k3_xboole_0('#skF_1', k2_xboole_0('#skF_3', C_33))=k2_xboole_0(k1_xboole_0, k3_xboole_0('#skF_1', C_33)))), inference(superposition, [status(thm), theory('equality')], [c_219, c_289])).
% 2.08/1.30  tff(c_401, plain, (![C_34]: (k3_xboole_0('#skF_1', k2_xboole_0('#skF_3', C_34))=k3_xboole_0('#skF_1', C_34))), inference(demodulation, [status(thm), theory('equality')], [c_99, c_316])).
% 2.08/1.30  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.08/1.30  tff(c_22, plain, (r1_tarski('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.08/1.30  tff(c_23, plain, (r1_tarski('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_22])).
% 2.08/1.30  tff(c_130, plain, (![A_24, B_25]: (k3_xboole_0(A_24, B_25)=A_24 | ~r1_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.08/1.30  tff(c_142, plain, (k3_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))='#skF_1'), inference(resolution, [status(thm)], [c_23, c_130])).
% 2.08/1.30  tff(c_413, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_401, c_142])).
% 2.08/1.30  tff(c_34, plain, (![B_18, A_19]: (k3_xboole_0(B_18, A_19)=k3_xboole_0(A_19, B_18))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.08/1.30  tff(c_10, plain, (![A_7, B_8]: (r1_tarski(k3_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.08/1.30  tff(c_49, plain, (![B_18, A_19]: (r1_tarski(k3_xboole_0(B_18, A_19), A_19))), inference(superposition, [status(thm), theory('equality')], [c_34, c_10])).
% 2.08/1.30  tff(c_453, plain, (r1_tarski('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_413, c_49])).
% 2.08/1.30  tff(c_461, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_453])).
% 2.08/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.30  
% 2.08/1.30  Inference rules
% 2.08/1.30  ----------------------
% 2.08/1.30  #Ref     : 0
% 2.08/1.30  #Sup     : 120
% 2.08/1.30  #Fact    : 0
% 2.08/1.30  #Define  : 0
% 2.08/1.30  #Split   : 0
% 2.08/1.30  #Chain   : 0
% 2.08/1.30  #Close   : 0
% 2.08/1.30  
% 2.08/1.30  Ordering : KBO
% 2.08/1.30  
% 2.08/1.30  Simplification rules
% 2.08/1.30  ----------------------
% 2.08/1.30  #Subsume      : 0
% 2.08/1.30  #Demod        : 44
% 2.08/1.30  #Tautology    : 69
% 2.08/1.30  #SimpNegUnit  : 1
% 2.08/1.30  #BackRed      : 0
% 2.08/1.30  
% 2.08/1.30  #Partial instantiations: 0
% 2.08/1.30  #Strategies tried      : 1
% 2.08/1.30  
% 2.08/1.30  Timing (in seconds)
% 2.08/1.30  ----------------------
% 2.08/1.30  Preprocessing        : 0.28
% 2.08/1.30  Parsing              : 0.16
% 2.08/1.30  CNF conversion       : 0.02
% 2.08/1.30  Main loop            : 0.24
% 2.08/1.30  Inferencing          : 0.08
% 2.08/1.30  Reduction            : 0.10
% 2.08/1.30  Demodulation         : 0.08
% 2.08/1.30  BG Simplification    : 0.01
% 2.08/1.30  Subsumption          : 0.04
% 2.08/1.30  Abstraction          : 0.01
% 2.08/1.30  MUC search           : 0.00
% 2.08/1.30  Cooper               : 0.00
% 2.08/1.30  Total                : 0.54
% 2.08/1.30  Index Insertion      : 0.00
% 2.08/1.30  Index Deletion       : 0.00
% 2.08/1.30  Index Matching       : 0.00
% 2.08/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
