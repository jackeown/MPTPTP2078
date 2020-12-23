%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:44 EST 2020

% Result     : Theorem 2.65s
% Output     : CNFRefutation 2.65s
% Verified   : 
% Statistics : Number of formulae       :   41 (  60 expanded)
%              Number of leaves         :   17 (  28 expanded)
%              Depth                    :    7
%              Number of atoms          :   35 (  68 expanded)
%              Number of equality atoms :   28 (  51 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_46,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( k2_xboole_0(A,B) = k2_xboole_0(C,D)
          & r1_xboole_0(C,A)
          & r1_xboole_0(D,B) )
       => C = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k2_xboole_0(B,C)) = k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_14,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_71,plain,(
    ! [B_16,A_17] : k2_xboole_0(B_16,A_17) = k2_xboole_0(A_17,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_7,B_8] : k3_xboole_0(A_7,k2_xboole_0(A_7,B_8)) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_86,plain,(
    ! [A_17,B_16] : k3_xboole_0(A_17,k2_xboole_0(B_16,A_17)) = A_17 ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_10])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_20,plain,(
    k2_xboole_0('#skF_3','#skF_4') = k2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_21,plain,(
    k2_xboole_0('#skF_1','#skF_2') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_20])).

tff(c_18,plain,(
    r1_xboole_0('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_149,plain,(
    ! [A_20,B_21] :
      ( k3_xboole_0(A_20,B_21) = k1_xboole_0
      | ~ r1_xboole_0(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_157,plain,(
    k3_xboole_0('#skF_3','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_149])).

tff(c_190,plain,(
    ! [A_24,B_25,C_26] : k2_xboole_0(k3_xboole_0(A_24,B_25),k3_xboole_0(A_24,C_26)) = k3_xboole_0(A_24,k2_xboole_0(B_25,C_26)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_278,plain,(
    ! [C_27] : k3_xboole_0('#skF_3',k2_xboole_0('#skF_1',C_27)) = k2_xboole_0(k1_xboole_0,k3_xboole_0('#skF_3',C_27)) ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_190])).

tff(c_309,plain,(
    k3_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_3')) = k2_xboole_0(k1_xboole_0,k3_xboole_0('#skF_3','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_21,c_278])).

tff(c_312,plain,(
    k2_xboole_0(k1_xboole_0,k3_xboole_0('#skF_3','#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_309])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_16,plain,(
    r1_xboole_0('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_156,plain,(
    k3_xboole_0('#skF_4','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_149])).

tff(c_358,plain,(
    ! [B_28,A_29,C_30] : k2_xboole_0(k3_xboole_0(B_28,A_29),k3_xboole_0(A_29,C_30)) = k3_xboole_0(A_29,k2_xboole_0(B_28,C_30)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_190])).

tff(c_893,plain,(
    ! [C_36] : k3_xboole_0('#skF_2',k2_xboole_0('#skF_4',C_36)) = k2_xboole_0(k1_xboole_0,k3_xboole_0('#skF_2',C_36)) ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_358])).

tff(c_114,plain,(
    ! [A_18,B_19] : k3_xboole_0(A_18,k2_xboole_0(B_19,A_18)) = A_18 ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_10])).

tff(c_137,plain,(
    k3_xboole_0('#skF_2',k2_xboole_0('#skF_4','#skF_3')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_21,c_114])).

tff(c_917,plain,(
    k2_xboole_0(k1_xboole_0,k3_xboole_0('#skF_2','#skF_3')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_893,c_137])).

tff(c_941,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_312,c_4,c_917])).

tff(c_943,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_941])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:01:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.65/1.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.65/1.50  
% 2.65/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.65/1.50  %$ r1_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.65/1.50  
% 2.65/1.50  %Foreground sorts:
% 2.65/1.50  
% 2.65/1.50  
% 2.65/1.50  %Background operators:
% 2.65/1.50  
% 2.65/1.50  
% 2.65/1.50  %Foreground operators:
% 2.65/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.65/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.65/1.50  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.65/1.50  tff('#skF_2', type, '#skF_2': $i).
% 2.65/1.50  tff('#skF_3', type, '#skF_3': $i).
% 2.65/1.50  tff('#skF_1', type, '#skF_1': $i).
% 2.65/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.65/1.50  tff('#skF_4', type, '#skF_4': $i).
% 2.65/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.65/1.50  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.65/1.50  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.65/1.50  
% 2.65/1.51  tff(f_46, negated_conjecture, ~(![A, B, C, D]: ((((k2_xboole_0(A, B) = k2_xboole_0(C, D)) & r1_xboole_0(C, A)) & r1_xboole_0(D, B)) => (C = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_xboole_1)).
% 2.65/1.51  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.65/1.51  tff(f_35, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_xboole_1)).
% 2.65/1.51  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.65/1.51  tff(f_37, axiom, (![A, B, C]: (k3_xboole_0(A, k2_xboole_0(B, C)) = k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_xboole_1)).
% 2.65/1.51  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.65/1.51  tff(c_14, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.65/1.51  tff(c_71, plain, (![B_16, A_17]: (k2_xboole_0(B_16, A_17)=k2_xboole_0(A_17, B_16))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.65/1.51  tff(c_10, plain, (![A_7, B_8]: (k3_xboole_0(A_7, k2_xboole_0(A_7, B_8))=A_7)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.65/1.51  tff(c_86, plain, (![A_17, B_16]: (k3_xboole_0(A_17, k2_xboole_0(B_16, A_17))=A_17)), inference(superposition, [status(thm), theory('equality')], [c_71, c_10])).
% 2.65/1.51  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.65/1.51  tff(c_20, plain, (k2_xboole_0('#skF_3', '#skF_4')=k2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.65/1.51  tff(c_21, plain, (k2_xboole_0('#skF_1', '#skF_2')=k2_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_20])).
% 2.65/1.51  tff(c_18, plain, (r1_xboole_0('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.65/1.51  tff(c_149, plain, (![A_20, B_21]: (k3_xboole_0(A_20, B_21)=k1_xboole_0 | ~r1_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.65/1.51  tff(c_157, plain, (k3_xboole_0('#skF_3', '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_18, c_149])).
% 2.65/1.51  tff(c_190, plain, (![A_24, B_25, C_26]: (k2_xboole_0(k3_xboole_0(A_24, B_25), k3_xboole_0(A_24, C_26))=k3_xboole_0(A_24, k2_xboole_0(B_25, C_26)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.65/1.51  tff(c_278, plain, (![C_27]: (k3_xboole_0('#skF_3', k2_xboole_0('#skF_1', C_27))=k2_xboole_0(k1_xboole_0, k3_xboole_0('#skF_3', C_27)))), inference(superposition, [status(thm), theory('equality')], [c_157, c_190])).
% 2.65/1.51  tff(c_309, plain, (k3_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_3'))=k2_xboole_0(k1_xboole_0, k3_xboole_0('#skF_3', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_21, c_278])).
% 2.65/1.51  tff(c_312, plain, (k2_xboole_0(k1_xboole_0, k3_xboole_0('#skF_3', '#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_309])).
% 2.65/1.51  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.65/1.51  tff(c_16, plain, (r1_xboole_0('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.65/1.51  tff(c_156, plain, (k3_xboole_0('#skF_4', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_16, c_149])).
% 2.65/1.51  tff(c_358, plain, (![B_28, A_29, C_30]: (k2_xboole_0(k3_xboole_0(B_28, A_29), k3_xboole_0(A_29, C_30))=k3_xboole_0(A_29, k2_xboole_0(B_28, C_30)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_190])).
% 2.65/1.51  tff(c_893, plain, (![C_36]: (k3_xboole_0('#skF_2', k2_xboole_0('#skF_4', C_36))=k2_xboole_0(k1_xboole_0, k3_xboole_0('#skF_2', C_36)))), inference(superposition, [status(thm), theory('equality')], [c_156, c_358])).
% 2.65/1.51  tff(c_114, plain, (![A_18, B_19]: (k3_xboole_0(A_18, k2_xboole_0(B_19, A_18))=A_18)), inference(superposition, [status(thm), theory('equality')], [c_71, c_10])).
% 2.65/1.51  tff(c_137, plain, (k3_xboole_0('#skF_2', k2_xboole_0('#skF_4', '#skF_3'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_21, c_114])).
% 2.65/1.51  tff(c_917, plain, (k2_xboole_0(k1_xboole_0, k3_xboole_0('#skF_2', '#skF_3'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_893, c_137])).
% 2.65/1.51  tff(c_941, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_312, c_4, c_917])).
% 2.65/1.51  tff(c_943, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14, c_941])).
% 2.65/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.65/1.51  
% 2.65/1.51  Inference rules
% 2.65/1.51  ----------------------
% 2.65/1.51  #Ref     : 0
% 2.65/1.51  #Sup     : 270
% 2.65/1.51  #Fact    : 0
% 2.65/1.51  #Define  : 0
% 2.65/1.51  #Split   : 0
% 2.65/1.51  #Chain   : 0
% 2.65/1.51  #Close   : 0
% 2.65/1.51  
% 2.65/1.51  Ordering : KBO
% 2.65/1.51  
% 2.65/1.51  Simplification rules
% 2.65/1.51  ----------------------
% 2.65/1.51  #Subsume      : 2
% 2.65/1.51  #Demod        : 83
% 2.65/1.51  #Tautology    : 102
% 2.65/1.51  #SimpNegUnit  : 1
% 2.65/1.51  #BackRed      : 0
% 2.65/1.51  
% 2.65/1.51  #Partial instantiations: 0
% 2.65/1.51  #Strategies tried      : 1
% 2.65/1.51  
% 2.65/1.51  Timing (in seconds)
% 2.65/1.51  ----------------------
% 2.65/1.51  Preprocessing        : 0.25
% 2.65/1.51  Parsing              : 0.13
% 2.65/1.51  CNF conversion       : 0.02
% 2.65/1.51  Main loop            : 0.41
% 2.65/1.51  Inferencing          : 0.13
% 2.65/1.51  Reduction            : 0.18
% 2.65/1.51  Demodulation         : 0.15
% 2.65/1.51  BG Simplification    : 0.02
% 2.65/1.51  Subsumption          : 0.06
% 2.65/1.51  Abstraction          : 0.02
% 2.65/1.51  MUC search           : 0.00
% 2.65/1.52  Cooper               : 0.00
% 2.65/1.52  Total                : 0.68
% 2.65/1.52  Index Insertion      : 0.00
% 2.65/1.52  Index Deletion       : 0.00
% 2.65/1.52  Index Matching       : 0.00
% 2.65/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
