%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:34 EST 2020

% Result     : Theorem 2.17s
% Output     : CNFRefutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :   39 (  61 expanded)
%              Number of leaves         :   15 (  29 expanded)
%              Depth                    :    5
%              Number of atoms          :   38 (  79 expanded)
%              Number of equality atoms :   16 (  30 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_46,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_xboole_0(A,D)
          & r1_xboole_0(B,D)
          & r1_xboole_0(C,D) )
       => r1_xboole_0(k2_xboole_0(k2_xboole_0(A,B),C),D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t114_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(c_14,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_19,plain,(
    ! [B_10,A_11] :
      ( r1_xboole_0(B_10,A_11)
      | ~ r1_xboole_0(A_11,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_26,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_19])).

tff(c_45,plain,(
    ! [A_14,B_15] :
      ( k4_xboole_0(A_14,B_15) = A_14
      | ~ r1_xboole_0(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_70,plain,(
    k4_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_26,c_45])).

tff(c_16,plain,(
    r1_xboole_0('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_27,plain,(
    r1_xboole_0('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_19])).

tff(c_67,plain,(
    k4_xboole_0('#skF_4','#skF_2') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_27,c_45])).

tff(c_165,plain,(
    ! [A_20,B_21,C_22] : k4_xboole_0(k4_xboole_0(A_20,B_21),C_22) = k4_xboole_0(A_20,k2_xboole_0(B_21,C_22)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_186,plain,(
    ! [C_22] : k4_xboole_0('#skF_4',k2_xboole_0('#skF_2',C_22)) = k4_xboole_0('#skF_4',C_22) ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_165])).

tff(c_18,plain,(
    r1_xboole_0('#skF_1','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_28,plain,(
    r1_xboole_0('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_19])).

tff(c_68,plain,(
    k4_xboole_0('#skF_4','#skF_1') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_28,c_45])).

tff(c_189,plain,(
    ! [C_22] : k4_xboole_0('#skF_4',k2_xboole_0('#skF_1',C_22)) = k4_xboole_0('#skF_4',C_22) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_165])).

tff(c_4,plain,(
    ! [A_3,B_4,C_5] : k4_xboole_0(k4_xboole_0(A_3,B_4),C_5) = k4_xboole_0(A_3,k2_xboole_0(B_4,C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_177,plain,(
    ! [A_3,B_4,C_5,C_22] : k4_xboole_0(k4_xboole_0(A_3,k2_xboole_0(B_4,C_5)),C_22) = k4_xboole_0(k4_xboole_0(A_3,B_4),k2_xboole_0(C_5,C_22)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_165])).

tff(c_201,plain,(
    ! [A_3,B_4,C_5,C_22] : k4_xboole_0(A_3,k2_xboole_0(k2_xboole_0(B_4,C_5),C_22)) = k4_xboole_0(A_3,k2_xboole_0(B_4,k2_xboole_0(C_5,C_22))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_4,c_177])).

tff(c_33,plain,(
    ! [A_12,B_13] :
      ( r1_xboole_0(A_12,B_13)
      | k4_xboole_0(A_12,B_13) != A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_153,plain,(
    ! [B_18,A_19] :
      ( r1_xboole_0(B_18,A_19)
      | k4_xboole_0(A_19,B_18) != A_19 ) ),
    inference(resolution,[status(thm)],[c_33,c_2])).

tff(c_12,plain,(
    ~ r1_xboole_0(k2_xboole_0(k2_xboole_0('#skF_1','#skF_2'),'#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_162,plain,(
    k4_xboole_0('#skF_4',k2_xboole_0(k2_xboole_0('#skF_1','#skF_2'),'#skF_3')) != '#skF_4' ),
    inference(resolution,[status(thm)],[c_153,c_12])).

tff(c_376,plain,(
    k4_xboole_0('#skF_4',k2_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3'))) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_201,c_162])).

tff(c_379,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_186,c_189,c_376])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:30:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.17/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.29  
% 2.17/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.29  %$ r1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.17/1.29  
% 2.17/1.29  %Foreground sorts:
% 2.17/1.29  
% 2.17/1.29  
% 2.17/1.29  %Background operators:
% 2.17/1.29  
% 2.17/1.29  
% 2.17/1.29  %Foreground operators:
% 2.17/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.17/1.29  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.17/1.29  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.17/1.29  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.17/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.17/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.17/1.29  tff('#skF_1', type, '#skF_1': $i).
% 2.17/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.17/1.29  tff('#skF_4', type, '#skF_4': $i).
% 2.17/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.17/1.29  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.17/1.29  
% 2.17/1.30  tff(f_46, negated_conjecture, ~(![A, B, C, D]: (((r1_xboole_0(A, D) & r1_xboole_0(B, D)) & r1_xboole_0(C, D)) => r1_xboole_0(k2_xboole_0(k2_xboole_0(A, B), C), D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t114_xboole_1)).
% 2.17/1.30  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.17/1.30  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.17/1.30  tff(f_31, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 2.17/1.30  tff(c_14, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.17/1.30  tff(c_19, plain, (![B_10, A_11]: (r1_xboole_0(B_10, A_11) | ~r1_xboole_0(A_11, B_10))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.17/1.30  tff(c_26, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_14, c_19])).
% 2.17/1.30  tff(c_45, plain, (![A_14, B_15]: (k4_xboole_0(A_14, B_15)=A_14 | ~r1_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.17/1.30  tff(c_70, plain, (k4_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_26, c_45])).
% 2.17/1.30  tff(c_16, plain, (r1_xboole_0('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.17/1.30  tff(c_27, plain, (r1_xboole_0('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_16, c_19])).
% 2.17/1.30  tff(c_67, plain, (k4_xboole_0('#skF_4', '#skF_2')='#skF_4'), inference(resolution, [status(thm)], [c_27, c_45])).
% 2.17/1.30  tff(c_165, plain, (![A_20, B_21, C_22]: (k4_xboole_0(k4_xboole_0(A_20, B_21), C_22)=k4_xboole_0(A_20, k2_xboole_0(B_21, C_22)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.17/1.30  tff(c_186, plain, (![C_22]: (k4_xboole_0('#skF_4', k2_xboole_0('#skF_2', C_22))=k4_xboole_0('#skF_4', C_22))), inference(superposition, [status(thm), theory('equality')], [c_67, c_165])).
% 2.17/1.30  tff(c_18, plain, (r1_xboole_0('#skF_1', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.17/1.30  tff(c_28, plain, (r1_xboole_0('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_18, c_19])).
% 2.17/1.30  tff(c_68, plain, (k4_xboole_0('#skF_4', '#skF_1')='#skF_4'), inference(resolution, [status(thm)], [c_28, c_45])).
% 2.17/1.30  tff(c_189, plain, (![C_22]: (k4_xboole_0('#skF_4', k2_xboole_0('#skF_1', C_22))=k4_xboole_0('#skF_4', C_22))), inference(superposition, [status(thm), theory('equality')], [c_68, c_165])).
% 2.17/1.30  tff(c_4, plain, (![A_3, B_4, C_5]: (k4_xboole_0(k4_xboole_0(A_3, B_4), C_5)=k4_xboole_0(A_3, k2_xboole_0(B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.17/1.30  tff(c_177, plain, (![A_3, B_4, C_5, C_22]: (k4_xboole_0(k4_xboole_0(A_3, k2_xboole_0(B_4, C_5)), C_22)=k4_xboole_0(k4_xboole_0(A_3, B_4), k2_xboole_0(C_5, C_22)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_165])).
% 2.17/1.30  tff(c_201, plain, (![A_3, B_4, C_5, C_22]: (k4_xboole_0(A_3, k2_xboole_0(k2_xboole_0(B_4, C_5), C_22))=k4_xboole_0(A_3, k2_xboole_0(B_4, k2_xboole_0(C_5, C_22))))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_4, c_177])).
% 2.17/1.30  tff(c_33, plain, (![A_12, B_13]: (r1_xboole_0(A_12, B_13) | k4_xboole_0(A_12, B_13)!=A_12)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.17/1.30  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.17/1.30  tff(c_153, plain, (![B_18, A_19]: (r1_xboole_0(B_18, A_19) | k4_xboole_0(A_19, B_18)!=A_19)), inference(resolution, [status(thm)], [c_33, c_2])).
% 2.17/1.30  tff(c_12, plain, (~r1_xboole_0(k2_xboole_0(k2_xboole_0('#skF_1', '#skF_2'), '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.17/1.30  tff(c_162, plain, (k4_xboole_0('#skF_4', k2_xboole_0(k2_xboole_0('#skF_1', '#skF_2'), '#skF_3'))!='#skF_4'), inference(resolution, [status(thm)], [c_153, c_12])).
% 2.17/1.30  tff(c_376, plain, (k4_xboole_0('#skF_4', k2_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3')))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_201, c_162])).
% 2.17/1.30  tff(c_379, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_186, c_189, c_376])).
% 2.17/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.30  
% 2.17/1.30  Inference rules
% 2.17/1.30  ----------------------
% 2.17/1.30  #Ref     : 0
% 2.17/1.30  #Sup     : 107
% 2.17/1.30  #Fact    : 0
% 2.17/1.30  #Define  : 0
% 2.17/1.30  #Split   : 0
% 2.17/1.30  #Chain   : 0
% 2.17/1.30  #Close   : 0
% 2.17/1.30  
% 2.17/1.30  Ordering : KBO
% 2.17/1.30  
% 2.17/1.30  Simplification rules
% 2.17/1.30  ----------------------
% 2.17/1.30  #Subsume      : 1
% 2.17/1.30  #Demod        : 36
% 2.17/1.30  #Tautology    : 58
% 2.17/1.30  #SimpNegUnit  : 0
% 2.17/1.30  #BackRed      : 1
% 2.17/1.30  
% 2.17/1.30  #Partial instantiations: 0
% 2.17/1.30  #Strategies tried      : 1
% 2.17/1.30  
% 2.17/1.30  Timing (in seconds)
% 2.17/1.30  ----------------------
% 2.17/1.31  Preprocessing        : 0.26
% 2.17/1.31  Parsing              : 0.14
% 2.17/1.31  CNF conversion       : 0.02
% 2.17/1.31  Main loop            : 0.26
% 2.17/1.31  Inferencing          : 0.11
% 2.17/1.31  Reduction            : 0.08
% 2.17/1.31  Demodulation         : 0.06
% 2.17/1.31  BG Simplification    : 0.01
% 2.17/1.31  Subsumption          : 0.04
% 2.17/1.31  Abstraction          : 0.01
% 2.17/1.31  MUC search           : 0.00
% 2.17/1.31  Cooper               : 0.00
% 2.17/1.31  Total                : 0.55
% 2.17/1.31  Index Insertion      : 0.00
% 2.17/1.31  Index Deletion       : 0.00
% 2.17/1.31  Index Matching       : 0.00
% 2.17/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
