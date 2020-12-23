%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:33 EST 2020

% Result     : Theorem 2.27s
% Output     : CNFRefutation 2.27s
% Verified   : 
% Statistics : Number of formulae       :   39 (  53 expanded)
%              Number of leaves         :   15 (  25 expanded)
%              Depth                    :    6
%              Number of atoms          :   39 (  72 expanded)
%              Number of equality atoms :   16 (  22 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(c_16,plain,(
    r1_xboole_0('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_20,plain,(
    ! [B_10,A_11] :
      ( r1_xboole_0(B_10,A_11)
      | ~ r1_xboole_0(A_11,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_28,plain,(
    r1_xboole_0('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_20])).

tff(c_83,plain,(
    ! [A_16,B_17] :
      ( k4_xboole_0(A_16,B_17) = A_16
      | ~ r1_xboole_0(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_106,plain,(
    k4_xboole_0('#skF_4','#skF_2') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_28,c_83])).

tff(c_18,plain,(
    r1_xboole_0('#skF_1','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_29,plain,(
    r1_xboole_0('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_20])).

tff(c_107,plain,(
    k4_xboole_0('#skF_4','#skF_1') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_29,c_83])).

tff(c_6,plain,(
    ! [A_5,B_6,C_7] : k4_xboole_0(k4_xboole_0(A_5,B_6),C_7) = k4_xboole_0(A_5,k2_xboole_0(B_6,C_7)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_160,plain,(
    ! [C_7] : k4_xboole_0('#skF_4',k2_xboole_0('#skF_1',C_7)) = k4_xboole_0('#skF_4',C_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_6])).

tff(c_14,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_27,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_20])).

tff(c_108,plain,(
    k4_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_27,c_83])).

tff(c_128,plain,(
    ! [A_18,B_19,C_20] : k4_xboole_0(k4_xboole_0(A_18,B_19),C_20) = k4_xboole_0(A_18,k2_xboole_0(B_19,C_20)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_143,plain,(
    ! [C_20] : k4_xboole_0('#skF_4',k2_xboole_0('#skF_3',C_20)) = k4_xboole_0('#skF_4',C_20) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_128])).

tff(c_75,plain,(
    ! [A_14,B_15] :
      ( r1_xboole_0(A_14,B_15)
      | k4_xboole_0(A_14,B_15) != A_14 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_171,plain,(
    ! [B_21,A_22] :
      ( r1_xboole_0(B_21,A_22)
      | k4_xboole_0(A_22,B_21) != A_22 ) ),
    inference(resolution,[status(thm)],[c_75,c_4])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ~ r1_xboole_0(k2_xboole_0(k2_xboole_0('#skF_1','#skF_2'),'#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_19,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_3',k2_xboole_0('#skF_1','#skF_2')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_12])).

tff(c_181,plain,(
    k4_xboole_0('#skF_4',k2_xboole_0('#skF_3',k2_xboole_0('#skF_1','#skF_2'))) != '#skF_4' ),
    inference(resolution,[status(thm)],[c_171,c_19])).

tff(c_409,plain,(
    k4_xboole_0('#skF_4',k2_xboole_0('#skF_1','#skF_2')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_181])).

tff(c_412,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_160,c_409])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:50:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.27/1.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.39  
% 2.27/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.39  %$ r1_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.27/1.39  
% 2.27/1.39  %Foreground sorts:
% 2.27/1.39  
% 2.27/1.39  
% 2.27/1.39  %Background operators:
% 2.27/1.39  
% 2.27/1.39  
% 2.27/1.39  %Foreground operators:
% 2.27/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.27/1.39  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.27/1.39  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.27/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.27/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.27/1.39  tff('#skF_1', type, '#skF_1': $i).
% 2.27/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.27/1.39  tff('#skF_4', type, '#skF_4': $i).
% 2.27/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.27/1.39  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.27/1.39  
% 2.27/1.40  tff(f_46, negated_conjecture, ~(![A, B, C, D]: (((r1_xboole_0(A, D) & r1_xboole_0(B, D)) & r1_xboole_0(C, D)) => r1_xboole_0(k2_xboole_0(k2_xboole_0(A, B), C), D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t114_xboole_1)).
% 2.27/1.40  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.27/1.40  tff(f_37, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.27/1.40  tff(f_33, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 2.27/1.40  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.27/1.40  tff(c_16, plain, (r1_xboole_0('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.27/1.40  tff(c_20, plain, (![B_10, A_11]: (r1_xboole_0(B_10, A_11) | ~r1_xboole_0(A_11, B_10))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.27/1.40  tff(c_28, plain, (r1_xboole_0('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_16, c_20])).
% 2.27/1.40  tff(c_83, plain, (![A_16, B_17]: (k4_xboole_0(A_16, B_17)=A_16 | ~r1_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.27/1.40  tff(c_106, plain, (k4_xboole_0('#skF_4', '#skF_2')='#skF_4'), inference(resolution, [status(thm)], [c_28, c_83])).
% 2.27/1.40  tff(c_18, plain, (r1_xboole_0('#skF_1', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.27/1.40  tff(c_29, plain, (r1_xboole_0('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_18, c_20])).
% 2.27/1.40  tff(c_107, plain, (k4_xboole_0('#skF_4', '#skF_1')='#skF_4'), inference(resolution, [status(thm)], [c_29, c_83])).
% 2.27/1.40  tff(c_6, plain, (![A_5, B_6, C_7]: (k4_xboole_0(k4_xboole_0(A_5, B_6), C_7)=k4_xboole_0(A_5, k2_xboole_0(B_6, C_7)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.27/1.40  tff(c_160, plain, (![C_7]: (k4_xboole_0('#skF_4', k2_xboole_0('#skF_1', C_7))=k4_xboole_0('#skF_4', C_7))), inference(superposition, [status(thm), theory('equality')], [c_107, c_6])).
% 2.27/1.40  tff(c_14, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.27/1.40  tff(c_27, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_14, c_20])).
% 2.27/1.40  tff(c_108, plain, (k4_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_27, c_83])).
% 2.27/1.40  tff(c_128, plain, (![A_18, B_19, C_20]: (k4_xboole_0(k4_xboole_0(A_18, B_19), C_20)=k4_xboole_0(A_18, k2_xboole_0(B_19, C_20)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.27/1.40  tff(c_143, plain, (![C_20]: (k4_xboole_0('#skF_4', k2_xboole_0('#skF_3', C_20))=k4_xboole_0('#skF_4', C_20))), inference(superposition, [status(thm), theory('equality')], [c_108, c_128])).
% 2.27/1.40  tff(c_75, plain, (![A_14, B_15]: (r1_xboole_0(A_14, B_15) | k4_xboole_0(A_14, B_15)!=A_14)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.27/1.40  tff(c_4, plain, (![B_4, A_3]: (r1_xboole_0(B_4, A_3) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.27/1.40  tff(c_171, plain, (![B_21, A_22]: (r1_xboole_0(B_21, A_22) | k4_xboole_0(A_22, B_21)!=A_22)), inference(resolution, [status(thm)], [c_75, c_4])).
% 2.27/1.40  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.27/1.40  tff(c_12, plain, (~r1_xboole_0(k2_xboole_0(k2_xboole_0('#skF_1', '#skF_2'), '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.27/1.40  tff(c_19, plain, (~r1_xboole_0(k2_xboole_0('#skF_3', k2_xboole_0('#skF_1', '#skF_2')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_12])).
% 2.27/1.40  tff(c_181, plain, (k4_xboole_0('#skF_4', k2_xboole_0('#skF_3', k2_xboole_0('#skF_1', '#skF_2')))!='#skF_4'), inference(resolution, [status(thm)], [c_171, c_19])).
% 2.27/1.40  tff(c_409, plain, (k4_xboole_0('#skF_4', k2_xboole_0('#skF_1', '#skF_2'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_143, c_181])).
% 2.27/1.40  tff(c_412, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_106, c_160, c_409])).
% 2.27/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.40  
% 2.27/1.40  Inference rules
% 2.27/1.40  ----------------------
% 2.27/1.40  #Ref     : 0
% 2.27/1.40  #Sup     : 103
% 2.27/1.40  #Fact    : 0
% 2.27/1.40  #Define  : 0
% 2.27/1.40  #Split   : 0
% 2.27/1.40  #Chain   : 0
% 2.27/1.40  #Close   : 0
% 2.27/1.40  
% 2.27/1.40  Ordering : KBO
% 2.27/1.40  
% 2.27/1.40  Simplification rules
% 2.27/1.40  ----------------------
% 2.27/1.40  #Subsume      : 1
% 2.27/1.40  #Demod        : 44
% 2.27/1.40  #Tautology    : 60
% 2.27/1.40  #SimpNegUnit  : 0
% 2.27/1.40  #BackRed      : 1
% 2.27/1.40  
% 2.27/1.40  #Partial instantiations: 0
% 2.27/1.40  #Strategies tried      : 1
% 2.27/1.40  
% 2.27/1.40  Timing (in seconds)
% 2.27/1.40  ----------------------
% 2.27/1.41  Preprocessing        : 0.30
% 2.27/1.41  Parsing              : 0.15
% 2.27/1.41  CNF conversion       : 0.02
% 2.27/1.41  Main loop            : 0.30
% 2.27/1.41  Inferencing          : 0.11
% 2.27/1.41  Reduction            : 0.12
% 2.27/1.41  Demodulation         : 0.09
% 2.27/1.41  BG Simplification    : 0.01
% 2.27/1.41  Subsumption          : 0.05
% 2.27/1.41  Abstraction          : 0.01
% 2.27/1.41  MUC search           : 0.00
% 2.27/1.41  Cooper               : 0.00
% 2.27/1.41  Total                : 0.63
% 2.27/1.41  Index Insertion      : 0.00
% 2.27/1.41  Index Deletion       : 0.00
% 2.27/1.41  Index Matching       : 0.00
% 2.27/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
