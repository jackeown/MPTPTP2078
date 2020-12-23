%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:32 EST 2020

% Result     : Theorem 5.77s
% Output     : CNFRefutation 5.77s
% Verified   : 
% Statistics : Number of formulae       :   33 (  44 expanded)
%              Number of leaves         :   13 (  21 expanded)
%              Depth                    :    7
%              Number of atoms          :   39 (  68 expanded)
%              Number of equality atoms :   18 (  27 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_49,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_tarski(C,B)
          & ! [D] :
              ( ( r1_tarski(A,D)
                & r1_tarski(C,D) )
             => r1_tarski(B,D) ) )
       => B = k2_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(c_10,plain,(
    k2_xboole_0('#skF_1','#skF_3') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_14,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_57,plain,(
    ! [A_16,B_17] :
      ( k2_xboole_0(A_16,B_17) = B_17
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_68,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_14,c_57])).

tff(c_16,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_69,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_16,c_57])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_18,plain,(
    ! [B_14,A_15] : k2_xboole_0(B_14,A_15) = k2_xboole_0(A_15,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_8,B_9] : r1_tarski(A_8,k2_xboole_0(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_36,plain,(
    ! [B_14,A_15] : r1_tarski(B_14,k2_xboole_0(A_15,B_14)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_8])).

tff(c_170,plain,(
    ! [A_23,B_24,C_25] : k2_xboole_0(k2_xboole_0(A_23,B_24),C_25) = k2_xboole_0(A_23,k2_xboole_0(B_24,C_25)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_224,plain,(
    ! [B_2,A_23,B_24] : k2_xboole_0(B_2,k2_xboole_0(A_23,B_24)) = k2_xboole_0(A_23,k2_xboole_0(B_24,B_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_170])).

tff(c_105,plain,(
    ! [D_20] :
      ( r1_tarski('#skF_2',D_20)
      | ~ r1_tarski('#skF_3',D_20)
      | ~ r1_tarski('#skF_1',D_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k2_xboole_0(A_3,B_4) = B_4
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_405,plain,(
    ! [D_33] :
      ( k2_xboole_0('#skF_2',D_33) = D_33
      | ~ r1_tarski('#skF_3',D_33)
      | ~ r1_tarski('#skF_1',D_33) ) ),
    inference(resolution,[status(thm)],[c_105,c_4])).

tff(c_423,plain,(
    ! [B_9] :
      ( k2_xboole_0('#skF_2',k2_xboole_0('#skF_3',B_9)) = k2_xboole_0('#skF_3',B_9)
      | ~ r1_tarski('#skF_1',k2_xboole_0('#skF_3',B_9)) ) ),
    inference(resolution,[status(thm)],[c_8,c_405])).

tff(c_5544,plain,(
    ! [B_86] :
      ( k2_xboole_0('#skF_3',k2_xboole_0(B_86,'#skF_2')) = k2_xboole_0('#skF_3',B_86)
      | ~ r1_tarski('#skF_1',k2_xboole_0('#skF_3',B_86)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_224,c_423])).

tff(c_5594,plain,(
    k2_xboole_0('#skF_3',k2_xboole_0('#skF_1','#skF_2')) = k2_xboole_0('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_5544])).

tff(c_5626,plain,(
    k2_xboole_0('#skF_1','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_69,c_2,c_5594])).

tff(c_5628,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_5626])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:44:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.77/2.09  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.77/2.10  
% 5.77/2.10  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.77/2.10  %$ r1_tarski > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 5.77/2.10  
% 5.77/2.10  %Foreground sorts:
% 5.77/2.10  
% 5.77/2.10  
% 5.77/2.10  %Background operators:
% 5.77/2.10  
% 5.77/2.10  
% 5.77/2.10  %Foreground operators:
% 5.77/2.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.77/2.10  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.77/2.10  tff('#skF_2', type, '#skF_2': $i).
% 5.77/2.10  tff('#skF_3', type, '#skF_3': $i).
% 5.77/2.10  tff('#skF_1', type, '#skF_1': $i).
% 5.77/2.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.77/2.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.77/2.10  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.77/2.10  
% 5.77/2.11  tff(f_49, negated_conjecture, ~(![A, B, C]: (((r1_tarski(A, B) & r1_tarski(C, B)) & (![D]: ((r1_tarski(A, D) & r1_tarski(C, D)) => r1_tarski(B, D)))) => (B = k2_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_xboole_1)).
% 5.77/2.11  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 5.77/2.11  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 5.77/2.11  tff(f_35, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 5.77/2.11  tff(f_33, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 5.77/2.11  tff(c_10, plain, (k2_xboole_0('#skF_1', '#skF_3')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.77/2.11  tff(c_14, plain, (r1_tarski('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.77/2.11  tff(c_57, plain, (![A_16, B_17]: (k2_xboole_0(A_16, B_17)=B_17 | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.77/2.11  tff(c_68, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_14, c_57])).
% 5.77/2.11  tff(c_16, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.77/2.11  tff(c_69, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_16, c_57])).
% 5.77/2.11  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.77/2.11  tff(c_18, plain, (![B_14, A_15]: (k2_xboole_0(B_14, A_15)=k2_xboole_0(A_15, B_14))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.77/2.11  tff(c_8, plain, (![A_8, B_9]: (r1_tarski(A_8, k2_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.77/2.11  tff(c_36, plain, (![B_14, A_15]: (r1_tarski(B_14, k2_xboole_0(A_15, B_14)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_8])).
% 5.77/2.11  tff(c_170, plain, (![A_23, B_24, C_25]: (k2_xboole_0(k2_xboole_0(A_23, B_24), C_25)=k2_xboole_0(A_23, k2_xboole_0(B_24, C_25)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.77/2.11  tff(c_224, plain, (![B_2, A_23, B_24]: (k2_xboole_0(B_2, k2_xboole_0(A_23, B_24))=k2_xboole_0(A_23, k2_xboole_0(B_24, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_170])).
% 5.77/2.11  tff(c_105, plain, (![D_20]: (r1_tarski('#skF_2', D_20) | ~r1_tarski('#skF_3', D_20) | ~r1_tarski('#skF_1', D_20))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.77/2.11  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, B_4)=B_4 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.77/2.11  tff(c_405, plain, (![D_33]: (k2_xboole_0('#skF_2', D_33)=D_33 | ~r1_tarski('#skF_3', D_33) | ~r1_tarski('#skF_1', D_33))), inference(resolution, [status(thm)], [c_105, c_4])).
% 5.77/2.11  tff(c_423, plain, (![B_9]: (k2_xboole_0('#skF_2', k2_xboole_0('#skF_3', B_9))=k2_xboole_0('#skF_3', B_9) | ~r1_tarski('#skF_1', k2_xboole_0('#skF_3', B_9)))), inference(resolution, [status(thm)], [c_8, c_405])).
% 5.77/2.11  tff(c_5544, plain, (![B_86]: (k2_xboole_0('#skF_3', k2_xboole_0(B_86, '#skF_2'))=k2_xboole_0('#skF_3', B_86) | ~r1_tarski('#skF_1', k2_xboole_0('#skF_3', B_86)))), inference(demodulation, [status(thm), theory('equality')], [c_224, c_423])).
% 5.77/2.11  tff(c_5594, plain, (k2_xboole_0('#skF_3', k2_xboole_0('#skF_1', '#skF_2'))=k2_xboole_0('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_36, c_5544])).
% 5.77/2.11  tff(c_5626, plain, (k2_xboole_0('#skF_1', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_69, c_2, c_5594])).
% 5.77/2.11  tff(c_5628, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10, c_5626])).
% 5.77/2.11  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.77/2.11  
% 5.77/2.11  Inference rules
% 5.77/2.11  ----------------------
% 5.77/2.11  #Ref     : 0
% 5.77/2.11  #Sup     : 1401
% 5.77/2.11  #Fact    : 0
% 5.77/2.11  #Define  : 0
% 5.77/2.11  #Split   : 0
% 5.77/2.11  #Chain   : 0
% 5.77/2.11  #Close   : 0
% 5.77/2.11  
% 5.77/2.11  Ordering : KBO
% 5.77/2.11  
% 5.77/2.11  Simplification rules
% 5.77/2.11  ----------------------
% 5.77/2.11  #Subsume      : 38
% 5.77/2.11  #Demod        : 1599
% 5.77/2.11  #Tautology    : 829
% 5.77/2.11  #SimpNegUnit  : 1
% 5.77/2.11  #BackRed      : 0
% 5.77/2.11  
% 5.77/2.11  #Partial instantiations: 0
% 5.77/2.11  #Strategies tried      : 1
% 5.77/2.11  
% 5.77/2.11  Timing (in seconds)
% 5.77/2.11  ----------------------
% 5.77/2.11  Preprocessing        : 0.27
% 5.77/2.11  Parsing              : 0.15
% 5.77/2.11  CNF conversion       : 0.02
% 5.77/2.11  Main loop            : 1.08
% 5.77/2.11  Inferencing          : 0.27
% 5.77/2.11  Reduction            : 0.57
% 5.77/2.11  Demodulation         : 0.50
% 5.77/2.11  BG Simplification    : 0.03
% 5.77/2.11  Subsumption          : 0.15
% 5.77/2.11  Abstraction          : 0.04
% 5.77/2.11  MUC search           : 0.00
% 5.77/2.11  Cooper               : 0.00
% 5.77/2.11  Total                : 1.38
% 5.77/2.11  Index Insertion      : 0.00
% 5.77/2.11  Index Deletion       : 0.00
% 5.77/2.11  Index Matching       : 0.00
% 5.77/2.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
