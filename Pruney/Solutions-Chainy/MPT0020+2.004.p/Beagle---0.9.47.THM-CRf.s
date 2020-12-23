%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:31 EST 2020

% Result     : Theorem 7.64s
% Output     : CNFRefutation 7.64s
% Verified   : 
% Statistics : Number of formulae       :   34 (  50 expanded)
%              Number of leaves         :   14 (  23 expanded)
%              Depth                    :    6
%              Number of atoms          :   29 (  51 expanded)
%              Number of equality atoms :   13 (  27 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_42,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(A,B)
          & r1_tarski(C,D) )
       => r1_tarski(k2_xboole_0(A,C),k2_xboole_0(B,D)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ~ r1_tarski(k2_xboole_0('#skF_1','#skF_3'),k2_xboole_0('#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_15,plain,(
    ~ r1_tarski(k2_xboole_0('#skF_1','#skF_3'),k2_xboole_0('#skF_4','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_10])).

tff(c_14,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_66,plain,(
    ! [A_16,B_17] :
      ( k2_xboole_0(A_16,B_17) = B_17
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_82,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_14,c_66])).

tff(c_139,plain,(
    ! [A_18,B_19,C_20] : k2_xboole_0(k2_xboole_0(A_18,B_19),C_20) = k2_xboole_0(A_18,k2_xboole_0(B_19,C_20)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1162,plain,(
    ! [A_44,A_42,B_43] : k2_xboole_0(A_44,k2_xboole_0(A_42,B_43)) = k2_xboole_0(A_42,k2_xboole_0(B_43,A_44)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_139])).

tff(c_3193,plain,(
    ! [A_70] : k2_xboole_0('#skF_2',k2_xboole_0(A_70,'#skF_1')) = k2_xboole_0(A_70,'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_1162])).

tff(c_3336,plain,(
    ! [A_1] : k2_xboole_0('#skF_2',k2_xboole_0('#skF_1',A_1)) = k2_xboole_0(A_1,'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_3193])).

tff(c_12,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_81,plain,(
    k2_xboole_0('#skF_3','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_12,c_66])).

tff(c_3473,plain,(
    ! [A_73] : k2_xboole_0('#skF_4',k2_xboole_0(A_73,'#skF_3')) = k2_xboole_0(A_73,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_1162])).

tff(c_17,plain,(
    ! [B_12,A_13] : k2_xboole_0(B_12,A_13) = k2_xboole_0(A_13,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_8,B_9] : r1_tarski(A_8,k2_xboole_0(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_32,plain,(
    ! [A_13,B_12] : r1_tarski(A_13,k2_xboole_0(B_12,A_13)) ),
    inference(superposition,[status(thm),theory(equality)],[c_17,c_8])).

tff(c_148,plain,(
    ! [C_20,A_18,B_19] : r1_tarski(C_20,k2_xboole_0(A_18,k2_xboole_0(B_19,C_20))) ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_32])).

tff(c_11501,plain,(
    ! [A_113,A_114] : r1_tarski(k2_xboole_0(A_113,'#skF_3'),k2_xboole_0(A_114,k2_xboole_0(A_113,'#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_3473,c_148])).

tff(c_11521,plain,(
    r1_tarski(k2_xboole_0('#skF_1','#skF_3'),k2_xboole_0('#skF_4','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3336,c_11501])).

tff(c_11659,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_15,c_11521])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:56:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.64/2.63  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.64/2.64  
% 7.64/2.64  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.64/2.64  %$ r1_tarski > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.64/2.64  
% 7.64/2.64  %Foreground sorts:
% 7.64/2.64  
% 7.64/2.64  
% 7.64/2.64  %Background operators:
% 7.64/2.64  
% 7.64/2.64  
% 7.64/2.64  %Foreground operators:
% 7.64/2.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.64/2.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.64/2.64  tff('#skF_2', type, '#skF_2': $i).
% 7.64/2.64  tff('#skF_3', type, '#skF_3': $i).
% 7.64/2.64  tff('#skF_1', type, '#skF_1': $i).
% 7.64/2.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.64/2.64  tff('#skF_4', type, '#skF_4': $i).
% 7.64/2.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.64/2.64  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.64/2.64  
% 7.64/2.65  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 7.64/2.65  tff(f_42, negated_conjecture, ~(![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k2_xboole_0(A, C), k2_xboole_0(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_xboole_1)).
% 7.64/2.65  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 7.64/2.65  tff(f_33, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 7.64/2.65  tff(f_35, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 7.64/2.65  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.64/2.65  tff(c_10, plain, (~r1_tarski(k2_xboole_0('#skF_1', '#skF_3'), k2_xboole_0('#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_42])).
% 7.64/2.65  tff(c_15, plain, (~r1_tarski(k2_xboole_0('#skF_1', '#skF_3'), k2_xboole_0('#skF_4', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_10])).
% 7.64/2.65  tff(c_14, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_42])).
% 7.64/2.65  tff(c_66, plain, (![A_16, B_17]: (k2_xboole_0(A_16, B_17)=B_17 | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.64/2.65  tff(c_82, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_14, c_66])).
% 7.64/2.65  tff(c_139, plain, (![A_18, B_19, C_20]: (k2_xboole_0(k2_xboole_0(A_18, B_19), C_20)=k2_xboole_0(A_18, k2_xboole_0(B_19, C_20)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.64/2.65  tff(c_1162, plain, (![A_44, A_42, B_43]: (k2_xboole_0(A_44, k2_xboole_0(A_42, B_43))=k2_xboole_0(A_42, k2_xboole_0(B_43, A_44)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_139])).
% 7.64/2.65  tff(c_3193, plain, (![A_70]: (k2_xboole_0('#skF_2', k2_xboole_0(A_70, '#skF_1'))=k2_xboole_0(A_70, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_82, c_1162])).
% 7.64/2.65  tff(c_3336, plain, (![A_1]: (k2_xboole_0('#skF_2', k2_xboole_0('#skF_1', A_1))=k2_xboole_0(A_1, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2, c_3193])).
% 7.64/2.65  tff(c_12, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_42])).
% 7.64/2.65  tff(c_81, plain, (k2_xboole_0('#skF_3', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_12, c_66])).
% 7.64/2.65  tff(c_3473, plain, (![A_73]: (k2_xboole_0('#skF_4', k2_xboole_0(A_73, '#skF_3'))=k2_xboole_0(A_73, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_81, c_1162])).
% 7.64/2.65  tff(c_17, plain, (![B_12, A_13]: (k2_xboole_0(B_12, A_13)=k2_xboole_0(A_13, B_12))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.64/2.65  tff(c_8, plain, (![A_8, B_9]: (r1_tarski(A_8, k2_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.64/2.65  tff(c_32, plain, (![A_13, B_12]: (r1_tarski(A_13, k2_xboole_0(B_12, A_13)))), inference(superposition, [status(thm), theory('equality')], [c_17, c_8])).
% 7.64/2.65  tff(c_148, plain, (![C_20, A_18, B_19]: (r1_tarski(C_20, k2_xboole_0(A_18, k2_xboole_0(B_19, C_20))))), inference(superposition, [status(thm), theory('equality')], [c_139, c_32])).
% 7.64/2.65  tff(c_11501, plain, (![A_113, A_114]: (r1_tarski(k2_xboole_0(A_113, '#skF_3'), k2_xboole_0(A_114, k2_xboole_0(A_113, '#skF_4'))))), inference(superposition, [status(thm), theory('equality')], [c_3473, c_148])).
% 7.64/2.65  tff(c_11521, plain, (r1_tarski(k2_xboole_0('#skF_1', '#skF_3'), k2_xboole_0('#skF_4', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_3336, c_11501])).
% 7.64/2.65  tff(c_11659, plain, $false, inference(negUnitSimplification, [status(thm)], [c_15, c_11521])).
% 7.64/2.65  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.64/2.65  
% 7.64/2.65  Inference rules
% 7.64/2.65  ----------------------
% 7.64/2.65  #Ref     : 0
% 7.64/2.65  #Sup     : 2816
% 7.64/2.65  #Fact    : 0
% 7.64/2.65  #Define  : 0
% 7.64/2.65  #Split   : 0
% 7.64/2.65  #Chain   : 0
% 7.64/2.65  #Close   : 0
% 7.64/2.65  
% 7.64/2.65  Ordering : KBO
% 7.64/2.65  
% 7.64/2.65  Simplification rules
% 7.64/2.65  ----------------------
% 7.64/2.65  #Subsume      : 151
% 7.64/2.65  #Demod        : 3639
% 7.64/2.65  #Tautology    : 1874
% 7.64/2.65  #SimpNegUnit  : 1
% 7.64/2.65  #BackRed      : 0
% 7.64/2.65  
% 7.64/2.65  #Partial instantiations: 0
% 7.64/2.65  #Strategies tried      : 1
% 7.64/2.65  
% 7.64/2.65  Timing (in seconds)
% 7.64/2.65  ----------------------
% 7.64/2.65  Preprocessing        : 0.25
% 7.64/2.65  Parsing              : 0.14
% 7.64/2.65  CNF conversion       : 0.01
% 7.64/2.65  Main loop            : 1.65
% 7.64/2.65  Inferencing          : 0.36
% 7.64/2.65  Reduction            : 0.98
% 7.64/2.65  Demodulation         : 0.87
% 7.64/2.65  BG Simplification    : 0.04
% 7.64/2.65  Subsumption          : 0.20
% 7.64/2.65  Abstraction          : 0.06
% 7.64/2.65  MUC search           : 0.00
% 7.64/2.65  Cooper               : 0.00
% 7.64/2.65  Total                : 1.92
% 7.64/2.65  Index Insertion      : 0.00
% 7.64/2.65  Index Deletion       : 0.00
% 7.64/2.65  Index Matching       : 0.00
% 7.64/2.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
