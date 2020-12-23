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
% DateTime   : Thu Dec  3 09:44:07 EST 2020

% Result     : Theorem 1.84s
% Output     : CNFRefutation 1.84s
% Verified   : 
% Statistics : Number of formulae       :   35 (  38 expanded)
%              Number of leaves         :   18 (  21 expanded)
%              Depth                    :    6
%              Number of atoms          :   30 (  38 expanded)
%              Number of equality atoms :   17 (  18 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_50,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r1_xboole_0(A,B)
          & r1_tarski(A,C)
          & r1_xboole_0(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_80,plain,(
    ! [A_20,B_21] :
      ( r1_xboole_0(A_20,B_21)
      | k3_xboole_0(A_20,B_21) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_20,plain,(
    ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_84,plain,(
    k3_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_80,c_20])).

tff(c_18,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_64,plain,(
    ! [A_18,B_19] :
      ( k2_xboole_0(A_18,B_19) = B_19
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_68,plain,(
    k2_xboole_0('#skF_1','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_18,c_64])).

tff(c_12,plain,(
    ! [A_10,B_11] : k3_xboole_0(A_10,k2_xboole_0(A_10,B_11)) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_72,plain,(
    k3_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_12])).

tff(c_113,plain,(
    ! [A_26,B_27,C_28] : k3_xboole_0(k3_xboole_0(A_26,B_27),C_28) = k3_xboole_0(A_26,k3_xboole_0(B_27,C_28)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_168,plain,(
    ! [C_29] : k3_xboole_0('#skF_1',k3_xboole_0('#skF_3',C_29)) = k3_xboole_0('#skF_1',C_29) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_113])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_16,plain,(
    r1_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_21,plain,(
    r1_xboole_0('#skF_1',k3_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_16])).

tff(c_85,plain,(
    ! [A_22,B_23] :
      ( k3_xboole_0(A_22,B_23) = k1_xboole_0
      | ~ r1_xboole_0(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_93,plain,(
    k3_xboole_0('#skF_1',k3_xboole_0('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_21,c_85])).

tff(c_177,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_93])).

tff(c_199,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_177])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:46:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.84/1.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.84/1.17  
% 1.84/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.84/1.17  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.84/1.17  
% 1.84/1.17  %Foreground sorts:
% 1.84/1.17  
% 1.84/1.17  
% 1.84/1.17  %Background operators:
% 1.84/1.17  
% 1.84/1.17  
% 1.84/1.17  %Foreground operators:
% 1.84/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.84/1.17  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.84/1.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.84/1.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.84/1.17  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.84/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.84/1.17  tff('#skF_3', type, '#skF_3': $i).
% 1.84/1.17  tff('#skF_1', type, '#skF_1': $i).
% 1.84/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.84/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.84/1.17  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.84/1.17  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.84/1.17  
% 1.84/1.18  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 1.84/1.18  tff(f_50, negated_conjecture, ~(![A, B, C]: ~((~r1_xboole_0(A, B) & r1_tarski(A, C)) & r1_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_xboole_1)).
% 1.84/1.18  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.84/1.18  tff(f_39, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_xboole_1)).
% 1.84/1.18  tff(f_37, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 1.84/1.18  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.84/1.18  tff(c_80, plain, (![A_20, B_21]: (r1_xboole_0(A_20, B_21) | k3_xboole_0(A_20, B_21)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.84/1.18  tff(c_20, plain, (~r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.84/1.18  tff(c_84, plain, (k3_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_80, c_20])).
% 1.84/1.18  tff(c_18, plain, (r1_tarski('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.84/1.18  tff(c_64, plain, (![A_18, B_19]: (k2_xboole_0(A_18, B_19)=B_19 | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.84/1.18  tff(c_68, plain, (k2_xboole_0('#skF_1', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_18, c_64])).
% 1.84/1.18  tff(c_12, plain, (![A_10, B_11]: (k3_xboole_0(A_10, k2_xboole_0(A_10, B_11))=A_10)), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.84/1.18  tff(c_72, plain, (k3_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_68, c_12])).
% 1.84/1.18  tff(c_113, plain, (![A_26, B_27, C_28]: (k3_xboole_0(k3_xboole_0(A_26, B_27), C_28)=k3_xboole_0(A_26, k3_xboole_0(B_27, C_28)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.84/1.18  tff(c_168, plain, (![C_29]: (k3_xboole_0('#skF_1', k3_xboole_0('#skF_3', C_29))=k3_xboole_0('#skF_1', C_29))), inference(superposition, [status(thm), theory('equality')], [c_72, c_113])).
% 1.84/1.18  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.84/1.18  tff(c_16, plain, (r1_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.84/1.18  tff(c_21, plain, (r1_xboole_0('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_16])).
% 1.84/1.18  tff(c_85, plain, (![A_22, B_23]: (k3_xboole_0(A_22, B_23)=k1_xboole_0 | ~r1_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.84/1.18  tff(c_93, plain, (k3_xboole_0('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_21, c_85])).
% 1.84/1.18  tff(c_177, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_168, c_93])).
% 1.84/1.18  tff(c_199, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_177])).
% 1.84/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.84/1.18  
% 1.84/1.18  Inference rules
% 1.84/1.18  ----------------------
% 1.84/1.18  #Ref     : 0
% 1.84/1.18  #Sup     : 48
% 1.84/1.18  #Fact    : 0
% 1.84/1.18  #Define  : 0
% 1.84/1.18  #Split   : 0
% 1.84/1.18  #Chain   : 0
% 1.84/1.18  #Close   : 0
% 1.84/1.18  
% 1.84/1.18  Ordering : KBO
% 1.84/1.18  
% 1.84/1.18  Simplification rules
% 1.84/1.18  ----------------------
% 1.84/1.18  #Subsume      : 0
% 1.84/1.18  #Demod        : 11
% 1.84/1.18  #Tautology    : 25
% 1.84/1.18  #SimpNegUnit  : 1
% 1.84/1.18  #BackRed      : 0
% 1.84/1.18  
% 1.84/1.18  #Partial instantiations: 0
% 1.84/1.18  #Strategies tried      : 1
% 1.84/1.18  
% 1.84/1.18  Timing (in seconds)
% 1.84/1.18  ----------------------
% 1.84/1.18  Preprocessing        : 0.26
% 1.84/1.18  Parsing              : 0.14
% 1.84/1.18  CNF conversion       : 0.02
% 1.84/1.18  Main loop            : 0.17
% 1.84/1.18  Inferencing          : 0.06
% 1.84/1.18  Reduction            : 0.07
% 1.84/1.18  Demodulation         : 0.06
% 1.84/1.18  BG Simplification    : 0.01
% 1.84/1.18  Subsumption          : 0.02
% 1.84/1.18  Abstraction          : 0.01
% 1.84/1.18  MUC search           : 0.00
% 1.84/1.19  Cooper               : 0.00
% 1.84/1.19  Total                : 0.45
% 1.84/1.19  Index Insertion      : 0.00
% 1.84/1.19  Index Deletion       : 0.00
% 1.84/1.19  Index Matching       : 0.00
% 1.84/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
