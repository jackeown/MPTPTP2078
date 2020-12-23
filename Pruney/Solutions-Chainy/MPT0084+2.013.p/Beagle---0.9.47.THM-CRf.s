%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:06 EST 2020

% Result     : Theorem 2.03s
% Output     : CNFRefutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :   41 (  50 expanded)
%              Number of leaves         :   19 (  25 expanded)
%              Depth                    :    7
%              Number of atoms          :   39 (  53 expanded)
%              Number of equality atoms :   21 (  28 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r1_xboole_0(A,B)
          & r1_tarski(A,C)
          & r1_xboole_0(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_43,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(c_76,plain,(
    ! [A_20,B_21] :
      ( r1_xboole_0(A_20,B_21)
      | k3_xboole_0(A_20,B_21) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_24,plain,(
    ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_83,plain,(
    k3_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_76,c_24])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_16,plain,(
    ! [A_12] : k4_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_22,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_122,plain,(
    ! [A_26,B_27] :
      ( k4_xboole_0(A_26,B_27) = k1_xboole_0
      | ~ r1_tarski(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_130,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_122])).

tff(c_135,plain,(
    ! [A_28,B_29] : k4_xboole_0(A_28,k4_xboole_0(A_28,B_29)) = k3_xboole_0(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_150,plain,(
    k4_xboole_0('#skF_1',k1_xboole_0) = k3_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_135])).

tff(c_156,plain,(
    k3_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_150])).

tff(c_185,plain,(
    ! [A_31,B_32,C_33] : k3_xboole_0(k3_xboole_0(A_31,B_32),C_33) = k3_xboole_0(A_31,k3_xboole_0(B_32,C_33)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_293,plain,(
    ! [B_37,A_38,C_39] : k3_xboole_0(k3_xboole_0(B_37,A_38),C_39) = k3_xboole_0(A_38,k3_xboole_0(B_37,C_39)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_185])).

tff(c_20,plain,(
    r1_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_25,plain,(
    r1_xboole_0('#skF_1',k3_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_20])).

tff(c_68,plain,(
    ! [B_18,A_19] :
      ( r1_xboole_0(B_18,A_19)
      | ~ r1_xboole_0(A_19,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_71,plain,(
    r1_xboole_0(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_25,c_68])).

tff(c_85,plain,(
    ! [A_24,B_25] :
      ( k3_xboole_0(A_24,B_25) = k1_xboole_0
      | ~ r1_xboole_0(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_96,plain,(
    k3_xboole_0(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_71,c_85])).

tff(c_312,plain,(
    k3_xboole_0('#skF_2',k3_xboole_0('#skF_3','#skF_1')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_293,c_96])).

tff(c_367,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_156,c_2,c_312])).

tff(c_369,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_367])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:35:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.03/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.03/1.27  
% 2.03/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.03/1.27  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.03/1.27  
% 2.03/1.27  %Foreground sorts:
% 2.03/1.27  
% 2.03/1.27  
% 2.03/1.27  %Background operators:
% 2.03/1.27  
% 2.03/1.27  
% 2.03/1.27  %Foreground operators:
% 2.03/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.03/1.27  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.03/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.03/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.03/1.27  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.03/1.27  tff('#skF_2', type, '#skF_2': $i).
% 2.03/1.27  tff('#skF_3', type, '#skF_3': $i).
% 2.03/1.27  tff('#skF_1', type, '#skF_1': $i).
% 2.03/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.03/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.03/1.27  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.03/1.27  
% 2.03/1.29  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.03/1.29  tff(f_54, negated_conjecture, ~(![A, B, C]: ~((~r1_xboole_0(A, B) & r1_tarski(A, C)) & r1_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_xboole_1)).
% 2.03/1.29  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.03/1.29  tff(f_43, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.03/1.29  tff(f_39, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.03/1.29  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.03/1.29  tff(f_41, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 2.03/1.29  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.03/1.29  tff(c_76, plain, (![A_20, B_21]: (r1_xboole_0(A_20, B_21) | k3_xboole_0(A_20, B_21)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.03/1.29  tff(c_24, plain, (~r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.03/1.29  tff(c_83, plain, (k3_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_76, c_24])).
% 2.03/1.29  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.03/1.29  tff(c_16, plain, (![A_12]: (k4_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.03/1.29  tff(c_22, plain, (r1_tarski('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.03/1.29  tff(c_122, plain, (![A_26, B_27]: (k4_xboole_0(A_26, B_27)=k1_xboole_0 | ~r1_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.03/1.29  tff(c_130, plain, (k4_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_22, c_122])).
% 2.03/1.29  tff(c_135, plain, (![A_28, B_29]: (k4_xboole_0(A_28, k4_xboole_0(A_28, B_29))=k3_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.03/1.29  tff(c_150, plain, (k4_xboole_0('#skF_1', k1_xboole_0)=k3_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_130, c_135])).
% 2.03/1.29  tff(c_156, plain, (k3_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_150])).
% 2.03/1.29  tff(c_185, plain, (![A_31, B_32, C_33]: (k3_xboole_0(k3_xboole_0(A_31, B_32), C_33)=k3_xboole_0(A_31, k3_xboole_0(B_32, C_33)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.03/1.29  tff(c_293, plain, (![B_37, A_38, C_39]: (k3_xboole_0(k3_xboole_0(B_37, A_38), C_39)=k3_xboole_0(A_38, k3_xboole_0(B_37, C_39)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_185])).
% 2.03/1.29  tff(c_20, plain, (r1_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.03/1.29  tff(c_25, plain, (r1_xboole_0('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_20])).
% 2.03/1.29  tff(c_68, plain, (![B_18, A_19]: (r1_xboole_0(B_18, A_19) | ~r1_xboole_0(A_19, B_18))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.03/1.29  tff(c_71, plain, (r1_xboole_0(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_25, c_68])).
% 2.03/1.29  tff(c_85, plain, (![A_24, B_25]: (k3_xboole_0(A_24, B_25)=k1_xboole_0 | ~r1_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.03/1.29  tff(c_96, plain, (k3_xboole_0(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_71, c_85])).
% 2.03/1.29  tff(c_312, plain, (k3_xboole_0('#skF_2', k3_xboole_0('#skF_3', '#skF_1'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_293, c_96])).
% 2.03/1.29  tff(c_367, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2, c_156, c_2, c_312])).
% 2.03/1.29  tff(c_369, plain, $false, inference(negUnitSimplification, [status(thm)], [c_83, c_367])).
% 2.03/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.03/1.29  
% 2.03/1.29  Inference rules
% 2.03/1.29  ----------------------
% 2.03/1.29  #Ref     : 0
% 2.03/1.29  #Sup     : 95
% 2.03/1.29  #Fact    : 0
% 2.03/1.29  #Define  : 0
% 2.03/1.29  #Split   : 0
% 2.03/1.29  #Chain   : 0
% 2.03/1.29  #Close   : 0
% 2.03/1.29  
% 2.03/1.29  Ordering : KBO
% 2.03/1.29  
% 2.03/1.29  Simplification rules
% 2.03/1.29  ----------------------
% 2.03/1.29  #Subsume      : 4
% 2.03/1.29  #Demod        : 31
% 2.03/1.29  #Tautology    : 41
% 2.03/1.29  #SimpNegUnit  : 1
% 2.03/1.29  #BackRed      : 0
% 2.03/1.29  
% 2.03/1.29  #Partial instantiations: 0
% 2.03/1.29  #Strategies tried      : 1
% 2.03/1.29  
% 2.03/1.29  Timing (in seconds)
% 2.03/1.29  ----------------------
% 2.03/1.29  Preprocessing        : 0.28
% 2.03/1.29  Parsing              : 0.16
% 2.03/1.29  CNF conversion       : 0.02
% 2.03/1.29  Main loop            : 0.25
% 2.03/1.29  Inferencing          : 0.08
% 2.03/1.29  Reduction            : 0.10
% 2.03/1.29  Demodulation         : 0.08
% 2.03/1.29  BG Simplification    : 0.01
% 2.03/1.29  Subsumption          : 0.04
% 2.03/1.29  Abstraction          : 0.01
% 2.03/1.29  MUC search           : 0.00
% 2.03/1.29  Cooper               : 0.00
% 2.03/1.29  Total                : 0.56
% 2.03/1.29  Index Insertion      : 0.00
% 2.03/1.29  Index Deletion       : 0.00
% 2.03/1.29  Index Matching       : 0.00
% 2.03/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
