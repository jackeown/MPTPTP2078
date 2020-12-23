%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:28 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :   32 (  39 expanded)
%              Number of leaves         :   16 (  20 expanded)
%              Depth                    :    7
%              Number of atoms          :   25 (  36 expanded)
%              Number of equality atoms :   11 (  15 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_48,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,B)
       => r1_tarski(k4_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(c_18,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_68,plain,(
    ! [A_24,B_25] :
      ( k3_xboole_0(A_24,B_25) = A_24
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_80,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_18,c_68])).

tff(c_384,plain,(
    ! [A_44,B_45,C_46] : k4_xboole_0(k3_xboole_0(A_44,B_45),C_46) = k3_xboole_0(A_44,k4_xboole_0(B_45,C_46)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_446,plain,(
    ! [C_49] : k3_xboole_0('#skF_1',k4_xboole_0('#skF_2',C_49)) = k4_xboole_0('#skF_1',C_49) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_384])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_166,plain,(
    ! [A_31,B_32,C_33] : k3_xboole_0(k3_xboole_0(A_31,B_32),C_33) = k3_xboole_0(A_31,k3_xboole_0(B_32,C_33)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_20,plain,(
    ! [B_20,A_21] : k3_xboole_0(B_20,A_21) = k3_xboole_0(A_21,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_8,B_9] : r1_tarski(k3_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_35,plain,(
    ! [B_20,A_21] : r1_tarski(k3_xboole_0(B_20,A_21),A_21) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_8])).

tff(c_264,plain,(
    ! [A_37,B_38,C_39] : r1_tarski(k3_xboole_0(A_37,k3_xboole_0(B_38,C_39)),C_39) ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_35])).

tff(c_306,plain,(
    ! [A_40] : r1_tarski(k3_xboole_0(A_40,'#skF_1'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_264])).

tff(c_319,plain,(
    ! [A_1] : r1_tarski(k3_xboole_0('#skF_1',A_1),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_306])).

tff(c_456,plain,(
    ! [C_49] : r1_tarski(k4_xboole_0('#skF_1',C_49),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_446,c_319])).

tff(c_16,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_493,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_456,c_16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:30:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.23/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.29  
% 2.23/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.29  %$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 2.23/1.29  
% 2.23/1.29  %Foreground sorts:
% 2.23/1.29  
% 2.23/1.29  
% 2.23/1.29  %Background operators:
% 2.23/1.29  
% 2.23/1.29  
% 2.23/1.29  %Foreground operators:
% 2.23/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.23/1.29  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.23/1.29  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.23/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.23/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.23/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.23/1.29  tff('#skF_1', type, '#skF_1': $i).
% 2.23/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.23/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.23/1.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.23/1.29  
% 2.23/1.31  tff(f_48, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t109_xboole_1)).
% 2.23/1.31  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.23/1.31  tff(f_43, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 2.23/1.31  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.23/1.31  tff(f_31, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 2.23/1.31  tff(f_33, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.23/1.31  tff(c_18, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.23/1.31  tff(c_68, plain, (![A_24, B_25]: (k3_xboole_0(A_24, B_25)=A_24 | ~r1_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.23/1.31  tff(c_80, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_18, c_68])).
% 2.23/1.31  tff(c_384, plain, (![A_44, B_45, C_46]: (k4_xboole_0(k3_xboole_0(A_44, B_45), C_46)=k3_xboole_0(A_44, k4_xboole_0(B_45, C_46)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.23/1.31  tff(c_446, plain, (![C_49]: (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', C_49))=k4_xboole_0('#skF_1', C_49))), inference(superposition, [status(thm), theory('equality')], [c_80, c_384])).
% 2.23/1.31  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.23/1.31  tff(c_166, plain, (![A_31, B_32, C_33]: (k3_xboole_0(k3_xboole_0(A_31, B_32), C_33)=k3_xboole_0(A_31, k3_xboole_0(B_32, C_33)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.23/1.31  tff(c_20, plain, (![B_20, A_21]: (k3_xboole_0(B_20, A_21)=k3_xboole_0(A_21, B_20))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.23/1.31  tff(c_8, plain, (![A_8, B_9]: (r1_tarski(k3_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.23/1.31  tff(c_35, plain, (![B_20, A_21]: (r1_tarski(k3_xboole_0(B_20, A_21), A_21))), inference(superposition, [status(thm), theory('equality')], [c_20, c_8])).
% 2.23/1.31  tff(c_264, plain, (![A_37, B_38, C_39]: (r1_tarski(k3_xboole_0(A_37, k3_xboole_0(B_38, C_39)), C_39))), inference(superposition, [status(thm), theory('equality')], [c_166, c_35])).
% 2.23/1.31  tff(c_306, plain, (![A_40]: (r1_tarski(k3_xboole_0(A_40, '#skF_1'), '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_80, c_264])).
% 2.23/1.31  tff(c_319, plain, (![A_1]: (r1_tarski(k3_xboole_0('#skF_1', A_1), '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2, c_306])).
% 2.23/1.31  tff(c_456, plain, (![C_49]: (r1_tarski(k4_xboole_0('#skF_1', C_49), '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_446, c_319])).
% 2.23/1.31  tff(c_16, plain, (~r1_tarski(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.23/1.31  tff(c_493, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_456, c_16])).
% 2.23/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.31  
% 2.23/1.31  Inference rules
% 2.23/1.31  ----------------------
% 2.23/1.31  #Ref     : 0
% 2.23/1.31  #Sup     : 125
% 2.23/1.31  #Fact    : 0
% 2.23/1.31  #Define  : 0
% 2.23/1.31  #Split   : 0
% 2.23/1.31  #Chain   : 0
% 2.23/1.31  #Close   : 0
% 2.23/1.31  
% 2.23/1.31  Ordering : KBO
% 2.23/1.31  
% 2.23/1.31  Simplification rules
% 2.23/1.31  ----------------------
% 2.23/1.31  #Subsume      : 0
% 2.23/1.31  #Demod        : 56
% 2.23/1.31  #Tautology    : 66
% 2.23/1.31  #SimpNegUnit  : 0
% 2.23/1.31  #BackRed      : 2
% 2.23/1.31  
% 2.23/1.31  #Partial instantiations: 0
% 2.23/1.31  #Strategies tried      : 1
% 2.23/1.31  
% 2.23/1.31  Timing (in seconds)
% 2.23/1.31  ----------------------
% 2.23/1.31  Preprocessing        : 0.28
% 2.23/1.31  Parsing              : 0.14
% 2.23/1.31  CNF conversion       : 0.02
% 2.23/1.31  Main loop            : 0.26
% 2.23/1.31  Inferencing          : 0.09
% 2.23/1.31  Reduction            : 0.10
% 2.23/1.31  Demodulation         : 0.09
% 2.23/1.31  BG Simplification    : 0.01
% 2.23/1.31  Subsumption          : 0.04
% 2.23/1.31  Abstraction          : 0.01
% 2.23/1.31  MUC search           : 0.00
% 2.23/1.31  Cooper               : 0.00
% 2.23/1.31  Total                : 0.57
% 2.23/1.31  Index Insertion      : 0.00
% 2.23/1.31  Index Deletion       : 0.00
% 2.23/1.31  Index Matching       : 0.00
% 2.23/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
