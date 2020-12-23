%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:38 EST 2020

% Result     : Theorem 1.99s
% Output     : CNFRefutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :   36 (  55 expanded)
%              Number of leaves         :   16 (  25 expanded)
%              Depth                    :    6
%              Number of atoms          :   40 (  74 expanded)
%              Number of equality atoms :    5 (  12 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_50,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(A,B)
          & r1_tarski(C,D) )
       => r1_tarski(k3_xboole_0(A,C),k3_xboole_0(B,D)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_16,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_8,plain,(
    ! [A_8,B_9] : r1_tarski(k3_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_68,plain,(
    ! [A_19,B_20] :
      ( k2_xboole_0(A_19,B_20) = B_20
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_82,plain,(
    ! [A_8,B_9] : k2_xboole_0(k3_xboole_0(A_8,B_9),A_8) = A_8 ),
    inference(resolution,[status(thm)],[c_8,c_68])).

tff(c_137,plain,(
    ! [A_25,C_26,B_27] :
      ( r1_tarski(A_25,C_26)
      | ~ r1_tarski(k2_xboole_0(A_25,B_27),C_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_246,plain,(
    ! [A_40,B_41,C_42] :
      ( r1_tarski(k3_xboole_0(A_40,B_41),C_42)
      | ~ r1_tarski(A_40,C_42) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_137])).

tff(c_14,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_188,plain,(
    ! [A_34,B_35,C_36] :
      ( r1_tarski(k3_xboole_0(A_34,B_35),C_36)
      | ~ r1_tarski(A_34,C_36) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_137])).

tff(c_213,plain,(
    ! [B_37,A_38,C_39] :
      ( r1_tarski(k3_xboole_0(B_37,A_38),C_39)
      | ~ r1_tarski(A_38,C_39) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_188])).

tff(c_150,plain,(
    ! [A_28,B_29,C_30] :
      ( r1_tarski(A_28,k3_xboole_0(B_29,C_30))
      | ~ r1_tarski(A_28,C_30)
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_12,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_1','#skF_3'),k3_xboole_0('#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_17,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_1','#skF_3'),k3_xboole_0('#skF_4','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_12])).

tff(c_169,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_1','#skF_3'),'#skF_2')
    | ~ r1_tarski(k3_xboole_0('#skF_1','#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_150,c_17])).

tff(c_187,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_1','#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_169])).

tff(c_216,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_213,c_187])).

tff(c_232,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_216])).

tff(c_233,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_169])).

tff(c_249,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_246,c_233])).

tff(c_265,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_249])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:09:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.99/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.25  
% 1.99/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.25  %$ r1_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.99/1.25  
% 1.99/1.25  %Foreground sorts:
% 1.99/1.25  
% 1.99/1.25  
% 1.99/1.25  %Background operators:
% 1.99/1.25  
% 1.99/1.25  
% 1.99/1.25  %Foreground operators:
% 1.99/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.99/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.99/1.25  tff('#skF_2', type, '#skF_2': $i).
% 1.99/1.25  tff('#skF_3', type, '#skF_3': $i).
% 1.99/1.25  tff('#skF_1', type, '#skF_1': $i).
% 1.99/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.99/1.25  tff('#skF_4', type, '#skF_4': $i).
% 1.99/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.99/1.25  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.99/1.25  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.99/1.25  
% 1.99/1.26  tff(f_50, negated_conjecture, ~(![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k3_xboole_0(A, C), k3_xboole_0(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_xboole_1)).
% 1.99/1.26  tff(f_37, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 1.99/1.26  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.99/1.26  tff(f_31, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 1.99/1.26  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.99/1.26  tff(f_43, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 1.99/1.26  tff(c_16, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.99/1.26  tff(c_8, plain, (![A_8, B_9]: (r1_tarski(k3_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.99/1.26  tff(c_68, plain, (![A_19, B_20]: (k2_xboole_0(A_19, B_20)=B_20 | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.99/1.26  tff(c_82, plain, (![A_8, B_9]: (k2_xboole_0(k3_xboole_0(A_8, B_9), A_8)=A_8)), inference(resolution, [status(thm)], [c_8, c_68])).
% 1.99/1.26  tff(c_137, plain, (![A_25, C_26, B_27]: (r1_tarski(A_25, C_26) | ~r1_tarski(k2_xboole_0(A_25, B_27), C_26))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.99/1.26  tff(c_246, plain, (![A_40, B_41, C_42]: (r1_tarski(k3_xboole_0(A_40, B_41), C_42) | ~r1_tarski(A_40, C_42))), inference(superposition, [status(thm), theory('equality')], [c_82, c_137])).
% 1.99/1.26  tff(c_14, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.99/1.26  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.99/1.26  tff(c_188, plain, (![A_34, B_35, C_36]: (r1_tarski(k3_xboole_0(A_34, B_35), C_36) | ~r1_tarski(A_34, C_36))), inference(superposition, [status(thm), theory('equality')], [c_82, c_137])).
% 1.99/1.26  tff(c_213, plain, (![B_37, A_38, C_39]: (r1_tarski(k3_xboole_0(B_37, A_38), C_39) | ~r1_tarski(A_38, C_39))), inference(superposition, [status(thm), theory('equality')], [c_2, c_188])).
% 1.99/1.26  tff(c_150, plain, (![A_28, B_29, C_30]: (r1_tarski(A_28, k3_xboole_0(B_29, C_30)) | ~r1_tarski(A_28, C_30) | ~r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.99/1.26  tff(c_12, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_3'), k3_xboole_0('#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.99/1.26  tff(c_17, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_3'), k3_xboole_0('#skF_4', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_12])).
% 1.99/1.26  tff(c_169, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_3'), '#skF_2') | ~r1_tarski(k3_xboole_0('#skF_1', '#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_150, c_17])).
% 1.99/1.26  tff(c_187, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_3'), '#skF_4')), inference(splitLeft, [status(thm)], [c_169])).
% 1.99/1.26  tff(c_216, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_213, c_187])).
% 1.99/1.26  tff(c_232, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_216])).
% 1.99/1.26  tff(c_233, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_169])).
% 1.99/1.26  tff(c_249, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_246, c_233])).
% 1.99/1.26  tff(c_265, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_249])).
% 1.99/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.26  
% 1.99/1.26  Inference rules
% 1.99/1.26  ----------------------
% 1.99/1.26  #Ref     : 0
% 1.99/1.26  #Sup     : 62
% 1.99/1.26  #Fact    : 0
% 1.99/1.26  #Define  : 0
% 1.99/1.26  #Split   : 1
% 1.99/1.26  #Chain   : 0
% 1.99/1.26  #Close   : 0
% 1.99/1.26  
% 1.99/1.26  Ordering : KBO
% 1.99/1.26  
% 1.99/1.26  Simplification rules
% 1.99/1.26  ----------------------
% 1.99/1.26  #Subsume      : 3
% 1.99/1.26  #Demod        : 11
% 1.99/1.26  #Tautology    : 27
% 1.99/1.26  #SimpNegUnit  : 0
% 1.99/1.26  #BackRed      : 0
% 1.99/1.26  
% 1.99/1.26  #Partial instantiations: 0
% 1.99/1.26  #Strategies tried      : 1
% 1.99/1.26  
% 1.99/1.26  Timing (in seconds)
% 1.99/1.26  ----------------------
% 1.99/1.26  Preprocessing        : 0.28
% 1.99/1.26  Parsing              : 0.15
% 1.99/1.26  CNF conversion       : 0.02
% 1.99/1.26  Main loop            : 0.20
% 1.99/1.26  Inferencing          : 0.07
% 1.99/1.26  Reduction            : 0.07
% 1.99/1.26  Demodulation         : 0.06
% 1.99/1.26  BG Simplification    : 0.01
% 1.99/1.26  Subsumption          : 0.04
% 1.99/1.26  Abstraction          : 0.01
% 1.99/1.26  MUC search           : 0.00
% 1.99/1.26  Cooper               : 0.00
% 1.99/1.26  Total                : 0.51
% 1.99/1.26  Index Insertion      : 0.00
% 1.99/1.26  Index Deletion       : 0.00
% 1.99/1.26  Index Matching       : 0.00
% 1.99/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
