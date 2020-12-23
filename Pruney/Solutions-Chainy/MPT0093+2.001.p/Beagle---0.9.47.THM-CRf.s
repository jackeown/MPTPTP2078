%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:31 EST 2020

% Result     : Theorem 1.82s
% Output     : CNFRefutation 1.82s
% Verified   : 
% Statistics : Number of formulae       :   28 (  30 expanded)
%              Number of leaves         :   15 (  17 expanded)
%              Depth                    :    7
%              Number of atoms          :   31 (  37 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_46,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_xboole_0(A,C) )
       => r1_tarski(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,k2_xboole_0(B,C))
        & r1_xboole_0(A,C) )
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).

tff(c_14,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,k2_xboole_0(C_5,B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_6,plain,(
    ! [A_6,B_7] : k2_xboole_0(A_6,k4_xboole_0(B_7,A_6)) = k2_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_78,plain,(
    ! [A_24,B_25,C_26] :
      ( r1_tarski(A_24,B_25)
      | ~ r1_xboole_0(A_24,C_26)
      | ~ r1_tarski(A_24,k2_xboole_0(B_25,C_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_101,plain,(
    ! [A_30,B_31,A_32] :
      ( r1_tarski(A_30,B_31)
      | ~ r1_xboole_0(A_30,A_32)
      | ~ r1_tarski(A_30,k2_xboole_0(A_32,B_31)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_78])).

tff(c_120,plain,(
    ! [A_36,B_37,A_38] :
      ( r1_tarski(A_36,k4_xboole_0(B_37,A_38))
      | ~ r1_xboole_0(A_36,A_38)
      | ~ r1_tarski(A_36,k2_xboole_0(A_38,B_37)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_101])).

tff(c_10,plain,(
    ~ r1_tarski('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_126,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_tarski('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_120,c_10])).

tff(c_130,plain,(
    ~ r1_tarski('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_126])).

tff(c_136,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_130])).

tff(c_141,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_136])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:53:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.82/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.82/1.26  
% 1.82/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.82/1.27  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.82/1.27  
% 1.82/1.27  %Foreground sorts:
% 1.82/1.27  
% 1.82/1.27  
% 1.82/1.27  %Background operators:
% 1.82/1.27  
% 1.82/1.27  
% 1.82/1.27  %Foreground operators:
% 1.82/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.82/1.27  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.82/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.82/1.27  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.82/1.27  tff('#skF_2', type, '#skF_2': $i).
% 1.82/1.27  tff('#skF_3', type, '#skF_3': $i).
% 1.82/1.27  tff('#skF_1', type, '#skF_1': $i).
% 1.82/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.82/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.82/1.27  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.82/1.27  
% 1.82/1.27  tff(f_46, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(A, C)) => r1_tarski(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_xboole_1)).
% 1.82/1.27  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 1.82/1.27  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 1.82/1.27  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.82/1.27  tff(f_39, axiom, (![A, B, C]: ((r1_tarski(A, k2_xboole_0(B, C)) & r1_xboole_0(A, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_xboole_1)).
% 1.82/1.27  tff(c_14, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.82/1.27  tff(c_4, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, k2_xboole_0(C_5, B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.82/1.27  tff(c_12, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.82/1.27  tff(c_6, plain, (![A_6, B_7]: (k2_xboole_0(A_6, k4_xboole_0(B_7, A_6))=k2_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.82/1.27  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.82/1.27  tff(c_78, plain, (![A_24, B_25, C_26]: (r1_tarski(A_24, B_25) | ~r1_xboole_0(A_24, C_26) | ~r1_tarski(A_24, k2_xboole_0(B_25, C_26)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.82/1.27  tff(c_101, plain, (![A_30, B_31, A_32]: (r1_tarski(A_30, B_31) | ~r1_xboole_0(A_30, A_32) | ~r1_tarski(A_30, k2_xboole_0(A_32, B_31)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_78])).
% 1.82/1.27  tff(c_120, plain, (![A_36, B_37, A_38]: (r1_tarski(A_36, k4_xboole_0(B_37, A_38)) | ~r1_xboole_0(A_36, A_38) | ~r1_tarski(A_36, k2_xboole_0(A_38, B_37)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_101])).
% 1.82/1.27  tff(c_10, plain, (~r1_tarski('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.82/1.27  tff(c_126, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_tarski('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_120, c_10])).
% 1.82/1.27  tff(c_130, plain, (~r1_tarski('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_126])).
% 1.82/1.27  tff(c_136, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_4, c_130])).
% 1.82/1.27  tff(c_141, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_136])).
% 1.82/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.82/1.27  
% 1.82/1.27  Inference rules
% 1.82/1.27  ----------------------
% 1.82/1.27  #Ref     : 0
% 1.82/1.27  #Sup     : 31
% 1.82/1.27  #Fact    : 0
% 1.82/1.27  #Define  : 0
% 1.82/1.27  #Split   : 1
% 1.82/1.27  #Chain   : 0
% 1.82/1.27  #Close   : 0
% 1.82/1.27  
% 1.82/1.27  Ordering : KBO
% 1.82/1.27  
% 1.82/1.27  Simplification rules
% 1.82/1.27  ----------------------
% 1.82/1.27  #Subsume      : 9
% 1.82/1.27  #Demod        : 2
% 1.82/1.27  #Tautology    : 13
% 1.82/1.27  #SimpNegUnit  : 0
% 1.82/1.27  #BackRed      : 0
% 1.82/1.27  
% 1.82/1.27  #Partial instantiations: 0
% 1.82/1.27  #Strategies tried      : 1
% 1.82/1.27  
% 1.82/1.27  Timing (in seconds)
% 1.82/1.27  ----------------------
% 1.82/1.28  Preprocessing        : 0.25
% 1.82/1.28  Parsing              : 0.14
% 1.82/1.28  CNF conversion       : 0.01
% 1.82/1.28  Main loop            : 0.15
% 1.82/1.28  Inferencing          : 0.06
% 1.82/1.28  Reduction            : 0.04
% 1.82/1.28  Demodulation         : 0.03
% 1.82/1.28  BG Simplification    : 0.01
% 1.82/1.28  Subsumption          : 0.03
% 1.82/1.28  Abstraction          : 0.01
% 1.82/1.28  MUC search           : 0.00
% 1.82/1.28  Cooper               : 0.00
% 1.82/1.28  Total                : 0.42
% 1.82/1.28  Index Insertion      : 0.00
% 1.82/1.28  Index Deletion       : 0.00
% 1.82/1.28  Index Matching       : 0.00
% 1.82/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
