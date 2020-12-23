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
% DateTime   : Thu Dec  3 09:42:41 EST 2020

% Result     : Theorem 9.02s
% Output     : CNFRefutation 9.02s
% Verified   : 
% Statistics : Number of formulae       :   30 (  43 expanded)
%              Number of leaves         :   15 (  21 expanded)
%              Depth                    :    6
%              Number of atoms          :   26 (  39 expanded)
%              Number of equality atoms :    9 (  20 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_39,axiom,(
    ! [A,B,C] : k2_xboole_0(A,k3_xboole_0(B,C)) = k3_xboole_0(k2_xboole_0(A,B),k2_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_42,negated_conjecture,(
    ~ ! [A,B,C] : r1_tarski(k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)),k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_xboole_1)).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_224,plain,(
    ! [A_39,B_40,C_41] : k3_xboole_0(k2_xboole_0(A_39,B_40),k2_xboole_0(A_39,C_41)) = k2_xboole_0(A_39,k3_xboole_0(B_40,C_41)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1177,plain,(
    ! [A_107,B_108,B_109] : k3_xboole_0(k2_xboole_0(A_107,B_108),k2_xboole_0(B_109,A_107)) = k2_xboole_0(A_107,k3_xboole_0(B_108,B_109)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_224])).

tff(c_1303,plain,(
    ! [B_109,A_107,B_108] : k3_xboole_0(k2_xboole_0(B_109,A_107),k2_xboole_0(A_107,B_108)) = k2_xboole_0(A_107,k3_xboole_0(B_108,B_109)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1177])).

tff(c_3792,plain,(
    ! [B_145,A_146,B_147] : k3_xboole_0(k2_xboole_0(B_145,A_146),k2_xboole_0(A_146,B_147)) = k2_xboole_0(A_146,k3_xboole_0(B_147,B_145)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1177])).

tff(c_6,plain,(
    ! [A_5,B_6] : r1_tarski(k3_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_97,plain,(
    ! [A_21,C_22,B_23] :
      ( r1_tarski(A_21,C_22)
      | ~ r1_tarski(B_23,C_22)
      | ~ r1_tarski(A_21,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_104,plain,(
    ! [A_24,A_25,B_26] :
      ( r1_tarski(A_24,A_25)
      | ~ r1_tarski(A_24,k3_xboole_0(A_25,B_26)) ) ),
    inference(resolution,[status(thm)],[c_6,c_97])).

tff(c_120,plain,(
    ! [A_25,B_26,B_6] : r1_tarski(k3_xboole_0(k3_xboole_0(A_25,B_26),B_6),A_25) ),
    inference(resolution,[status(thm)],[c_6,c_104])).

tff(c_4811,plain,(
    ! [A_158,B_159,B_160,B_161] : r1_tarski(k3_xboole_0(k2_xboole_0(A_158,k3_xboole_0(B_159,B_160)),B_161),k2_xboole_0(B_160,A_158)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3792,c_120])).

tff(c_4834,plain,(
    ! [B_159,B_160,B_108,B_109] : r1_tarski(k2_xboole_0(k3_xboole_0(B_159,B_160),k3_xboole_0(B_108,B_109)),k2_xboole_0(B_160,B_109)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1303,c_4811])).

tff(c_12,plain,(
    ~ r1_tarski(k2_xboole_0(k3_xboole_0('#skF_1','#skF_2'),k3_xboole_0('#skF_1','#skF_3')),k2_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_13,plain,(
    ~ r1_tarski(k2_xboole_0(k3_xboole_0('#skF_1','#skF_3'),k3_xboole_0('#skF_1','#skF_2')),k2_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_12])).

tff(c_11050,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4834,c_13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:38:50 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.02/3.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.02/3.21  
% 9.02/3.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.02/3.21  %$ r1_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 9.02/3.21  
% 9.02/3.21  %Foreground sorts:
% 9.02/3.21  
% 9.02/3.21  
% 9.02/3.21  %Background operators:
% 9.02/3.21  
% 9.02/3.21  
% 9.02/3.21  %Foreground operators:
% 9.02/3.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.02/3.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.02/3.21  tff('#skF_2', type, '#skF_2': $i).
% 9.02/3.21  tff('#skF_3', type, '#skF_3': $i).
% 9.02/3.21  tff('#skF_1', type, '#skF_1': $i).
% 9.02/3.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.02/3.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.02/3.21  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.02/3.21  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.02/3.21  
% 9.02/3.22  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 9.02/3.22  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 9.02/3.22  tff(f_39, axiom, (![A, B, C]: (k2_xboole_0(A, k3_xboole_0(B, C)) = k3_xboole_0(k2_xboole_0(A, B), k2_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_xboole_1)).
% 9.02/3.22  tff(f_31, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 9.02/3.22  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 9.02/3.22  tff(f_42, negated_conjecture, ~(![A, B, C]: r1_tarski(k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)), k2_xboole_0(B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_xboole_1)).
% 9.02/3.22  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 9.02/3.22  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.02/3.22  tff(c_224, plain, (![A_39, B_40, C_41]: (k3_xboole_0(k2_xboole_0(A_39, B_40), k2_xboole_0(A_39, C_41))=k2_xboole_0(A_39, k3_xboole_0(B_40, C_41)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.02/3.22  tff(c_1177, plain, (![A_107, B_108, B_109]: (k3_xboole_0(k2_xboole_0(A_107, B_108), k2_xboole_0(B_109, A_107))=k2_xboole_0(A_107, k3_xboole_0(B_108, B_109)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_224])).
% 9.02/3.22  tff(c_1303, plain, (![B_109, A_107, B_108]: (k3_xboole_0(k2_xboole_0(B_109, A_107), k2_xboole_0(A_107, B_108))=k2_xboole_0(A_107, k3_xboole_0(B_108, B_109)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_1177])).
% 9.02/3.22  tff(c_3792, plain, (![B_145, A_146, B_147]: (k3_xboole_0(k2_xboole_0(B_145, A_146), k2_xboole_0(A_146, B_147))=k2_xboole_0(A_146, k3_xboole_0(B_147, B_145)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_1177])).
% 9.02/3.22  tff(c_6, plain, (![A_5, B_6]: (r1_tarski(k3_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.02/3.22  tff(c_97, plain, (![A_21, C_22, B_23]: (r1_tarski(A_21, C_22) | ~r1_tarski(B_23, C_22) | ~r1_tarski(A_21, B_23))), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.02/3.22  tff(c_104, plain, (![A_24, A_25, B_26]: (r1_tarski(A_24, A_25) | ~r1_tarski(A_24, k3_xboole_0(A_25, B_26)))), inference(resolution, [status(thm)], [c_6, c_97])).
% 9.02/3.22  tff(c_120, plain, (![A_25, B_26, B_6]: (r1_tarski(k3_xboole_0(k3_xboole_0(A_25, B_26), B_6), A_25))), inference(resolution, [status(thm)], [c_6, c_104])).
% 9.02/3.22  tff(c_4811, plain, (![A_158, B_159, B_160, B_161]: (r1_tarski(k3_xboole_0(k2_xboole_0(A_158, k3_xboole_0(B_159, B_160)), B_161), k2_xboole_0(B_160, A_158)))), inference(superposition, [status(thm), theory('equality')], [c_3792, c_120])).
% 9.02/3.22  tff(c_4834, plain, (![B_159, B_160, B_108, B_109]: (r1_tarski(k2_xboole_0(k3_xboole_0(B_159, B_160), k3_xboole_0(B_108, B_109)), k2_xboole_0(B_160, B_109)))), inference(superposition, [status(thm), theory('equality')], [c_1303, c_4811])).
% 9.02/3.22  tff(c_12, plain, (~r1_tarski(k2_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), k3_xboole_0('#skF_1', '#skF_3')), k2_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_42])).
% 9.02/3.22  tff(c_13, plain, (~r1_tarski(k2_xboole_0(k3_xboole_0('#skF_1', '#skF_3'), k3_xboole_0('#skF_1', '#skF_2')), k2_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2, c_12])).
% 9.02/3.22  tff(c_11050, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4834, c_13])).
% 9.02/3.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.02/3.22  
% 9.02/3.22  Inference rules
% 9.02/3.22  ----------------------
% 9.02/3.22  #Ref     : 0
% 9.02/3.22  #Sup     : 2981
% 9.02/3.22  #Fact    : 0
% 9.02/3.22  #Define  : 0
% 9.02/3.22  #Split   : 0
% 9.02/3.22  #Chain   : 0
% 9.02/3.22  #Close   : 0
% 9.02/3.22  
% 9.02/3.22  Ordering : KBO
% 9.02/3.22  
% 9.02/3.22  Simplification rules
% 9.02/3.22  ----------------------
% 9.02/3.22  #Subsume      : 145
% 9.02/3.22  #Demod        : 578
% 9.02/3.22  #Tautology    : 625
% 9.02/3.22  #SimpNegUnit  : 0
% 9.02/3.22  #BackRed      : 1
% 9.02/3.22  
% 9.02/3.22  #Partial instantiations: 0
% 9.02/3.22  #Strategies tried      : 1
% 9.02/3.22  
% 9.02/3.22  Timing (in seconds)
% 9.02/3.22  ----------------------
% 9.02/3.22  Preprocessing        : 0.28
% 9.02/3.22  Parsing              : 0.15
% 9.02/3.22  CNF conversion       : 0.02
% 9.02/3.22  Main loop            : 2.11
% 9.02/3.22  Inferencing          : 0.44
% 9.02/3.22  Reduction            : 1.10
% 9.02/3.22  Demodulation         : 1.00
% 9.02/3.22  BG Simplification    : 0.07
% 9.02/3.22  Subsumption          : 0.39
% 9.02/3.22  Abstraction          : 0.06
% 9.02/3.22  MUC search           : 0.00
% 9.02/3.22  Cooper               : 0.00
% 9.02/3.22  Total                : 2.42
% 9.02/3.22  Index Insertion      : 0.00
% 9.02/3.22  Index Deletion       : 0.00
% 9.02/3.22  Index Matching       : 0.00
% 9.02/3.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
