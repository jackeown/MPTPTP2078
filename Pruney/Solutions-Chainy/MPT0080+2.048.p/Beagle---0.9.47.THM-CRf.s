%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:55 EST 2020

% Result     : Theorem 2.02s
% Output     : CNFRefutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :   39 (  41 expanded)
%              Number of leaves         :   22 (  24 expanded)
%              Depth                    :    9
%              Number of atoms          :   37 (  43 expanded)
%              Number of equality atoms :   12 (  12 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_66,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,C) )
       => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_51,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_49,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

tff(c_18,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_22,plain,(
    r1_tarski('#skF_3',k2_xboole_0('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_10] : k4_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_20,plain,(
    r1_xboole_0('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_8,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_75,plain,(
    ! [A_24,B_25,C_26] :
      ( ~ r1_xboole_0(A_24,B_25)
      | ~ r2_hidden(C_26,k3_xboole_0(A_24,B_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_81,plain,(
    ! [A_27,B_28] :
      ( ~ r1_xboole_0(A_27,B_28)
      | k3_xboole_0(A_27,B_28) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_75])).

tff(c_85,plain,(
    k3_xboole_0('#skF_3','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_81])).

tff(c_14,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k3_xboole_0(A_14,B_15)) = k4_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_92,plain,(
    k4_xboole_0('#skF_3',k1_xboole_0) = k4_xboole_0('#skF_3','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_14])).

tff(c_97,plain,(
    k4_xboole_0('#skF_3','#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_92])).

tff(c_157,plain,(
    ! [A_32,B_33,C_34] :
      ( r1_tarski(k4_xboole_0(A_32,B_33),C_34)
      | ~ r1_tarski(A_32,k2_xboole_0(B_33,C_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_214,plain,(
    ! [C_36] :
      ( r1_tarski('#skF_3',C_36)
      | ~ r1_tarski('#skF_3',k2_xboole_0('#skF_5',C_36)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_157])).

tff(c_282,plain,(
    ! [A_41] :
      ( r1_tarski('#skF_3',A_41)
      | ~ r1_tarski('#skF_3',k2_xboole_0(A_41,'#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_214])).

tff(c_293,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_282])).

tff(c_297,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_293])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:31:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.02/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.25  
% 2.02/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.25  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 2.02/1.25  
% 2.02/1.25  %Foreground sorts:
% 2.02/1.25  
% 2.02/1.25  
% 2.02/1.25  %Background operators:
% 2.02/1.25  
% 2.02/1.25  
% 2.02/1.25  %Foreground operators:
% 2.02/1.25  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.02/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.02/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.02/1.25  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.02/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.02/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.02/1.25  tff('#skF_5', type, '#skF_5': $i).
% 2.02/1.25  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.02/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.02/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.02/1.25  tff('#skF_4', type, '#skF_4': $i).
% 2.02/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.02/1.25  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.02/1.25  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.02/1.25  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.02/1.25  
% 2.02/1.26  tff(f_66, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, k2_xboole_0(B, C)) & r1_xboole_0(A, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_xboole_1)).
% 2.02/1.26  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.02/1.26  tff(f_51, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.02/1.26  tff(f_49, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.02/1.26  tff(f_41, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.02/1.26  tff(f_57, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 2.02/1.26  tff(f_55, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 2.02/1.26  tff(c_18, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.02/1.26  tff(c_22, plain, (r1_tarski('#skF_3', k2_xboole_0('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.02/1.26  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.02/1.26  tff(c_10, plain, (![A_10]: (k4_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.02/1.26  tff(c_20, plain, (r1_xboole_0('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.02/1.26  tff(c_8, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.02/1.26  tff(c_75, plain, (![A_24, B_25, C_26]: (~r1_xboole_0(A_24, B_25) | ~r2_hidden(C_26, k3_xboole_0(A_24, B_25)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.02/1.26  tff(c_81, plain, (![A_27, B_28]: (~r1_xboole_0(A_27, B_28) | k3_xboole_0(A_27, B_28)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_75])).
% 2.02/1.26  tff(c_85, plain, (k3_xboole_0('#skF_3', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_20, c_81])).
% 2.02/1.26  tff(c_14, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k3_xboole_0(A_14, B_15))=k4_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.02/1.26  tff(c_92, plain, (k4_xboole_0('#skF_3', k1_xboole_0)=k4_xboole_0('#skF_3', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_85, c_14])).
% 2.02/1.26  tff(c_97, plain, (k4_xboole_0('#skF_3', '#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_10, c_92])).
% 2.02/1.26  tff(c_157, plain, (![A_32, B_33, C_34]: (r1_tarski(k4_xboole_0(A_32, B_33), C_34) | ~r1_tarski(A_32, k2_xboole_0(B_33, C_34)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.02/1.26  tff(c_214, plain, (![C_36]: (r1_tarski('#skF_3', C_36) | ~r1_tarski('#skF_3', k2_xboole_0('#skF_5', C_36)))), inference(superposition, [status(thm), theory('equality')], [c_97, c_157])).
% 2.02/1.26  tff(c_282, plain, (![A_41]: (r1_tarski('#skF_3', A_41) | ~r1_tarski('#skF_3', k2_xboole_0(A_41, '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_2, c_214])).
% 2.02/1.26  tff(c_293, plain, (r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_22, c_282])).
% 2.02/1.26  tff(c_297, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_293])).
% 2.02/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.26  
% 2.02/1.26  Inference rules
% 2.02/1.26  ----------------------
% 2.02/1.26  #Ref     : 0
% 2.02/1.26  #Sup     : 71
% 2.02/1.26  #Fact    : 0
% 2.02/1.26  #Define  : 0
% 2.02/1.26  #Split   : 1
% 2.02/1.26  #Chain   : 0
% 2.02/1.26  #Close   : 0
% 2.02/1.26  
% 2.02/1.26  Ordering : KBO
% 2.02/1.26  
% 2.02/1.26  Simplification rules
% 2.02/1.26  ----------------------
% 2.02/1.26  #Subsume      : 4
% 2.02/1.26  #Demod        : 18
% 2.02/1.26  #Tautology    : 38
% 2.02/1.26  #SimpNegUnit  : 5
% 2.02/1.26  #BackRed      : 0
% 2.02/1.26  
% 2.02/1.26  #Partial instantiations: 0
% 2.02/1.26  #Strategies tried      : 1
% 2.02/1.26  
% 2.02/1.26  Timing (in seconds)
% 2.02/1.26  ----------------------
% 2.02/1.26  Preprocessing        : 0.26
% 2.02/1.26  Parsing              : 0.14
% 2.02/1.26  CNF conversion       : 0.02
% 2.02/1.26  Main loop            : 0.19
% 2.02/1.26  Inferencing          : 0.07
% 2.02/1.26  Reduction            : 0.07
% 2.02/1.26  Demodulation         : 0.05
% 2.02/1.26  BG Simplification    : 0.01
% 2.02/1.26  Subsumption          : 0.03
% 2.02/1.26  Abstraction          : 0.01
% 2.02/1.26  MUC search           : 0.00
% 2.02/1.26  Cooper               : 0.00
% 2.02/1.26  Total                : 0.47
% 2.02/1.26  Index Insertion      : 0.00
% 2.02/1.26  Index Deletion       : 0.00
% 2.02/1.26  Index Matching       : 0.00
% 2.02/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
