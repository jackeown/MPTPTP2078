%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:43 EST 2020

% Result     : Theorem 1.69s
% Output     : CNFRefutation 1.69s
% Verified   : 
% Statistics : Number of formulae       :   22 (  27 expanded)
%              Number of leaves         :   11 (  14 expanded)
%              Depth                    :    5
%              Number of atoms          :   19 (  28 expanded)
%              Number of equality atoms :   18 (  27 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(f_36,negated_conjecture,(
    ~ ! [A,B,C] :
        ( k1_tarski(A) = k2_tarski(B,C)
       => B = C ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( k1_tarski(A) = k2_tarski(B,C)
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(c_8,plain,(
    k2_tarski('#skF_2','#skF_3') = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_63,plain,(
    ! [B_8,A_9,C_10] :
      ( B_8 = A_9
      | k2_tarski(B_8,C_10) != k1_tarski(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_75,plain,(
    ! [A_9] :
      ( A_9 = '#skF_2'
      | k1_tarski(A_9) != k1_tarski('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_63])).

tff(c_80,plain,(
    '#skF_2' = '#skF_1' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_75])).

tff(c_6,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_85,plain,(
    '#skF_3' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_6])).

tff(c_13,plain,(
    ! [B_6,A_7] : k2_tarski(B_6,A_7) = k2_tarski(A_7,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_28,plain,(
    k2_tarski('#skF_3','#skF_2') = k1_tarski('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_13,c_8])).

tff(c_66,plain,(
    ! [A_9] :
      ( A_9 = '#skF_3'
      | k1_tarski(A_9) != k1_tarski('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_63])).

tff(c_122,plain,(
    '#skF_3' = '#skF_1' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_66])).

tff(c_124,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_122])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:45:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.69/1.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.69/1.13  
% 1.69/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.69/1.13  %$ k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 1.69/1.13  
% 1.69/1.13  %Foreground sorts:
% 1.69/1.13  
% 1.69/1.13  
% 1.69/1.13  %Background operators:
% 1.69/1.13  
% 1.69/1.13  
% 1.69/1.13  %Foreground operators:
% 1.69/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.69/1.13  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.69/1.13  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.69/1.13  tff('#skF_2', type, '#skF_2': $i).
% 1.69/1.13  tff('#skF_3', type, '#skF_3': $i).
% 1.69/1.13  tff('#skF_1', type, '#skF_1': $i).
% 1.69/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.69/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.69/1.13  
% 1.69/1.14  tff(f_36, negated_conjecture, ~(![A, B, C]: ((k1_tarski(A) = k2_tarski(B, C)) => (B = C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_zfmisc_1)).
% 1.69/1.14  tff(f_31, axiom, (![A, B, C]: ((k1_tarski(A) = k2_tarski(B, C)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_zfmisc_1)).
% 1.69/1.14  tff(f_27, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 1.69/1.14  tff(c_8, plain, (k2_tarski('#skF_2', '#skF_3')=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.69/1.14  tff(c_63, plain, (![B_8, A_9, C_10]: (B_8=A_9 | k2_tarski(B_8, C_10)!=k1_tarski(A_9))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.69/1.14  tff(c_75, plain, (![A_9]: (A_9='#skF_2' | k1_tarski(A_9)!=k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_8, c_63])).
% 1.69/1.14  tff(c_80, plain, ('#skF_2'='#skF_1'), inference(reflexivity, [status(thm), theory('equality')], [c_75])).
% 1.69/1.14  tff(c_6, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.69/1.14  tff(c_85, plain, ('#skF_3'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_6])).
% 1.69/1.14  tff(c_13, plain, (![B_6, A_7]: (k2_tarski(B_6, A_7)=k2_tarski(A_7, B_6))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.69/1.14  tff(c_28, plain, (k2_tarski('#skF_3', '#skF_2')=k1_tarski('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_13, c_8])).
% 1.69/1.14  tff(c_66, plain, (![A_9]: (A_9='#skF_3' | k1_tarski(A_9)!=k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_28, c_63])).
% 1.69/1.14  tff(c_122, plain, ('#skF_3'='#skF_1'), inference(reflexivity, [status(thm), theory('equality')], [c_66])).
% 1.69/1.14  tff(c_124, plain, $false, inference(negUnitSimplification, [status(thm)], [c_85, c_122])).
% 1.69/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.69/1.14  
% 1.69/1.14  Inference rules
% 1.69/1.14  ----------------------
% 1.69/1.14  #Ref     : 2
% 1.69/1.14  #Sup     : 32
% 1.69/1.14  #Fact    : 0
% 1.69/1.14  #Define  : 0
% 1.69/1.14  #Split   : 0
% 1.69/1.14  #Chain   : 0
% 1.69/1.14  #Close   : 0
% 1.69/1.14  
% 1.69/1.14  Ordering : KBO
% 1.69/1.14  
% 1.69/1.14  Simplification rules
% 1.69/1.14  ----------------------
% 1.69/1.14  #Subsume      : 0
% 1.69/1.14  #Demod        : 11
% 1.69/1.14  #Tautology    : 25
% 1.69/1.14  #SimpNegUnit  : 1
% 1.69/1.14  #BackRed      : 4
% 1.69/1.14  
% 1.69/1.14  #Partial instantiations: 0
% 1.69/1.14  #Strategies tried      : 1
% 1.69/1.14  
% 1.69/1.14  Timing (in seconds)
% 1.69/1.14  ----------------------
% 1.69/1.14  Preprocessing        : 0.26
% 1.69/1.14  Parsing              : 0.14
% 1.69/1.14  CNF conversion       : 0.02
% 1.69/1.14  Main loop            : 0.11
% 1.69/1.14  Inferencing          : 0.04
% 1.69/1.14  Reduction            : 0.04
% 1.69/1.14  Demodulation         : 0.03
% 1.69/1.14  BG Simplification    : 0.01
% 1.69/1.14  Subsumption          : 0.01
% 1.69/1.14  Abstraction          : 0.01
% 1.69/1.14  MUC search           : 0.00
% 1.69/1.14  Cooper               : 0.00
% 1.69/1.14  Total                : 0.40
% 1.69/1.14  Index Insertion      : 0.00
% 1.69/1.14  Index Deletion       : 0.00
% 1.69/1.14  Index Matching       : 0.00
% 1.69/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
