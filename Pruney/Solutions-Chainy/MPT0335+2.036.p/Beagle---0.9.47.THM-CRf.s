%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:58 EST 2020

% Result     : Theorem 1.99s
% Output     : CNFRefutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :   37 (  41 expanded)
%              Number of leaves         :   20 (  24 expanded)
%              Depth                    :    7
%              Number of atoms          :   33 (  47 expanded)
%              Number of equality atoms :   18 (  25 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(A,B)
          & k3_xboole_0(B,C) = k1_tarski(D)
          & r2_hidden(D,A) )
       => k3_xboole_0(A,C) = k1_tarski(D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_20,plain,(
    k3_xboole_0('#skF_1','#skF_3') != k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_22,plain,(
    r2_hidden('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_24,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_26,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_101,plain,(
    ! [A_25,B_26] :
      ( k3_xboole_0(A_25,B_26) = A_25
      | ~ r1_tarski(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_105,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_26,c_101])).

tff(c_183,plain,(
    ! [A_38,B_39,C_40] : k3_xboole_0(k3_xboole_0(A_38,B_39),C_40) = k3_xboole_0(A_38,k3_xboole_0(B_39,C_40)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_243,plain,(
    ! [C_41] : k3_xboole_0('#skF_1',k3_xboole_0('#skF_2',C_41)) = k3_xboole_0('#skF_1',C_41) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_183])).

tff(c_267,plain,(
    k3_xboole_0('#skF_1',k1_tarski('#skF_4')) = k3_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_243])).

tff(c_110,plain,(
    ! [A_27,B_28] :
      ( r1_tarski(k1_tarski(A_27),B_28)
      | ~ r2_hidden(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( k3_xboole_0(A_6,B_7) = A_6
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_129,plain,(
    ! [A_34,B_35] :
      ( k3_xboole_0(k1_tarski(A_34),B_35) = k1_tarski(A_34)
      | ~ r2_hidden(A_34,B_35) ) ),
    inference(resolution,[status(thm)],[c_110,c_6])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_135,plain,(
    ! [B_35,A_34] :
      ( k3_xboole_0(B_35,k1_tarski(A_34)) = k1_tarski(A_34)
      | ~ r2_hidden(A_34,B_35) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_2])).

tff(c_278,plain,
    ( k3_xboole_0('#skF_1','#skF_3') = k1_tarski('#skF_4')
    | ~ r2_hidden('#skF_4','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_267,c_135])).

tff(c_286,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_278])).

tff(c_288,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_286])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:35:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.99/1.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.20  
% 1.99/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.21  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.99/1.21  
% 1.99/1.21  %Foreground sorts:
% 1.99/1.21  
% 1.99/1.21  
% 1.99/1.21  %Background operators:
% 1.99/1.21  
% 1.99/1.21  
% 1.99/1.21  %Foreground operators:
% 1.99/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.99/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.99/1.21  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.99/1.21  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.99/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.99/1.21  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.99/1.21  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.99/1.21  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.99/1.21  tff('#skF_2', type, '#skF_2': $i).
% 1.99/1.21  tff('#skF_3', type, '#skF_3': $i).
% 1.99/1.21  tff('#skF_1', type, '#skF_1': $i).
% 1.99/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.99/1.21  tff('#skF_4', type, '#skF_4': $i).
% 1.99/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.99/1.21  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.99/1.21  
% 1.99/1.22  tff(f_54, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(A, B) & (k3_xboole_0(B, C) = k1_tarski(D))) & r2_hidden(D, A)) => (k3_xboole_0(A, C) = k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_zfmisc_1)).
% 1.99/1.22  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.99/1.22  tff(f_29, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 1.99/1.22  tff(f_45, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 1.99/1.22  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.99/1.22  tff(c_20, plain, (k3_xboole_0('#skF_1', '#skF_3')!=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.99/1.22  tff(c_22, plain, (r2_hidden('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.99/1.22  tff(c_24, plain, (k3_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.99/1.22  tff(c_26, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.99/1.22  tff(c_101, plain, (![A_25, B_26]: (k3_xboole_0(A_25, B_26)=A_25 | ~r1_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.99/1.22  tff(c_105, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_26, c_101])).
% 1.99/1.22  tff(c_183, plain, (![A_38, B_39, C_40]: (k3_xboole_0(k3_xboole_0(A_38, B_39), C_40)=k3_xboole_0(A_38, k3_xboole_0(B_39, C_40)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.99/1.22  tff(c_243, plain, (![C_41]: (k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', C_41))=k3_xboole_0('#skF_1', C_41))), inference(superposition, [status(thm), theory('equality')], [c_105, c_183])).
% 1.99/1.22  tff(c_267, plain, (k3_xboole_0('#skF_1', k1_tarski('#skF_4'))=k3_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_24, c_243])).
% 1.99/1.22  tff(c_110, plain, (![A_27, B_28]: (r1_tarski(k1_tarski(A_27), B_28) | ~r2_hidden(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.99/1.22  tff(c_6, plain, (![A_6, B_7]: (k3_xboole_0(A_6, B_7)=A_6 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.99/1.22  tff(c_129, plain, (![A_34, B_35]: (k3_xboole_0(k1_tarski(A_34), B_35)=k1_tarski(A_34) | ~r2_hidden(A_34, B_35))), inference(resolution, [status(thm)], [c_110, c_6])).
% 1.99/1.22  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.99/1.22  tff(c_135, plain, (![B_35, A_34]: (k3_xboole_0(B_35, k1_tarski(A_34))=k1_tarski(A_34) | ~r2_hidden(A_34, B_35))), inference(superposition, [status(thm), theory('equality')], [c_129, c_2])).
% 1.99/1.22  tff(c_278, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_tarski('#skF_4') | ~r2_hidden('#skF_4', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_267, c_135])).
% 1.99/1.22  tff(c_286, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_278])).
% 1.99/1.22  tff(c_288, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_286])).
% 1.99/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.22  
% 1.99/1.22  Inference rules
% 1.99/1.22  ----------------------
% 1.99/1.22  #Ref     : 0
% 1.99/1.22  #Sup     : 70
% 1.99/1.22  #Fact    : 0
% 1.99/1.22  #Define  : 0
% 1.99/1.22  #Split   : 0
% 1.99/1.22  #Chain   : 0
% 1.99/1.22  #Close   : 0
% 1.99/1.22  
% 1.99/1.22  Ordering : KBO
% 1.99/1.22  
% 1.99/1.22  Simplification rules
% 1.99/1.22  ----------------------
% 1.99/1.22  #Subsume      : 5
% 1.99/1.22  #Demod        : 14
% 1.99/1.22  #Tautology    : 37
% 1.99/1.22  #SimpNegUnit  : 1
% 1.99/1.22  #BackRed      : 0
% 1.99/1.22  
% 1.99/1.22  #Partial instantiations: 0
% 1.99/1.22  #Strategies tried      : 1
% 1.99/1.22  
% 1.99/1.22  Timing (in seconds)
% 1.99/1.22  ----------------------
% 1.99/1.22  Preprocessing        : 0.28
% 1.99/1.22  Parsing              : 0.15
% 1.99/1.22  CNF conversion       : 0.02
% 1.99/1.22  Main loop            : 0.18
% 1.99/1.22  Inferencing          : 0.07
% 1.99/1.22  Reduction            : 0.07
% 1.99/1.22  Demodulation         : 0.05
% 1.99/1.22  BG Simplification    : 0.01
% 1.99/1.22  Subsumption          : 0.03
% 1.99/1.22  Abstraction          : 0.01
% 1.99/1.22  MUC search           : 0.00
% 1.99/1.22  Cooper               : 0.00
% 1.99/1.22  Total                : 0.48
% 1.99/1.22  Index Insertion      : 0.00
% 1.99/1.22  Index Deletion       : 0.00
% 1.99/1.22  Index Matching       : 0.00
% 1.99/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
