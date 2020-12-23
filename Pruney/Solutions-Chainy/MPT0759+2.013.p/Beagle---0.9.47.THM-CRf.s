%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:33 EST 2020

% Result     : Theorem 1.69s
% Output     : CNFRefutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :   37 (  38 expanded)
%              Number of leaves         :   22 (  23 expanded)
%              Depth                    :    6
%              Number of atoms          :   30 (  33 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_ordinal1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_45,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_49,axiom,(
    ! [A] : k1_ordinal1(A) = k2_xboole_0(A,k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

tff(f_34,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_57,negated_conjecture,(
    ~ ! [A] : k6_subset_1(k1_ordinal1(A),k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_ordinal1)).

tff(f_54,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_103,plain,(
    ! [A_35,B_36] :
      ( ~ r2_hidden('#skF_1'(A_35,B_36),B_36)
      | r1_tarski(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_108,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_103])).

tff(c_18,plain,(
    ! [A_14,B_15] :
      ( k4_xboole_0(A_14,k1_tarski(B_15)) = A_14
      | r2_hidden(B_15,A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_22,plain,(
    ! [A_18] : k2_xboole_0(A_18,k1_tarski(A_18)) = k1_ordinal1(A_18) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_65,plain,(
    ! [A_29,B_30] : k4_xboole_0(k2_xboole_0(A_29,B_30),B_30) = k4_xboole_0(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_74,plain,(
    ! [A_18] : k4_xboole_0(k1_ordinal1(A_18),k1_tarski(A_18)) = k4_xboole_0(A_18,k1_tarski(A_18)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_65])).

tff(c_20,plain,(
    ! [A_16,B_17] : k6_subset_1(A_16,B_17) = k4_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_26,plain,(
    k6_subset_1(k1_ordinal1('#skF_2'),k1_tarski('#skF_2')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_27,plain,(
    k4_xboole_0(k1_ordinal1('#skF_2'),k1_tarski('#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_26])).

tff(c_133,plain,(
    k4_xboole_0('#skF_2',k1_tarski('#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_27])).

tff(c_156,plain,(
    r2_hidden('#skF_2','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_133])).

tff(c_24,plain,(
    ! [B_20,A_19] :
      ( ~ r1_tarski(B_20,A_19)
      | ~ r2_hidden(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_161,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_156,c_24])).

tff(c_166,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_161])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:25:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.69/1.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.69/1.18  
% 1.69/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.18  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_ordinal1 > #skF_2 > #skF_1
% 1.87/1.18  
% 1.87/1.18  %Foreground sorts:
% 1.87/1.18  
% 1.87/1.18  
% 1.87/1.18  %Background operators:
% 1.87/1.18  
% 1.87/1.18  
% 1.87/1.18  %Foreground operators:
% 1.87/1.18  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 1.87/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.87/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.87/1.18  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.87/1.18  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.87/1.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.87/1.18  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.87/1.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.87/1.18  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.87/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.87/1.18  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 1.87/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.87/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.87/1.18  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.87/1.18  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.87/1.18  
% 1.88/1.19  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 1.88/1.19  tff(f_45, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 1.88/1.19  tff(f_49, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_ordinal1)).
% 1.88/1.19  tff(f_34, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 1.88/1.19  tff(f_47, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 1.88/1.19  tff(f_57, negated_conjecture, ~(![A]: (k6_subset_1(k1_ordinal1(A), k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_ordinal1)).
% 1.88/1.19  tff(f_54, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 1.88/1.19  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.88/1.19  tff(c_103, plain, (![A_35, B_36]: (~r2_hidden('#skF_1'(A_35, B_36), B_36) | r1_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.88/1.19  tff(c_108, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_103])).
% 1.88/1.19  tff(c_18, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k1_tarski(B_15))=A_14 | r2_hidden(B_15, A_14))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.88/1.19  tff(c_22, plain, (![A_18]: (k2_xboole_0(A_18, k1_tarski(A_18))=k1_ordinal1(A_18))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.88/1.19  tff(c_65, plain, (![A_29, B_30]: (k4_xboole_0(k2_xboole_0(A_29, B_30), B_30)=k4_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.88/1.19  tff(c_74, plain, (![A_18]: (k4_xboole_0(k1_ordinal1(A_18), k1_tarski(A_18))=k4_xboole_0(A_18, k1_tarski(A_18)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_65])).
% 1.88/1.19  tff(c_20, plain, (![A_16, B_17]: (k6_subset_1(A_16, B_17)=k4_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.88/1.19  tff(c_26, plain, (k6_subset_1(k1_ordinal1('#skF_2'), k1_tarski('#skF_2'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.88/1.19  tff(c_27, plain, (k4_xboole_0(k1_ordinal1('#skF_2'), k1_tarski('#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_26])).
% 1.88/1.19  tff(c_133, plain, (k4_xboole_0('#skF_2', k1_tarski('#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_27])).
% 1.88/1.19  tff(c_156, plain, (r2_hidden('#skF_2', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_18, c_133])).
% 1.88/1.19  tff(c_24, plain, (![B_20, A_19]: (~r1_tarski(B_20, A_19) | ~r2_hidden(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.88/1.19  tff(c_161, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_156, c_24])).
% 1.88/1.19  tff(c_166, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_108, c_161])).
% 1.88/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.19  
% 1.88/1.19  Inference rules
% 1.88/1.19  ----------------------
% 1.88/1.19  #Ref     : 0
% 1.88/1.19  #Sup     : 31
% 1.88/1.19  #Fact    : 0
% 1.88/1.19  #Define  : 0
% 1.88/1.19  #Split   : 1
% 1.88/1.19  #Chain   : 0
% 1.88/1.19  #Close   : 0
% 1.88/1.19  
% 1.88/1.19  Ordering : KBO
% 1.88/1.19  
% 1.88/1.19  Simplification rules
% 1.88/1.19  ----------------------
% 1.88/1.19  #Subsume      : 0
% 1.88/1.19  #Demod        : 3
% 1.88/1.19  #Tautology    : 17
% 1.88/1.19  #SimpNegUnit  : 0
% 1.88/1.19  #BackRed      : 1
% 1.88/1.19  
% 1.88/1.19  #Partial instantiations: 0
% 1.88/1.19  #Strategies tried      : 1
% 1.88/1.19  
% 1.88/1.19  Timing (in seconds)
% 1.88/1.19  ----------------------
% 1.88/1.19  Preprocessing        : 0.29
% 1.88/1.19  Parsing              : 0.16
% 1.88/1.19  CNF conversion       : 0.02
% 1.88/1.19  Main loop            : 0.13
% 1.88/1.19  Inferencing          : 0.05
% 1.88/1.19  Reduction            : 0.04
% 1.88/1.19  Demodulation         : 0.03
% 1.88/1.19  BG Simplification    : 0.01
% 1.88/1.19  Subsumption          : 0.02
% 1.88/1.19  Abstraction          : 0.01
% 1.88/1.19  MUC search           : 0.00
% 1.88/1.20  Cooper               : 0.00
% 1.88/1.20  Total                : 0.45
% 1.88/1.20  Index Insertion      : 0.00
% 1.88/1.20  Index Deletion       : 0.00
% 1.88/1.20  Index Matching       : 0.00
% 1.88/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
