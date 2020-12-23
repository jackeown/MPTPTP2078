%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:33 EST 2020

% Result     : Theorem 1.67s
% Output     : CNFRefutation 1.79s
% Verified   : 
% Statistics : Number of formulae       :   33 (  34 expanded)
%              Number of leaves         :   20 (  21 expanded)
%              Depth                    :    5
%              Number of atoms          :   28 (  31 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k1_enumset1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_ordinal1 > #skF_2 > #skF_1

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
    ! [A] : k1_ordinal1(A) = k2_xboole_0(A,k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => k4_xboole_0(k2_xboole_0(B,k1_tarski(A)),k1_tarski(A)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t141_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_53,negated_conjecture,(
    ~ ! [A] : k6_subset_1(k1_ordinal1(A),k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_ordinal1)).

tff(f_50,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_64,plain,(
    ! [A_26,B_27] :
      ( ~ r2_hidden('#skF_1'(A_26,B_27),B_27)
      | r1_tarski(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_69,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_64])).

tff(c_16,plain,(
    ! [A_13] : k2_xboole_0(A_13,k1_tarski(A_13)) = k1_ordinal1(A_13) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_76,plain,(
    ! [B_34,A_35] :
      ( k4_xboole_0(k2_xboole_0(B_34,k1_tarski(A_35)),k1_tarski(A_35)) = B_34
      | r2_hidden(A_35,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_88,plain,(
    ! [A_36] :
      ( k4_xboole_0(k1_ordinal1(A_36),k1_tarski(A_36)) = A_36
      | r2_hidden(A_36,A_36) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_76])).

tff(c_14,plain,(
    ! [A_11,B_12] : k6_subset_1(A_11,B_12) = k4_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_20,plain,(
    k6_subset_1(k1_ordinal1('#skF_2'),k1_tarski('#skF_2')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_21,plain,(
    k4_xboole_0(k1_ordinal1('#skF_2'),k1_tarski('#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_20])).

tff(c_99,plain,(
    r2_hidden('#skF_2','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_21])).

tff(c_18,plain,(
    ! [B_15,A_14] :
      ( ~ r1_tarski(B_15,A_14)
      | ~ r2_hidden(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_105,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_99,c_18])).

tff(c_110,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_105])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:24:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.67/1.12  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.67/1.13  
% 1.67/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.79/1.13  %$ r2_hidden > r1_tarski > k1_enumset1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_ordinal1 > #skF_2 > #skF_1
% 1.79/1.13  
% 1.79/1.13  %Foreground sorts:
% 1.79/1.13  
% 1.79/1.13  
% 1.79/1.13  %Background operators:
% 1.79/1.13  
% 1.79/1.13  
% 1.79/1.13  %Foreground operators:
% 1.79/1.13  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 1.79/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.79/1.13  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.79/1.13  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.79/1.13  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.79/1.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.79/1.13  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.79/1.13  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.79/1.13  tff('#skF_2', type, '#skF_2': $i).
% 1.79/1.13  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 1.79/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.79/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.79/1.13  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.79/1.13  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.79/1.13  
% 1.79/1.14  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 1.79/1.14  tff(f_45, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_ordinal1)).
% 1.79/1.14  tff(f_41, axiom, (![A, B]: (~r2_hidden(A, B) => (k4_xboole_0(k2_xboole_0(B, k1_tarski(A)), k1_tarski(A)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t141_zfmisc_1)).
% 1.79/1.14  tff(f_43, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 1.79/1.14  tff(f_53, negated_conjecture, ~(![A]: (k6_subset_1(k1_ordinal1(A), k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_ordinal1)).
% 1.79/1.14  tff(f_50, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 1.79/1.14  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.79/1.14  tff(c_64, plain, (![A_26, B_27]: (~r2_hidden('#skF_1'(A_26, B_27), B_27) | r1_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.79/1.14  tff(c_69, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_64])).
% 1.79/1.14  tff(c_16, plain, (![A_13]: (k2_xboole_0(A_13, k1_tarski(A_13))=k1_ordinal1(A_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.79/1.14  tff(c_76, plain, (![B_34, A_35]: (k4_xboole_0(k2_xboole_0(B_34, k1_tarski(A_35)), k1_tarski(A_35))=B_34 | r2_hidden(A_35, B_34))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.79/1.14  tff(c_88, plain, (![A_36]: (k4_xboole_0(k1_ordinal1(A_36), k1_tarski(A_36))=A_36 | r2_hidden(A_36, A_36))), inference(superposition, [status(thm), theory('equality')], [c_16, c_76])).
% 1.79/1.14  tff(c_14, plain, (![A_11, B_12]: (k6_subset_1(A_11, B_12)=k4_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.79/1.14  tff(c_20, plain, (k6_subset_1(k1_ordinal1('#skF_2'), k1_tarski('#skF_2'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.79/1.14  tff(c_21, plain, (k4_xboole_0(k1_ordinal1('#skF_2'), k1_tarski('#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_20])).
% 1.79/1.14  tff(c_99, plain, (r2_hidden('#skF_2', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_88, c_21])).
% 1.79/1.14  tff(c_18, plain, (![B_15, A_14]: (~r1_tarski(B_15, A_14) | ~r2_hidden(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.79/1.14  tff(c_105, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_99, c_18])).
% 1.79/1.14  tff(c_110, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_69, c_105])).
% 1.79/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.79/1.14  
% 1.79/1.14  Inference rules
% 1.79/1.14  ----------------------
% 1.79/1.14  #Ref     : 0
% 1.79/1.14  #Sup     : 19
% 1.79/1.14  #Fact    : 0
% 1.79/1.14  #Define  : 0
% 1.79/1.14  #Split   : 0
% 1.79/1.14  #Chain   : 0
% 1.79/1.14  #Close   : 0
% 1.79/1.14  
% 1.79/1.14  Ordering : KBO
% 1.79/1.14  
% 1.79/1.14  Simplification rules
% 1.79/1.14  ----------------------
% 1.79/1.14  #Subsume      : 0
% 1.79/1.14  #Demod        : 2
% 1.79/1.14  #Tautology    : 12
% 1.79/1.14  #SimpNegUnit  : 0
% 1.79/1.14  #BackRed      : 0
% 1.79/1.14  
% 1.79/1.14  #Partial instantiations: 0
% 1.79/1.14  #Strategies tried      : 1
% 1.79/1.14  
% 1.79/1.14  Timing (in seconds)
% 1.79/1.14  ----------------------
% 1.79/1.14  Preprocessing        : 0.28
% 1.79/1.14  Parsing              : 0.15
% 1.79/1.14  CNF conversion       : 0.02
% 1.79/1.14  Main loop            : 0.10
% 1.79/1.14  Inferencing          : 0.05
% 1.79/1.14  Reduction            : 0.03
% 1.79/1.14  Demodulation         : 0.02
% 1.79/1.14  BG Simplification    : 0.01
% 1.79/1.14  Subsumption          : 0.01
% 1.79/1.14  Abstraction          : 0.01
% 1.79/1.14  MUC search           : 0.00
% 1.79/1.14  Cooper               : 0.00
% 1.79/1.14  Total                : 0.40
% 1.79/1.14  Index Insertion      : 0.00
% 1.79/1.14  Index Deletion       : 0.00
% 1.79/1.14  Index Matching       : 0.00
% 1.79/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
