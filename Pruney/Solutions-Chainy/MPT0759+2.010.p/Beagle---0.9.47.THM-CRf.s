%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:33 EST 2020

% Result     : Theorem 1.69s
% Output     : CNFRefutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :   36 (  36 expanded)
%              Number of leaves         :   21 (  21 expanded)
%              Depth                    :    7
%              Number of atoms          :   34 (  34 expanded)
%              Number of equality atoms :   16 (  16 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_ordinal1 > #skF_1

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_46,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_50,axiom,(
    ! [A] : k1_ordinal1(A) = k2_xboole_0(A,k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => k4_xboole_0(k2_xboole_0(A,B),B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_58,negated_conjecture,(
    ~ ! [A] : k6_subset_1(k1_ordinal1(A),k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_ordinal1)).

tff(f_55,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_18,plain,(
    ! [A_8,B_9] :
      ( k4_xboole_0(A_8,k1_tarski(B_9)) = A_8
      | r2_hidden(B_9,A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( r1_xboole_0(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != A_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_22,plain,(
    ! [A_12] : k2_xboole_0(A_12,k1_tarski(A_12)) = k1_ordinal1(A_12) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_89,plain,(
    ! [A_32,B_33] :
      ( k4_xboole_0(k2_xboole_0(A_32,B_33),B_33) = A_32
      | ~ r1_xboole_0(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_113,plain,(
    ! [A_34] :
      ( k4_xboole_0(k1_ordinal1(A_34),k1_tarski(A_34)) = A_34
      | ~ r1_xboole_0(A_34,k1_tarski(A_34)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_89])).

tff(c_20,plain,(
    ! [A_10,B_11] : k6_subset_1(A_10,B_11) = k4_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_26,plain,(
    k6_subset_1(k1_ordinal1('#skF_1'),k1_tarski('#skF_1')) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_27,plain,(
    k4_xboole_0(k1_ordinal1('#skF_1'),k1_tarski('#skF_1')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_26])).

tff(c_134,plain,(
    ~ r1_xboole_0('#skF_1',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_27])).

tff(c_148,plain,(
    k4_xboole_0('#skF_1',k1_tarski('#skF_1')) != '#skF_1' ),
    inference(resolution,[status(thm)],[c_10,c_134])).

tff(c_152,plain,(
    r2_hidden('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_148])).

tff(c_24,plain,(
    ! [B_14,A_13] :
      ( ~ r1_tarski(B_14,A_13)
      | ~ r2_hidden(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_155,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_152,c_24])).

tff(c_159,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_155])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:47:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.69/1.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.69/1.18  
% 1.69/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.69/1.18  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_ordinal1 > #skF_1
% 1.69/1.18  
% 1.69/1.18  %Foreground sorts:
% 1.69/1.18  
% 1.69/1.18  
% 1.69/1.18  %Background operators:
% 1.69/1.18  
% 1.69/1.18  
% 1.69/1.18  %Foreground operators:
% 1.69/1.18  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 1.69/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.69/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.69/1.18  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.69/1.18  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.69/1.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.69/1.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.69/1.18  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.69/1.18  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 1.69/1.18  tff('#skF_1', type, '#skF_1': $i).
% 1.69/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.69/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.69/1.18  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.69/1.18  
% 1.94/1.19  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.94/1.19  tff(f_46, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 1.94/1.19  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 1.94/1.19  tff(f_50, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_ordinal1)).
% 1.94/1.19  tff(f_39, axiom, (![A, B]: (r1_xboole_0(A, B) => (k4_xboole_0(k2_xboole_0(A, B), B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_xboole_1)).
% 1.94/1.19  tff(f_48, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 1.94/1.19  tff(f_58, negated_conjecture, ~(![A]: (k6_subset_1(k1_ordinal1(A), k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_ordinal1)).
% 1.94/1.19  tff(f_55, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 1.94/1.19  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.94/1.19  tff(c_18, plain, (![A_8, B_9]: (k4_xboole_0(A_8, k1_tarski(B_9))=A_8 | r2_hidden(B_9, A_8))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.94/1.19  tff(c_10, plain, (![A_3, B_4]: (r1_xboole_0(A_3, B_4) | k4_xboole_0(A_3, B_4)!=A_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.94/1.19  tff(c_22, plain, (![A_12]: (k2_xboole_0(A_12, k1_tarski(A_12))=k1_ordinal1(A_12))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.94/1.19  tff(c_89, plain, (![A_32, B_33]: (k4_xboole_0(k2_xboole_0(A_32, B_33), B_33)=A_32 | ~r1_xboole_0(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.94/1.19  tff(c_113, plain, (![A_34]: (k4_xboole_0(k1_ordinal1(A_34), k1_tarski(A_34))=A_34 | ~r1_xboole_0(A_34, k1_tarski(A_34)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_89])).
% 1.94/1.19  tff(c_20, plain, (![A_10, B_11]: (k6_subset_1(A_10, B_11)=k4_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.94/1.19  tff(c_26, plain, (k6_subset_1(k1_ordinal1('#skF_1'), k1_tarski('#skF_1'))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.94/1.19  tff(c_27, plain, (k4_xboole_0(k1_ordinal1('#skF_1'), k1_tarski('#skF_1'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_26])).
% 1.94/1.19  tff(c_134, plain, (~r1_xboole_0('#skF_1', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_113, c_27])).
% 1.94/1.19  tff(c_148, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_1'))!='#skF_1'), inference(resolution, [status(thm)], [c_10, c_134])).
% 1.94/1.19  tff(c_152, plain, (r2_hidden('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_18, c_148])).
% 1.94/1.19  tff(c_24, plain, (![B_14, A_13]: (~r1_tarski(B_14, A_13) | ~r2_hidden(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.94/1.19  tff(c_155, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_152, c_24])).
% 1.94/1.19  tff(c_159, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_155])).
% 1.94/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.19  
% 1.94/1.19  Inference rules
% 1.94/1.19  ----------------------
% 1.94/1.19  #Ref     : 0
% 1.94/1.19  #Sup     : 29
% 1.94/1.19  #Fact    : 0
% 1.94/1.19  #Define  : 0
% 1.94/1.19  #Split   : 1
% 1.94/1.19  #Chain   : 0
% 1.94/1.19  #Close   : 0
% 1.94/1.19  
% 1.94/1.19  Ordering : KBO
% 1.94/1.19  
% 1.94/1.19  Simplification rules
% 1.94/1.19  ----------------------
% 1.94/1.19  #Subsume      : 0
% 1.94/1.19  #Demod        : 5
% 1.94/1.19  #Tautology    : 16
% 1.94/1.19  #SimpNegUnit  : 0
% 1.94/1.19  #BackRed      : 0
% 1.94/1.19  
% 1.94/1.19  #Partial instantiations: 0
% 1.94/1.19  #Strategies tried      : 1
% 1.94/1.19  
% 1.94/1.19  Timing (in seconds)
% 1.94/1.19  ----------------------
% 1.94/1.19  Preprocessing        : 0.29
% 1.94/1.19  Parsing              : 0.15
% 1.94/1.19  CNF conversion       : 0.02
% 1.94/1.19  Main loop            : 0.13
% 1.94/1.19  Inferencing          : 0.05
% 1.94/1.19  Reduction            : 0.04
% 1.94/1.19  Demodulation         : 0.03
% 1.94/1.19  BG Simplification    : 0.01
% 1.94/1.19  Subsumption          : 0.02
% 1.94/1.19  Abstraction          : 0.01
% 1.94/1.19  MUC search           : 0.00
% 1.94/1.19  Cooper               : 0.00
% 1.94/1.19  Total                : 0.45
% 1.94/1.19  Index Insertion      : 0.00
% 1.94/1.19  Index Deletion       : 0.00
% 1.94/1.19  Index Matching       : 0.00
% 1.94/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
