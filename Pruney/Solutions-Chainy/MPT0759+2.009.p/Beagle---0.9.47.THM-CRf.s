%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:33 EST 2020

% Result     : Theorem 1.67s
% Output     : CNFRefutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :   32 (  32 expanded)
%              Number of leaves         :   19 (  19 expanded)
%              Depth                    :    6
%              Number of atoms          :   26 (  26 expanded)
%              Number of equality atoms :   14 (  14 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_ordinal1 > #skF_1

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_44,axiom,(
    ! [A] : k1_ordinal1(A) = k2_xboole_0(A,k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_42,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_52,negated_conjecture,(
    ~ ! [A] : k6_subset_1(k1_ordinal1(A),k1_tarski(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_ordinal1)).

tff(f_49,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14,plain,(
    ! [A_6,B_7] :
      ( k4_xboole_0(A_6,k1_tarski(B_7)) = A_6
      | r2_hidden(B_7,A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_18,plain,(
    ! [A_10] : k2_xboole_0(A_10,k1_tarski(A_10)) = k1_ordinal1(A_10) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_54,plain,(
    ! [A_20,B_21] : k4_xboole_0(k2_xboole_0(A_20,B_21),B_21) = k4_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_63,plain,(
    ! [A_10] : k4_xboole_0(k1_ordinal1(A_10),k1_tarski(A_10)) = k4_xboole_0(A_10,k1_tarski(A_10)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_54])).

tff(c_16,plain,(
    ! [A_8,B_9] : k6_subset_1(A_8,B_9) = k4_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_22,plain,(
    k6_subset_1(k1_ordinal1('#skF_1'),k1_tarski('#skF_1')) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_23,plain,(
    k4_xboole_0(k1_ordinal1('#skF_1'),k1_tarski('#skF_1')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_22])).

tff(c_103,plain,(
    k4_xboole_0('#skF_1',k1_tarski('#skF_1')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_23])).

tff(c_126,plain,(
    r2_hidden('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_103])).

tff(c_20,plain,(
    ! [B_12,A_11] :
      ( ~ r1_tarski(B_12,A_11)
      | ~ r2_hidden(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_129,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_126,c_20])).

tff(c_133,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_129])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:15:00 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.67/1.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.16  
% 1.67/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.16  %$ r2_hidden > r1_tarski > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_ordinal1 > #skF_1
% 1.67/1.16  
% 1.67/1.16  %Foreground sorts:
% 1.67/1.16  
% 1.67/1.16  
% 1.67/1.16  %Background operators:
% 1.67/1.16  
% 1.67/1.16  
% 1.67/1.16  %Foreground operators:
% 1.67/1.16  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 1.67/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.67/1.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.67/1.16  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.67/1.16  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.67/1.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.67/1.16  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.67/1.16  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 1.67/1.16  tff('#skF_1', type, '#skF_1': $i).
% 1.67/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.67/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.67/1.16  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.67/1.16  
% 1.67/1.17  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.67/1.17  tff(f_40, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 1.67/1.17  tff(f_44, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_ordinal1)).
% 1.67/1.17  tff(f_33, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 1.67/1.17  tff(f_42, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 1.67/1.17  tff(f_52, negated_conjecture, ~(![A]: (k6_subset_1(k1_ordinal1(A), k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_ordinal1)).
% 1.67/1.17  tff(f_49, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 1.67/1.17  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.67/1.17  tff(c_14, plain, (![A_6, B_7]: (k4_xboole_0(A_6, k1_tarski(B_7))=A_6 | r2_hidden(B_7, A_6))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.67/1.17  tff(c_18, plain, (![A_10]: (k2_xboole_0(A_10, k1_tarski(A_10))=k1_ordinal1(A_10))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.67/1.17  tff(c_54, plain, (![A_20, B_21]: (k4_xboole_0(k2_xboole_0(A_20, B_21), B_21)=k4_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.67/1.17  tff(c_63, plain, (![A_10]: (k4_xboole_0(k1_ordinal1(A_10), k1_tarski(A_10))=k4_xboole_0(A_10, k1_tarski(A_10)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_54])).
% 1.67/1.17  tff(c_16, plain, (![A_8, B_9]: (k6_subset_1(A_8, B_9)=k4_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.67/1.17  tff(c_22, plain, (k6_subset_1(k1_ordinal1('#skF_1'), k1_tarski('#skF_1'))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.67/1.17  tff(c_23, plain, (k4_xboole_0(k1_ordinal1('#skF_1'), k1_tarski('#skF_1'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_22])).
% 1.67/1.17  tff(c_103, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_1'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_63, c_23])).
% 1.67/1.17  tff(c_126, plain, (r2_hidden('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_14, c_103])).
% 1.67/1.17  tff(c_20, plain, (![B_12, A_11]: (~r1_tarski(B_12, A_11) | ~r2_hidden(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.67/1.17  tff(c_129, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_126, c_20])).
% 1.67/1.17  tff(c_133, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_129])).
% 1.67/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.17  
% 1.67/1.17  Inference rules
% 1.67/1.17  ----------------------
% 1.67/1.17  #Ref     : 0
% 1.67/1.17  #Sup     : 24
% 1.67/1.17  #Fact    : 0
% 1.67/1.17  #Define  : 0
% 1.67/1.17  #Split   : 1
% 1.67/1.17  #Chain   : 0
% 1.67/1.17  #Close   : 0
% 1.67/1.17  
% 1.67/1.17  Ordering : KBO
% 1.67/1.17  
% 1.67/1.17  Simplification rules
% 1.67/1.17  ----------------------
% 1.67/1.17  #Subsume      : 0
% 1.67/1.17  #Demod        : 5
% 1.67/1.17  #Tautology    : 15
% 1.67/1.17  #SimpNegUnit  : 0
% 1.67/1.17  #BackRed      : 1
% 1.67/1.17  
% 1.67/1.17  #Partial instantiations: 0
% 1.67/1.17  #Strategies tried      : 1
% 1.67/1.17  
% 1.67/1.17  Timing (in seconds)
% 1.67/1.17  ----------------------
% 1.67/1.18  Preprocessing        : 0.29
% 1.67/1.18  Parsing              : 0.16
% 1.67/1.18  CNF conversion       : 0.02
% 1.67/1.18  Main loop            : 0.11
% 1.67/1.18  Inferencing          : 0.04
% 1.67/1.18  Reduction            : 0.03
% 1.67/1.18  Demodulation         : 0.02
% 1.67/1.18  BG Simplification    : 0.01
% 1.67/1.18  Subsumption          : 0.01
% 1.67/1.18  Abstraction          : 0.01
% 1.67/1.18  MUC search           : 0.00
% 1.67/1.18  Cooper               : 0.00
% 1.67/1.18  Total                : 0.42
% 1.67/1.18  Index Insertion      : 0.00
% 1.67/1.18  Index Deletion       : 0.00
% 1.67/1.18  Index Matching       : 0.00
% 1.67/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
