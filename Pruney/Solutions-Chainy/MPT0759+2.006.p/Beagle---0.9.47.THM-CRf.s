%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:32 EST 2020

% Result     : Theorem 1.64s
% Output     : CNFRefutation 1.79s
% Verified   : 
% Statistics : Number of formulae       :   31 (  33 expanded)
%              Number of leaves         :   17 (  18 expanded)
%              Depth                    :    6
%              Number of atoms          :   28 (  30 expanded)
%              Number of equality atoms :   19 (  21 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > k1_ordinal1 > #skF_1

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

tff(f_43,axiom,(
    ! [A] : A != k1_ordinal1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_ordinal1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_40,axiom,(
    ! [A] : k1_ordinal1(A) = k2_xboole_0(A,k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => k4_xboole_0(k2_xboole_0(B,k1_tarski(A)),k1_tarski(A)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t141_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_46,negated_conjecture,(
    ~ ! [A] : k6_subset_1(k1_ordinal1(A),k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_ordinal1)).

tff(c_12,plain,(
    ! [A_10] : k1_ordinal1(A_10) != A_10 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_68,plain,(
    ! [A_17,B_18] :
      ( k2_xboole_0(k1_tarski(A_17),B_18) = B_18
      | ~ r2_hidden(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_99,plain,(
    ! [B_19,A_20] :
      ( k2_xboole_0(B_19,k1_tarski(A_20)) = B_19
      | ~ r2_hidden(A_20,B_19) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_2])).

tff(c_10,plain,(
    ! [A_9] : k2_xboole_0(A_9,k1_tarski(A_9)) = k1_ordinal1(A_9) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_110,plain,(
    ! [A_20] :
      ( k1_ordinal1(A_20) = A_20
      | ~ r2_hidden(A_20,A_20) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_10])).

tff(c_136,plain,(
    ! [A_20] : ~ r2_hidden(A_20,A_20) ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_110])).

tff(c_140,plain,(
    ! [B_22,A_23] :
      ( k4_xboole_0(k2_xboole_0(B_22,k1_tarski(A_23)),k1_tarski(A_23)) = B_22
      | r2_hidden(A_23,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_156,plain,(
    ! [A_9] :
      ( k4_xboole_0(k1_ordinal1(A_9),k1_tarski(A_9)) = A_9
      | r2_hidden(A_9,A_9) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_140])).

tff(c_167,plain,(
    ! [A_9] : k4_xboole_0(k1_ordinal1(A_9),k1_tarski(A_9)) = A_9 ),
    inference(negUnitSimplification,[status(thm)],[c_136,c_156])).

tff(c_8,plain,(
    ! [A_7,B_8] : k6_subset_1(A_7,B_8) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_14,plain,(
    k6_subset_1(k1_ordinal1('#skF_1'),k1_tarski('#skF_1')) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_15,plain,(
    k4_xboole_0(k1_ordinal1('#skF_1'),k1_tarski('#skF_1')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_14])).

tff(c_170,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:46:29 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.64/1.12  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.64/1.13  
% 1.64/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.64/1.13  %$ r2_hidden > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > k1_ordinal1 > #skF_1
% 1.64/1.13  
% 1.64/1.13  %Foreground sorts:
% 1.64/1.13  
% 1.64/1.13  
% 1.64/1.13  %Background operators:
% 1.64/1.13  
% 1.64/1.13  
% 1.64/1.13  %Foreground operators:
% 1.64/1.13  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 1.64/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.64/1.13  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.64/1.13  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.64/1.13  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.64/1.13  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 1.64/1.13  tff('#skF_1', type, '#skF_1': $i).
% 1.64/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.64/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.64/1.13  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.64/1.13  
% 1.79/1.14  tff(f_43, axiom, (![A]: ~(A = k1_ordinal1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_ordinal1)).
% 1.79/1.14  tff(f_36, axiom, (![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 1.79/1.14  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.79/1.14  tff(f_40, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_ordinal1)).
% 1.79/1.14  tff(f_32, axiom, (![A, B]: (~r2_hidden(A, B) => (k4_xboole_0(k2_xboole_0(B, k1_tarski(A)), k1_tarski(A)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t141_zfmisc_1)).
% 1.79/1.14  tff(f_38, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 1.79/1.14  tff(f_46, negated_conjecture, ~(![A]: (k6_subset_1(k1_ordinal1(A), k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_ordinal1)).
% 1.79/1.14  tff(c_12, plain, (![A_10]: (k1_ordinal1(A_10)!=A_10)), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.79/1.14  tff(c_68, plain, (![A_17, B_18]: (k2_xboole_0(k1_tarski(A_17), B_18)=B_18 | ~r2_hidden(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.79/1.14  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.79/1.14  tff(c_99, plain, (![B_19, A_20]: (k2_xboole_0(B_19, k1_tarski(A_20))=B_19 | ~r2_hidden(A_20, B_19))), inference(superposition, [status(thm), theory('equality')], [c_68, c_2])).
% 1.79/1.14  tff(c_10, plain, (![A_9]: (k2_xboole_0(A_9, k1_tarski(A_9))=k1_ordinal1(A_9))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.79/1.14  tff(c_110, plain, (![A_20]: (k1_ordinal1(A_20)=A_20 | ~r2_hidden(A_20, A_20))), inference(superposition, [status(thm), theory('equality')], [c_99, c_10])).
% 1.79/1.14  tff(c_136, plain, (![A_20]: (~r2_hidden(A_20, A_20))), inference(negUnitSimplification, [status(thm)], [c_12, c_110])).
% 1.79/1.14  tff(c_140, plain, (![B_22, A_23]: (k4_xboole_0(k2_xboole_0(B_22, k1_tarski(A_23)), k1_tarski(A_23))=B_22 | r2_hidden(A_23, B_22))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.79/1.14  tff(c_156, plain, (![A_9]: (k4_xboole_0(k1_ordinal1(A_9), k1_tarski(A_9))=A_9 | r2_hidden(A_9, A_9))), inference(superposition, [status(thm), theory('equality')], [c_10, c_140])).
% 1.79/1.14  tff(c_167, plain, (![A_9]: (k4_xboole_0(k1_ordinal1(A_9), k1_tarski(A_9))=A_9)), inference(negUnitSimplification, [status(thm)], [c_136, c_156])).
% 1.79/1.14  tff(c_8, plain, (![A_7, B_8]: (k6_subset_1(A_7, B_8)=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.79/1.14  tff(c_14, plain, (k6_subset_1(k1_ordinal1('#skF_1'), k1_tarski('#skF_1'))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.79/1.14  tff(c_15, plain, (k4_xboole_0(k1_ordinal1('#skF_1'), k1_tarski('#skF_1'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_8, c_14])).
% 1.79/1.14  tff(c_170, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_167, c_15])).
% 1.79/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.79/1.14  
% 1.79/1.14  Inference rules
% 1.79/1.14  ----------------------
% 1.79/1.14  #Ref     : 0
% 1.79/1.14  #Sup     : 37
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
% 1.79/1.14  #Subsume      : 5
% 1.79/1.14  #Demod        : 2
% 1.79/1.14  #Tautology    : 19
% 1.79/1.14  #SimpNegUnit  : 3
% 1.79/1.14  #BackRed      : 1
% 1.79/1.14  
% 1.79/1.14  #Partial instantiations: 0
% 1.79/1.14  #Strategies tried      : 1
% 1.79/1.14  
% 1.79/1.14  Timing (in seconds)
% 1.79/1.14  ----------------------
% 1.79/1.14  Preprocessing        : 0.27
% 1.79/1.14  Parsing              : 0.14
% 1.79/1.14  CNF conversion       : 0.01
% 1.79/1.14  Main loop            : 0.12
% 1.79/1.14  Inferencing          : 0.05
% 1.79/1.14  Reduction            : 0.04
% 1.79/1.14  Demodulation         : 0.03
% 1.79/1.14  BG Simplification    : 0.01
% 1.79/1.14  Subsumption          : 0.02
% 1.79/1.14  Abstraction          : 0.01
% 1.79/1.14  MUC search           : 0.00
% 1.79/1.14  Cooper               : 0.00
% 1.79/1.14  Total                : 0.41
% 1.79/1.14  Index Insertion      : 0.00
% 1.79/1.14  Index Deletion       : 0.00
% 1.79/1.14  Index Matching       : 0.00
% 1.79/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
