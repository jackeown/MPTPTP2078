%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:57 EST 2020

% Result     : Theorem 1.86s
% Output     : CNFRefutation 1.86s
% Verified   : 
% Statistics : Number of formulae       :   32 (  36 expanded)
%              Number of leaves         :   19 (  22 expanded)
%              Depth                    :    6
%              Number of atoms          :   24 (  30 expanded)
%              Number of equality atoms :   19 (  24 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_51,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k1_tarski(A),k1_tarski(B))
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(c_20,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_16,plain,(
    ! [B_18] : k4_xboole_0(k1_tarski(B_18),k1_tarski(B_18)) != k1_tarski(B_18) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_60,plain,(
    ! [A_26,B_27] : k5_xboole_0(A_26,k3_xboole_0(A_26,B_27)) = k4_xboole_0(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_72,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_60])).

tff(c_22,plain,(
    r1_tarski(k1_tarski('#skF_1'),k1_tarski('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_41,plain,(
    ! [A_21,B_22] :
      ( k3_xboole_0(A_21,B_22) = A_21
      | ~ r1_tarski(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_45,plain,(
    k3_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) = k1_tarski('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_41])).

tff(c_69,plain,(
    k5_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_1')) = k4_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_45,c_60])).

tff(c_79,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) = k4_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_69])).

tff(c_18,plain,(
    ! [A_17,B_18] :
      ( k4_xboole_0(k1_tarski(A_17),k1_tarski(B_18)) = k1_tarski(A_17)
      | B_18 = A_17 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_117,plain,
    ( k4_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_1')) = k1_tarski('#skF_1')
    | '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_18])).

tff(c_124,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_16,c_117])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:39:25 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.86/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.86/1.32  
% 1.86/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.86/1.32  %$ r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1
% 1.86/1.32  
% 1.86/1.32  %Foreground sorts:
% 1.86/1.32  
% 1.86/1.32  
% 1.86/1.32  %Background operators:
% 1.86/1.32  
% 1.86/1.32  
% 1.86/1.32  %Foreground operators:
% 1.86/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.86/1.32  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.86/1.32  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.86/1.32  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.86/1.32  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.86/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.86/1.32  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.86/1.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.86/1.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.86/1.32  tff('#skF_2', type, '#skF_2': $i).
% 1.86/1.32  tff('#skF_1', type, '#skF_1': $i).
% 1.86/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.86/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.86/1.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.86/1.32  
% 1.86/1.33  tff(f_51, negated_conjecture, ~(![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_zfmisc_1)).
% 1.86/1.33  tff(f_46, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 1.86/1.33  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 1.86/1.33  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 1.86/1.33  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.86/1.33  tff(c_20, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.86/1.33  tff(c_16, plain, (![B_18]: (k4_xboole_0(k1_tarski(B_18), k1_tarski(B_18))!=k1_tarski(B_18))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.86/1.33  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.86/1.33  tff(c_60, plain, (![A_26, B_27]: (k5_xboole_0(A_26, k3_xboole_0(A_26, B_27))=k4_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.86/1.33  tff(c_72, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_60])).
% 1.86/1.33  tff(c_22, plain, (r1_tarski(k1_tarski('#skF_1'), k1_tarski('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.86/1.33  tff(c_41, plain, (![A_21, B_22]: (k3_xboole_0(A_21, B_22)=A_21 | ~r1_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.86/1.33  tff(c_45, plain, (k3_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))=k1_tarski('#skF_1')), inference(resolution, [status(thm)], [c_22, c_41])).
% 1.86/1.33  tff(c_69, plain, (k5_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_1'))=k4_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_45, c_60])).
% 1.86/1.33  tff(c_79, plain, (k4_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))=k4_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_69])).
% 1.86/1.33  tff(c_18, plain, (![A_17, B_18]: (k4_xboole_0(k1_tarski(A_17), k1_tarski(B_18))=k1_tarski(A_17) | B_18=A_17)), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.86/1.33  tff(c_117, plain, (k4_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_1'))=k1_tarski('#skF_1') | '#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_79, c_18])).
% 1.86/1.33  tff(c_124, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_16, c_117])).
% 1.86/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.86/1.33  
% 1.86/1.33  Inference rules
% 1.86/1.33  ----------------------
% 1.86/1.33  #Ref     : 0
% 1.86/1.33  #Sup     : 26
% 1.86/1.33  #Fact    : 0
% 1.86/1.33  #Define  : 0
% 1.86/1.33  #Split   : 0
% 1.86/1.33  #Chain   : 0
% 1.86/1.33  #Close   : 0
% 1.86/1.33  
% 1.86/1.33  Ordering : KBO
% 1.86/1.33  
% 1.86/1.33  Simplification rules
% 1.86/1.33  ----------------------
% 1.86/1.33  #Subsume      : 0
% 1.86/1.33  #Demod        : 1
% 1.86/1.33  #Tautology    : 20
% 1.86/1.33  #SimpNegUnit  : 1
% 1.86/1.33  #BackRed      : 1
% 1.86/1.33  
% 1.86/1.33  #Partial instantiations: 0
% 1.86/1.33  #Strategies tried      : 1
% 1.86/1.33  
% 1.86/1.33  Timing (in seconds)
% 1.86/1.33  ----------------------
% 1.86/1.33  Preprocessing        : 0.31
% 1.86/1.33  Parsing              : 0.16
% 1.86/1.33  CNF conversion       : 0.02
% 1.86/1.33  Main loop            : 0.10
% 1.86/1.33  Inferencing          : 0.04
% 1.86/1.33  Reduction            : 0.03
% 1.86/1.33  Demodulation         : 0.02
% 1.86/1.33  BG Simplification    : 0.01
% 1.86/1.33  Subsumption          : 0.01
% 1.86/1.33  Abstraction          : 0.01
% 1.86/1.33  MUC search           : 0.00
% 1.86/1.33  Cooper               : 0.00
% 1.86/1.33  Total                : 0.43
% 1.86/1.33  Index Insertion      : 0.00
% 1.86/1.33  Index Deletion       : 0.00
% 1.86/1.33  Index Matching       : 0.00
% 1.86/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
