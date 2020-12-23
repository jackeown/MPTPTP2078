%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:28 EST 2020

% Result     : Theorem 1.73s
% Output     : CNFRefutation 1.73s
% Verified   : 
% Statistics : Number of formulae       :   34 (  38 expanded)
%              Number of leaves         :   19 (  22 expanded)
%              Depth                    :    5
%              Number of atoms          :   30 (  36 expanded)
%              Number of equality atoms :   22 (  27 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(f_54,negated_conjecture,(
    ~ ! [A,B] :
        ( k3_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),k1_tarski(B))
        & A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( A != B
     => r1_xboole_0(k1_tarski(A),k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).

tff(c_20,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_67,plain,(
    ! [A_26,B_27] :
      ( r1_xboole_0(A_26,B_27)
      | k4_xboole_0(A_26,B_27) != A_26 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_16,plain,(
    ! [B_14] : ~ r1_xboole_0(k1_tarski(B_14),k1_tarski(B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_75,plain,(
    ! [B_14] : k4_xboole_0(k1_tarski(B_14),k1_tarski(B_14)) != k1_tarski(B_14) ),
    inference(resolution,[status(thm)],[c_67,c_16])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_76,plain,(
    ! [A_28,B_29] : k5_xboole_0(A_28,k3_xboole_0(A_28,B_29)) = k4_xboole_0(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_88,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_76])).

tff(c_22,plain,(
    k3_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_85,plain,(
    k5_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_1')) = k4_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_76])).

tff(c_126,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) = k4_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_85])).

tff(c_18,plain,(
    ! [A_15,B_16] :
      ( r1_xboole_0(k1_tarski(A_15),k1_tarski(B_16))
      | B_16 = A_15 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_53,plain,(
    ! [A_22,B_23] :
      ( k4_xboole_0(A_22,B_23) = A_22
      | ~ r1_xboole_0(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_57,plain,(
    ! [A_15,B_16] :
      ( k4_xboole_0(k1_tarski(A_15),k1_tarski(B_16)) = k1_tarski(A_15)
      | B_16 = A_15 ) ),
    inference(resolution,[status(thm)],[c_18,c_53])).

tff(c_130,plain,
    ( k4_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_1')) = k1_tarski('#skF_1')
    | '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_57])).

tff(c_137,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_75,c_130])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:36:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.73/1.09  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.73/1.09  
% 1.73/1.09  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.73/1.09  %$ r1_xboole_0 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1
% 1.73/1.09  
% 1.73/1.09  %Foreground sorts:
% 1.73/1.09  
% 1.73/1.09  
% 1.73/1.09  %Background operators:
% 1.73/1.09  
% 1.73/1.09  
% 1.73/1.09  %Foreground operators:
% 1.73/1.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.73/1.09  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.73/1.09  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.73/1.09  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.73/1.09  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.73/1.09  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.73/1.09  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.73/1.09  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.73/1.09  tff('#skF_2', type, '#skF_2': $i).
% 1.73/1.09  tff('#skF_1', type, '#skF_1': $i).
% 1.73/1.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.73/1.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.73/1.09  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.73/1.09  
% 1.73/1.10  tff(f_54, negated_conjecture, ~(![A, B]: ((k3_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_zfmisc_1)).
% 1.73/1.10  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 1.73/1.10  tff(f_44, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), k1_tarski(B)) & (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_zfmisc_1)).
% 1.73/1.10  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 1.73/1.10  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 1.73/1.10  tff(f_49, axiom, (![A, B]: (~(A = B) => r1_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 1.73/1.10  tff(c_20, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.73/1.10  tff(c_67, plain, (![A_26, B_27]: (r1_xboole_0(A_26, B_27) | k4_xboole_0(A_26, B_27)!=A_26)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.73/1.10  tff(c_16, plain, (![B_14]: (~r1_xboole_0(k1_tarski(B_14), k1_tarski(B_14)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.73/1.10  tff(c_75, plain, (![B_14]: (k4_xboole_0(k1_tarski(B_14), k1_tarski(B_14))!=k1_tarski(B_14))), inference(resolution, [status(thm)], [c_67, c_16])).
% 1.73/1.10  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.73/1.10  tff(c_76, plain, (![A_28, B_29]: (k5_xboole_0(A_28, k3_xboole_0(A_28, B_29))=k4_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.73/1.10  tff(c_88, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_76])).
% 1.73/1.10  tff(c_22, plain, (k3_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.73/1.10  tff(c_85, plain, (k5_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_1'))=k4_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_22, c_76])).
% 1.73/1.10  tff(c_126, plain, (k4_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))=k4_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_85])).
% 1.73/1.10  tff(c_18, plain, (![A_15, B_16]: (r1_xboole_0(k1_tarski(A_15), k1_tarski(B_16)) | B_16=A_15)), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.73/1.10  tff(c_53, plain, (![A_22, B_23]: (k4_xboole_0(A_22, B_23)=A_22 | ~r1_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.73/1.10  tff(c_57, plain, (![A_15, B_16]: (k4_xboole_0(k1_tarski(A_15), k1_tarski(B_16))=k1_tarski(A_15) | B_16=A_15)), inference(resolution, [status(thm)], [c_18, c_53])).
% 1.73/1.10  tff(c_130, plain, (k4_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_1'))=k1_tarski('#skF_1') | '#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_126, c_57])).
% 1.73/1.10  tff(c_137, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_75, c_130])).
% 1.73/1.10  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.73/1.10  
% 1.73/1.10  Inference rules
% 1.73/1.10  ----------------------
% 1.73/1.10  #Ref     : 0
% 1.73/1.10  #Sup     : 27
% 1.73/1.10  #Fact    : 0
% 1.73/1.10  #Define  : 0
% 1.73/1.10  #Split   : 0
% 1.73/1.10  #Chain   : 0
% 1.73/1.10  #Close   : 0
% 1.73/1.10  
% 1.73/1.10  Ordering : KBO
% 1.73/1.10  
% 1.73/1.10  Simplification rules
% 1.73/1.10  ----------------------
% 1.73/1.10  #Subsume      : 0
% 1.73/1.10  #Demod        : 1
% 1.73/1.10  #Tautology    : 20
% 1.73/1.10  #SimpNegUnit  : 1
% 1.73/1.10  #BackRed      : 0
% 1.73/1.10  
% 1.73/1.10  #Partial instantiations: 0
% 1.73/1.10  #Strategies tried      : 1
% 1.73/1.10  
% 1.73/1.10  Timing (in seconds)
% 1.73/1.10  ----------------------
% 1.73/1.11  Preprocessing        : 0.27
% 1.73/1.11  Parsing              : 0.14
% 1.73/1.11  CNF conversion       : 0.02
% 1.73/1.11  Main loop            : 0.11
% 1.73/1.11  Inferencing          : 0.05
% 1.73/1.11  Reduction            : 0.03
% 1.73/1.11  Demodulation         : 0.02
% 1.73/1.11  BG Simplification    : 0.01
% 1.73/1.11  Subsumption          : 0.01
% 1.73/1.11  Abstraction          : 0.01
% 1.73/1.11  MUC search           : 0.00
% 1.73/1.11  Cooper               : 0.00
% 1.73/1.11  Total                : 0.40
% 1.73/1.11  Index Insertion      : 0.00
% 1.73/1.11  Index Deletion       : 0.00
% 1.73/1.11  Index Matching       : 0.00
% 1.73/1.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
