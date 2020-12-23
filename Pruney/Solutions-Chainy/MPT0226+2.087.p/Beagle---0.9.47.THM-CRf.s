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
% DateTime   : Thu Dec  3 09:48:48 EST 2020

% Result     : Theorem 1.75s
% Output     : CNFRefutation 1.75s
% Verified   : 
% Statistics : Number of formulae       :   31 (  44 expanded)
%              Number of leaves         :   18 (  24 expanded)
%              Depth                    :    6
%              Number of atoms          :   27 (  50 expanded)
%              Number of equality atoms :   19 (  37 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(f_52,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_xboole_0
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( A != B
     => r1_xboole_0(k1_tarski(A),k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_29,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_42,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),k1_tarski(B))
        & A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_zfmisc_1)).

tff(c_18,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_16,plain,(
    ! [A_11,B_12] :
      ( r1_xboole_0(k1_tarski(A_11),k1_tarski(B_12))
      | B_12 = A_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_63,plain,(
    ! [A_22,B_23] :
      ( k4_xboole_0(A_22,B_23) = A_22
      | ~ r1_xboole_0(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_83,plain,(
    ! [A_27,B_28] :
      ( k4_xboole_0(k1_tarski(A_27),k1_tarski(B_28)) = k1_tarski(A_27)
      | B_28 = A_27 ) ),
    inference(resolution,[status(thm)],[c_16,c_63])).

tff(c_20,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_93,plain,
    ( k1_tarski('#skF_1') = k1_xboole_0
    | '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_20])).

tff(c_103,plain,(
    k1_tarski('#skF_1') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_93])).

tff(c_4,plain,(
    ! [A_3] : k4_xboole_0(k1_xboole_0,A_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_42,plain,(
    ! [A_16,B_17] :
      ( r1_xboole_0(A_16,B_17)
      | k4_xboole_0(A_16,B_17) != A_16 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_14,plain,(
    ! [B_10] : ~ r1_xboole_0(k1_tarski(B_10),k1_tarski(B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_46,plain,(
    ! [B_10] : k4_xboole_0(k1_tarski(B_10),k1_tarski(B_10)) != k1_tarski(B_10) ),
    inference(resolution,[status(thm)],[c_42,c_14])).

tff(c_117,plain,(
    k4_xboole_0(k1_xboole_0,k1_tarski('#skF_1')) != k1_tarski('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_46])).

tff(c_138,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_4,c_117])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:34:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.75/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.75/1.19  
% 1.75/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.75/1.19  %$ r1_xboole_0 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 1.75/1.19  
% 1.75/1.19  %Foreground sorts:
% 1.75/1.19  
% 1.75/1.19  
% 1.75/1.19  %Background operators:
% 1.75/1.19  
% 1.75/1.19  
% 1.75/1.19  %Foreground operators:
% 1.75/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.75/1.19  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.75/1.19  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.75/1.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.75/1.19  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.75/1.19  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.75/1.19  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.75/1.19  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.75/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.75/1.19  tff('#skF_1', type, '#skF_1': $i).
% 1.75/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.75/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.75/1.19  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.75/1.19  
% 1.75/1.20  tff(f_52, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_xboole_0) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_zfmisc_1)).
% 1.75/1.20  tff(f_47, axiom, (![A, B]: (~(A = B) => r1_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 1.75/1.20  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 1.75/1.20  tff(f_29, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 1.75/1.20  tff(f_42, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), k1_tarski(B)) & (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_zfmisc_1)).
% 1.75/1.20  tff(c_18, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.75/1.20  tff(c_16, plain, (![A_11, B_12]: (r1_xboole_0(k1_tarski(A_11), k1_tarski(B_12)) | B_12=A_11)), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.75/1.20  tff(c_63, plain, (![A_22, B_23]: (k4_xboole_0(A_22, B_23)=A_22 | ~r1_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.75/1.20  tff(c_83, plain, (![A_27, B_28]: (k4_xboole_0(k1_tarski(A_27), k1_tarski(B_28))=k1_tarski(A_27) | B_28=A_27)), inference(resolution, [status(thm)], [c_16, c_63])).
% 1.75/1.20  tff(c_20, plain, (k4_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.75/1.20  tff(c_93, plain, (k1_tarski('#skF_1')=k1_xboole_0 | '#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_83, c_20])).
% 1.75/1.20  tff(c_103, plain, (k1_tarski('#skF_1')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_18, c_93])).
% 1.75/1.20  tff(c_4, plain, (![A_3]: (k4_xboole_0(k1_xboole_0, A_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.75/1.20  tff(c_42, plain, (![A_16, B_17]: (r1_xboole_0(A_16, B_17) | k4_xboole_0(A_16, B_17)!=A_16)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.75/1.20  tff(c_14, plain, (![B_10]: (~r1_xboole_0(k1_tarski(B_10), k1_tarski(B_10)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.75/1.20  tff(c_46, plain, (![B_10]: (k4_xboole_0(k1_tarski(B_10), k1_tarski(B_10))!=k1_tarski(B_10))), inference(resolution, [status(thm)], [c_42, c_14])).
% 1.75/1.20  tff(c_117, plain, (k4_xboole_0(k1_xboole_0, k1_tarski('#skF_1'))!=k1_tarski('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_103, c_46])).
% 1.75/1.20  tff(c_138, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_103, c_4, c_117])).
% 1.75/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.75/1.20  
% 1.75/1.20  Inference rules
% 1.75/1.20  ----------------------
% 1.75/1.20  #Ref     : 0
% 1.75/1.20  #Sup     : 29
% 1.75/1.20  #Fact    : 0
% 1.75/1.20  #Define  : 0
% 1.75/1.20  #Split   : 0
% 1.75/1.20  #Chain   : 0
% 1.75/1.20  #Close   : 0
% 1.75/1.20  
% 1.75/1.20  Ordering : KBO
% 1.75/1.20  
% 1.75/1.20  Simplification rules
% 1.75/1.20  ----------------------
% 1.75/1.20  #Subsume      : 0
% 1.75/1.20  #Demod        : 6
% 1.75/1.20  #Tautology    : 18
% 1.75/1.20  #SimpNegUnit  : 2
% 1.75/1.20  #BackRed      : 1
% 1.75/1.20  
% 1.75/1.20  #Partial instantiations: 0
% 1.75/1.20  #Strategies tried      : 1
% 1.75/1.20  
% 1.75/1.20  Timing (in seconds)
% 1.75/1.20  ----------------------
% 1.75/1.20  Preprocessing        : 0.30
% 1.75/1.20  Parsing              : 0.16
% 1.75/1.20  CNF conversion       : 0.02
% 1.75/1.20  Main loop            : 0.10
% 1.75/1.20  Inferencing          : 0.04
% 1.75/1.20  Reduction            : 0.03
% 1.75/1.20  Demodulation         : 0.02
% 1.75/1.20  BG Simplification    : 0.01
% 1.75/1.20  Subsumption          : 0.01
% 1.75/1.20  Abstraction          : 0.01
% 1.75/1.20  MUC search           : 0.00
% 1.75/1.20  Cooper               : 0.00
% 1.75/1.20  Total                : 0.42
% 1.75/1.20  Index Insertion      : 0.00
% 1.75/1.20  Index Deletion       : 0.00
% 1.75/1.20  Index Matching       : 0.00
% 1.75/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
