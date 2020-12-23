%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:52 EST 2020

% Result     : Theorem 2.46s
% Output     : CNFRefutation 2.46s
% Verified   : 
% Statistics : Number of formulae       :   24 (  25 expanded)
%              Number of leaves         :   15 (  16 expanded)
%              Depth                    :    5
%              Number of atoms          :   16 (  18 expanded)
%              Number of equality atoms :   15 (  17 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_66,negated_conjecture,(
    ~ ! [A,B] :
        ( A != B
       => k4_xboole_0(k2_tarski(A,B),k1_tarski(B)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_zfmisc_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(c_32,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_28,plain,(
    ! [A_23,B_24] :
      ( k4_xboole_0(k1_tarski(A_23),k1_tarski(B_24)) = k1_tarski(A_23)
      | B_24 = A_23 ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_170,plain,(
    ! [A_48,B_49] : k2_xboole_0(k1_tarski(A_48),k1_tarski(B_49)) = k2_tarski(A_48,B_49) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_16,plain,(
    ! [A_13,B_14] : k4_xboole_0(k2_xboole_0(A_13,B_14),B_14) = k4_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_182,plain,(
    ! [A_48,B_49] : k4_xboole_0(k2_tarski(A_48,B_49),k1_tarski(B_49)) = k4_xboole_0(k1_tarski(A_48),k1_tarski(B_49)) ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_16])).

tff(c_30,plain,(
    k4_xboole_0(k2_tarski('#skF_1','#skF_2'),k1_tarski('#skF_2')) != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_620,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) != k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_30])).

tff(c_677,plain,(
    '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_620])).

tff(c_681,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_677])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:57:29 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.46/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.46/1.33  
% 2.46/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.46/1.33  %$ r1_tarski > k2_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1
% 2.46/1.33  
% 2.46/1.33  %Foreground sorts:
% 2.46/1.33  
% 2.46/1.33  
% 2.46/1.33  %Background operators:
% 2.46/1.33  
% 2.46/1.33  
% 2.46/1.33  %Foreground operators:
% 2.46/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.46/1.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.46/1.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.46/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.46/1.33  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.46/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.46/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.46/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.46/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.46/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.46/1.33  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.46/1.33  
% 2.46/1.33  tff(f_66, negated_conjecture, ~(![A, B]: (~(A = B) => (k4_xboole_0(k2_tarski(A, B), k1_tarski(B)) = k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_zfmisc_1)).
% 2.46/1.33  tff(f_60, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.46/1.33  tff(f_51, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 2.46/1.33  tff(f_45, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 2.46/1.33  tff(c_32, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.46/1.33  tff(c_28, plain, (![A_23, B_24]: (k4_xboole_0(k1_tarski(A_23), k1_tarski(B_24))=k1_tarski(A_23) | B_24=A_23)), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.46/1.33  tff(c_170, plain, (![A_48, B_49]: (k2_xboole_0(k1_tarski(A_48), k1_tarski(B_49))=k2_tarski(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.46/1.33  tff(c_16, plain, (![A_13, B_14]: (k4_xboole_0(k2_xboole_0(A_13, B_14), B_14)=k4_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.46/1.33  tff(c_182, plain, (![A_48, B_49]: (k4_xboole_0(k2_tarski(A_48, B_49), k1_tarski(B_49))=k4_xboole_0(k1_tarski(A_48), k1_tarski(B_49)))), inference(superposition, [status(thm), theory('equality')], [c_170, c_16])).
% 2.46/1.33  tff(c_30, plain, (k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), k1_tarski('#skF_2'))!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.46/1.33  tff(c_620, plain, (k4_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))!=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_182, c_30])).
% 2.46/1.33  tff(c_677, plain, ('#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_28, c_620])).
% 2.46/1.33  tff(c_681, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_677])).
% 2.46/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.46/1.33  
% 2.46/1.33  Inference rules
% 2.46/1.33  ----------------------
% 2.46/1.33  #Ref     : 0
% 2.46/1.33  #Sup     : 167
% 2.46/1.33  #Fact    : 0
% 2.46/1.33  #Define  : 0
% 2.46/1.33  #Split   : 0
% 2.46/1.33  #Chain   : 0
% 2.46/1.33  #Close   : 0
% 2.46/1.33  
% 2.46/1.33  Ordering : KBO
% 2.46/1.33  
% 2.46/1.33  Simplification rules
% 2.46/1.33  ----------------------
% 2.46/1.33  #Subsume      : 17
% 2.46/1.33  #Demod        : 55
% 2.46/1.33  #Tautology    : 76
% 2.46/1.33  #SimpNegUnit  : 1
% 2.46/1.34  #BackRed      : 1
% 2.46/1.34  
% 2.46/1.34  #Partial instantiations: 0
% 2.46/1.34  #Strategies tried      : 1
% 2.46/1.34  
% 2.46/1.34  Timing (in seconds)
% 2.46/1.34  ----------------------
% 2.46/1.34  Preprocessing        : 0.28
% 2.46/1.34  Parsing              : 0.14
% 2.46/1.34  CNF conversion       : 0.02
% 2.46/1.34  Main loop            : 0.29
% 2.46/1.34  Inferencing          : 0.10
% 2.46/1.34  Reduction            : 0.11
% 2.46/1.34  Demodulation         : 0.08
% 2.46/1.34  BG Simplification    : 0.02
% 2.46/1.34  Subsumption          : 0.05
% 2.46/1.34  Abstraction          : 0.01
% 2.46/1.34  MUC search           : 0.00
% 2.46/1.34  Cooper               : 0.00
% 2.46/1.34  Total                : 0.59
% 2.46/1.34  Index Insertion      : 0.00
% 2.46/1.34  Index Deletion       : 0.00
% 2.46/1.34  Index Matching       : 0.00
% 2.46/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
