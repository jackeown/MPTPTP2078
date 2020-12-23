%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:43 EST 2020

% Result     : Theorem 1.65s
% Output     : CNFRefutation 1.77s
% Verified   : 
% Statistics : Number of formulae       :   37 (  38 expanded)
%              Number of leaves         :   22 (  23 expanded)
%              Depth                    :    8
%              Number of atoms          :   32 (  34 expanded)
%              Number of equality atoms :   27 (  29 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_54,negated_conjecture,(
    ~ ! [A,B] :
        ( A != B
       => k5_xboole_0(k1_tarski(A),k1_tarski(B)) = k2_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_33,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_48,axiom,(
    ! [A,B] :
      ( A != B
     => r1_xboole_0(k1_tarski(A),k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(c_24,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_12,plain,(
    ! [A_8,B_9] : k2_xboole_0(k1_tarski(A_8),k1_tarski(B_9)) = k2_tarski(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_8,plain,(
    ! [A_5] : k5_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_58,plain,(
    ! [A_26,B_27] :
      ( r1_xboole_0(k1_tarski(A_26),k1_tarski(B_27))
      | B_27 = A_26 ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_92,plain,(
    ! [A_34,B_35] :
      ( k3_xboole_0(k1_tarski(A_34),k1_tarski(B_35)) = k1_xboole_0
      | B_35 = A_34 ) ),
    inference(resolution,[status(thm)],[c_58,c_2])).

tff(c_6,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_98,plain,(
    ! [A_34,B_35] :
      ( k4_xboole_0(k1_tarski(A_34),k1_tarski(B_35)) = k5_xboole_0(k1_tarski(A_34),k1_xboole_0)
      | B_35 = A_34 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_6])).

tff(c_115,plain,(
    ! [A_39,B_40] :
      ( k4_xboole_0(k1_tarski(A_39),k1_tarski(B_40)) = k1_tarski(A_39)
      | B_40 = A_39 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_98])).

tff(c_10,plain,(
    ! [A_6,B_7] : k5_xboole_0(A_6,k4_xboole_0(B_7,A_6)) = k2_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_121,plain,(
    ! [B_40,A_39] :
      ( k5_xboole_0(k1_tarski(B_40),k1_tarski(A_39)) = k2_xboole_0(k1_tarski(B_40),k1_tarski(A_39))
      | B_40 = A_39 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_10])).

tff(c_128,plain,(
    ! [B_41,A_42] :
      ( k5_xboole_0(k1_tarski(B_41),k1_tarski(A_42)) = k2_tarski(B_41,A_42)
      | B_41 = A_42 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_121])).

tff(c_22,plain,(
    k5_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_134,plain,(
    '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_22])).

tff(c_142,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_134])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:26:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.65/1.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.77/1.13  
% 1.77/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.77/1.13  %$ r1_xboole_0 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 1.77/1.13  
% 1.77/1.13  %Foreground sorts:
% 1.77/1.13  
% 1.77/1.13  
% 1.77/1.13  %Background operators:
% 1.77/1.13  
% 1.77/1.13  
% 1.77/1.13  %Foreground operators:
% 1.77/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.77/1.13  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.77/1.13  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.77/1.13  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.77/1.13  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.77/1.13  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.77/1.13  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.77/1.13  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.77/1.13  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.77/1.13  tff('#skF_2', type, '#skF_2': $i).
% 1.77/1.13  tff('#skF_1', type, '#skF_1': $i).
% 1.77/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.77/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.77/1.13  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.77/1.13  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.77/1.13  
% 1.77/1.14  tff(f_54, negated_conjecture, ~(![A, B]: (~(A = B) => (k5_xboole_0(k1_tarski(A), k1_tarski(B)) = k2_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_zfmisc_1)).
% 1.77/1.14  tff(f_37, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 1.77/1.14  tff(f_33, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 1.77/1.14  tff(f_48, axiom, (![A, B]: (~(A = B) => r1_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 1.77/1.14  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 1.77/1.14  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 1.77/1.14  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 1.77/1.14  tff(c_24, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.77/1.14  tff(c_12, plain, (![A_8, B_9]: (k2_xboole_0(k1_tarski(A_8), k1_tarski(B_9))=k2_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.77/1.14  tff(c_8, plain, (![A_5]: (k5_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.77/1.14  tff(c_58, plain, (![A_26, B_27]: (r1_xboole_0(k1_tarski(A_26), k1_tarski(B_27)) | B_27=A_26)), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.77/1.14  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.77/1.14  tff(c_92, plain, (![A_34, B_35]: (k3_xboole_0(k1_tarski(A_34), k1_tarski(B_35))=k1_xboole_0 | B_35=A_34)), inference(resolution, [status(thm)], [c_58, c_2])).
% 1.77/1.14  tff(c_6, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.77/1.14  tff(c_98, plain, (![A_34, B_35]: (k4_xboole_0(k1_tarski(A_34), k1_tarski(B_35))=k5_xboole_0(k1_tarski(A_34), k1_xboole_0) | B_35=A_34)), inference(superposition, [status(thm), theory('equality')], [c_92, c_6])).
% 1.77/1.14  tff(c_115, plain, (![A_39, B_40]: (k4_xboole_0(k1_tarski(A_39), k1_tarski(B_40))=k1_tarski(A_39) | B_40=A_39)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_98])).
% 1.77/1.14  tff(c_10, plain, (![A_6, B_7]: (k5_xboole_0(A_6, k4_xboole_0(B_7, A_6))=k2_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.77/1.14  tff(c_121, plain, (![B_40, A_39]: (k5_xboole_0(k1_tarski(B_40), k1_tarski(A_39))=k2_xboole_0(k1_tarski(B_40), k1_tarski(A_39)) | B_40=A_39)), inference(superposition, [status(thm), theory('equality')], [c_115, c_10])).
% 1.77/1.14  tff(c_128, plain, (![B_41, A_42]: (k5_xboole_0(k1_tarski(B_41), k1_tarski(A_42))=k2_tarski(B_41, A_42) | B_41=A_42)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_121])).
% 1.77/1.14  tff(c_22, plain, (k5_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.77/1.14  tff(c_134, plain, ('#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_128, c_22])).
% 1.77/1.14  tff(c_142, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_134])).
% 1.77/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.77/1.14  
% 1.77/1.14  Inference rules
% 1.77/1.14  ----------------------
% 1.77/1.14  #Ref     : 0
% 1.77/1.14  #Sup     : 25
% 1.77/1.14  #Fact    : 0
% 1.77/1.14  #Define  : 0
% 1.77/1.14  #Split   : 0
% 1.77/1.14  #Chain   : 0
% 1.77/1.14  #Close   : 0
% 1.77/1.14  
% 1.77/1.14  Ordering : KBO
% 1.77/1.14  
% 1.77/1.14  Simplification rules
% 1.77/1.14  ----------------------
% 1.77/1.14  #Subsume      : 0
% 1.77/1.14  #Demod        : 2
% 1.77/1.14  #Tautology    : 20
% 1.77/1.14  #SimpNegUnit  : 1
% 1.77/1.14  #BackRed      : 0
% 1.77/1.14  
% 1.77/1.14  #Partial instantiations: 0
% 1.77/1.14  #Strategies tried      : 1
% 1.77/1.14  
% 1.77/1.14  Timing (in seconds)
% 1.77/1.14  ----------------------
% 1.77/1.15  Preprocessing        : 0.28
% 1.77/1.15  Parsing              : 0.15
% 1.77/1.15  CNF conversion       : 0.01
% 1.77/1.15  Main loop            : 0.11
% 1.77/1.15  Inferencing          : 0.05
% 1.77/1.15  Reduction            : 0.03
% 1.77/1.15  Demodulation         : 0.02
% 1.77/1.15  BG Simplification    : 0.01
% 1.77/1.15  Subsumption          : 0.01
% 1.77/1.15  Abstraction          : 0.01
% 1.77/1.15  MUC search           : 0.00
% 1.77/1.15  Cooper               : 0.00
% 1.77/1.15  Total                : 0.41
% 1.77/1.15  Index Insertion      : 0.00
% 1.77/1.15  Index Deletion       : 0.00
% 1.77/1.15  Index Matching       : 0.00
% 1.77/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
