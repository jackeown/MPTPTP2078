%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:42 EST 2020

% Result     : Theorem 1.77s
% Output     : CNFRefutation 1.77s
% Verified   : 
% Statistics : Number of formulae       :   24 (  25 expanded)
%              Number of leaves         :   15 (  16 expanded)
%              Depth                    :    5
%              Number of atoms          :   18 (  20 expanded)
%              Number of equality atoms :   17 (  19 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_46,negated_conjecture,(
    ~ ! [A,B] :
        ( A != B
       => k5_xboole_0(k1_tarski(A),k1_tarski(B)) = k2_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(c_18,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_10,plain,(
    ! [A_8,B_9] : k2_xboole_0(k1_tarski(A_8),k1_tarski(B_9)) = k2_tarski(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_183,plain,(
    ! [A_24,B_25] :
      ( k4_xboole_0(k1_tarski(A_24),k1_tarski(B_25)) = k1_tarski(A_24)
      | B_25 = A_24 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_8,plain,(
    ! [A_6,B_7] : k5_xboole_0(A_6,k4_xboole_0(B_7,A_6)) = k2_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_189,plain,(
    ! [B_25,A_24] :
      ( k5_xboole_0(k1_tarski(B_25),k1_tarski(A_24)) = k2_xboole_0(k1_tarski(B_25),k1_tarski(A_24))
      | B_25 = A_24 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_8])).

tff(c_203,plain,(
    ! [B_26,A_27] :
      ( k5_xboole_0(k1_tarski(B_26),k1_tarski(A_27)) = k2_tarski(B_26,A_27)
      | B_26 = A_27 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_189])).

tff(c_16,plain,(
    k5_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_209,plain,(
    '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_203,c_16])).

tff(c_229,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_209])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:57:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.77/1.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.77/1.16  
% 1.77/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.77/1.16  %$ k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 1.77/1.16  
% 1.77/1.16  %Foreground sorts:
% 1.77/1.16  
% 1.77/1.16  
% 1.77/1.16  %Background operators:
% 1.77/1.16  
% 1.77/1.16  
% 1.77/1.16  %Foreground operators:
% 1.77/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.77/1.16  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.77/1.16  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.77/1.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.77/1.16  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.77/1.16  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.77/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.77/1.16  tff('#skF_1', type, '#skF_1': $i).
% 1.77/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.77/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.77/1.16  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.77/1.16  
% 1.77/1.17  tff(f_46, negated_conjecture, ~(![A, B]: (~(A = B) => (k5_xboole_0(k1_tarski(A), k1_tarski(B)) = k2_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_zfmisc_1)).
% 1.77/1.17  tff(f_35, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 1.77/1.17  tff(f_40, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 1.77/1.17  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 1.77/1.17  tff(c_18, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.77/1.17  tff(c_10, plain, (![A_8, B_9]: (k2_xboole_0(k1_tarski(A_8), k1_tarski(B_9))=k2_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.77/1.17  tff(c_183, plain, (![A_24, B_25]: (k4_xboole_0(k1_tarski(A_24), k1_tarski(B_25))=k1_tarski(A_24) | B_25=A_24)), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.77/1.17  tff(c_8, plain, (![A_6, B_7]: (k5_xboole_0(A_6, k4_xboole_0(B_7, A_6))=k2_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.77/1.17  tff(c_189, plain, (![B_25, A_24]: (k5_xboole_0(k1_tarski(B_25), k1_tarski(A_24))=k2_xboole_0(k1_tarski(B_25), k1_tarski(A_24)) | B_25=A_24)), inference(superposition, [status(thm), theory('equality')], [c_183, c_8])).
% 1.77/1.17  tff(c_203, plain, (![B_26, A_27]: (k5_xboole_0(k1_tarski(B_26), k1_tarski(A_27))=k2_tarski(B_26, A_27) | B_26=A_27)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_189])).
% 1.77/1.17  tff(c_16, plain, (k5_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.77/1.17  tff(c_209, plain, ('#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_203, c_16])).
% 1.77/1.17  tff(c_229, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_209])).
% 1.77/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.77/1.17  
% 1.77/1.17  Inference rules
% 1.77/1.17  ----------------------
% 1.77/1.17  #Ref     : 0
% 1.77/1.17  #Sup     : 48
% 1.77/1.17  #Fact    : 0
% 1.77/1.17  #Define  : 0
% 1.77/1.17  #Split   : 0
% 1.77/1.17  #Chain   : 0
% 1.77/1.17  #Close   : 0
% 1.77/1.17  
% 1.77/1.17  Ordering : KBO
% 1.77/1.17  
% 1.77/1.17  Simplification rules
% 1.77/1.17  ----------------------
% 1.77/1.17  #Subsume      : 0
% 1.77/1.17  #Demod        : 11
% 1.77/1.17  #Tautology    : 38
% 1.77/1.17  #SimpNegUnit  : 1
% 1.77/1.17  #BackRed      : 0
% 1.77/1.17  
% 1.77/1.17  #Partial instantiations: 0
% 1.77/1.17  #Strategies tried      : 1
% 1.77/1.17  
% 1.77/1.17  Timing (in seconds)
% 1.77/1.17  ----------------------
% 1.77/1.17  Preprocessing        : 0.28
% 1.77/1.17  Parsing              : 0.15
% 1.77/1.17  CNF conversion       : 0.02
% 1.77/1.17  Main loop            : 0.14
% 1.77/1.17  Inferencing          : 0.06
% 1.77/1.17  Reduction            : 0.04
% 1.77/1.17  Demodulation         : 0.03
% 1.77/1.17  BG Simplification    : 0.01
% 1.77/1.17  Subsumption          : 0.02
% 1.77/1.17  Abstraction          : 0.01
% 1.77/1.17  MUC search           : 0.00
% 1.77/1.17  Cooper               : 0.00
% 1.77/1.17  Total                : 0.44
% 1.77/1.17  Index Insertion      : 0.00
% 1.77/1.18  Index Deletion       : 0.00
% 1.77/1.18  Index Matching       : 0.00
% 1.77/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
