%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:44 EST 2020

% Result     : Theorem 1.68s
% Output     : CNFRefutation 1.68s
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
%$ k2_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1

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

tff(f_44,negated_conjecture,(
    ~ ! [A,B] :
        ( A != B
       => k5_xboole_0(k1_tarski(A),k1_tarski(B)) = k2_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(c_16,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(k1_tarski(A_3),k1_tarski(B_4)) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_55,plain,(
    ! [A_18,B_19] :
      ( k4_xboole_0(k1_tarski(A_18),k1_tarski(B_19)) = k1_tarski(A_18)
      | B_19 = A_18 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k4_xboole_0(B_2,A_1)) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_61,plain,(
    ! [B_19,A_18] :
      ( k5_xboole_0(k1_tarski(B_19),k1_tarski(A_18)) = k2_xboole_0(k1_tarski(B_19),k1_tarski(A_18))
      | B_19 = A_18 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_2])).

tff(c_74,plain,(
    ! [B_20,A_21] :
      ( k5_xboole_0(k1_tarski(B_20),k1_tarski(A_21)) = k2_tarski(B_20,A_21)
      | B_20 = A_21 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_61])).

tff(c_14,plain,(
    k5_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_80,plain,(
    '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_14])).

tff(c_88,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_80])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:52:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.68/1.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.68/1.14  
% 1.68/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.68/1.14  %$ k2_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1
% 1.68/1.14  
% 1.68/1.14  %Foreground sorts:
% 1.68/1.14  
% 1.68/1.14  
% 1.68/1.14  %Background operators:
% 1.68/1.14  
% 1.68/1.14  
% 1.68/1.14  %Foreground operators:
% 1.68/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.68/1.14  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.68/1.14  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.68/1.14  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.68/1.14  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.68/1.14  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.68/1.14  tff('#skF_2', type, '#skF_2': $i).
% 1.68/1.14  tff('#skF_1', type, '#skF_1': $i).
% 1.68/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.68/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.68/1.14  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.68/1.14  
% 1.68/1.15  tff(f_44, negated_conjecture, ~(![A, B]: (~(A = B) => (k5_xboole_0(k1_tarski(A), k1_tarski(B)) = k2_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_zfmisc_1)).
% 1.68/1.15  tff(f_29, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 1.68/1.15  tff(f_38, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 1.68/1.15  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 1.68/1.15  tff(c_16, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.68/1.15  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(k1_tarski(A_3), k1_tarski(B_4))=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.68/1.15  tff(c_55, plain, (![A_18, B_19]: (k4_xboole_0(k1_tarski(A_18), k1_tarski(B_19))=k1_tarski(A_18) | B_19=A_18)), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.68/1.15  tff(c_2, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k4_xboole_0(B_2, A_1))=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.68/1.15  tff(c_61, plain, (![B_19, A_18]: (k5_xboole_0(k1_tarski(B_19), k1_tarski(A_18))=k2_xboole_0(k1_tarski(B_19), k1_tarski(A_18)) | B_19=A_18)), inference(superposition, [status(thm), theory('equality')], [c_55, c_2])).
% 1.68/1.15  tff(c_74, plain, (![B_20, A_21]: (k5_xboole_0(k1_tarski(B_20), k1_tarski(A_21))=k2_tarski(B_20, A_21) | B_20=A_21)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_61])).
% 1.68/1.15  tff(c_14, plain, (k5_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.68/1.15  tff(c_80, plain, ('#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_74, c_14])).
% 1.68/1.15  tff(c_88, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16, c_80])).
% 1.68/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.68/1.15  
% 1.68/1.15  Inference rules
% 1.68/1.15  ----------------------
% 1.68/1.15  #Ref     : 0
% 1.68/1.15  #Sup     : 15
% 1.68/1.15  #Fact    : 0
% 1.68/1.15  #Define  : 0
% 1.68/1.15  #Split   : 0
% 1.68/1.15  #Chain   : 0
% 1.68/1.15  #Close   : 0
% 1.68/1.15  
% 1.68/1.15  Ordering : KBO
% 1.68/1.15  
% 1.68/1.15  Simplification rules
% 1.68/1.15  ----------------------
% 1.68/1.15  #Subsume      : 0
% 1.68/1.15  #Demod        : 1
% 1.68/1.15  #Tautology    : 12
% 1.68/1.15  #SimpNegUnit  : 1
% 1.68/1.15  #BackRed      : 0
% 1.68/1.15  
% 1.68/1.15  #Partial instantiations: 0
% 1.68/1.15  #Strategies tried      : 1
% 1.68/1.15  
% 1.68/1.15  Timing (in seconds)
% 1.68/1.15  ----------------------
% 1.73/1.15  Preprocessing        : 0.27
% 1.73/1.15  Parsing              : 0.14
% 1.73/1.15  CNF conversion       : 0.01
% 1.73/1.15  Main loop            : 0.08
% 1.73/1.15  Inferencing          : 0.04
% 1.73/1.15  Reduction            : 0.02
% 1.73/1.15  Demodulation         : 0.02
% 1.73/1.15  BG Simplification    : 0.01
% 1.73/1.15  Subsumption          : 0.01
% 1.73/1.15  Abstraction          : 0.01
% 1.73/1.16  MUC search           : 0.00
% 1.73/1.16  Cooper               : 0.00
% 1.73/1.16  Total                : 0.38
% 1.73/1.16  Index Insertion      : 0.00
% 1.73/1.16  Index Deletion       : 0.00
% 1.73/1.16  Index Matching       : 0.00
% 1.73/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
