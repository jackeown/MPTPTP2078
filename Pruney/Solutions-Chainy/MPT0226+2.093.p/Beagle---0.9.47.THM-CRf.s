%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:49 EST 2020

% Result     : Theorem 1.62s
% Output     : CNFRefutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :   23 (  26 expanded)
%              Number of leaves         :   13 (  15 expanded)
%              Depth                    :    6
%              Number of atoms          :   21 (  26 expanded)
%              Number of equality atoms :   20 (  25 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_27,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_41,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_xboole_0
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_zfmisc_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_zfmisc_1)).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_28,plain,(
    ! [A_8,B_9] :
      ( k4_xboole_0(k1_tarski(A_8),k1_tarski(B_9)) = k1_tarski(A_8)
      | B_9 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_12,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_38,plain,
    ( k1_tarski('#skF_1') = k1_xboole_0
    | '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_12])).

tff(c_48,plain,(
    k1_tarski('#skF_1') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_38])).

tff(c_4,plain,(
    ! [B_3,A_2] :
      ( B_3 = A_2
      | k2_xboole_0(k1_tarski(A_2),k1_tarski(B_3)) != k1_tarski(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_59,plain,(
    ! [A_2] :
      ( A_2 = '#skF_1'
      | k2_xboole_0(k1_tarski(A_2),k1_xboole_0) != k1_tarski(A_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_4])).

tff(c_81,plain,(
    ! [A_12] : A_12 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_59])).

tff(c_109,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:19:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.62/1.09  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.62/1.10  
% 1.62/1.10  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.62/1.10  %$ k4_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 1.62/1.10  
% 1.62/1.10  %Foreground sorts:
% 1.62/1.10  
% 1.62/1.10  
% 1.62/1.10  %Background operators:
% 1.62/1.10  
% 1.62/1.10  
% 1.62/1.10  %Foreground operators:
% 1.62/1.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.62/1.10  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.62/1.10  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.62/1.10  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.62/1.10  tff('#skF_2', type, '#skF_2': $i).
% 1.62/1.10  tff('#skF_1', type, '#skF_1': $i).
% 1.62/1.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.62/1.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.62/1.10  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.62/1.10  
% 1.62/1.10  tff(f_27, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 1.62/1.10  tff(f_41, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_xboole_0) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_zfmisc_1)).
% 1.62/1.10  tff(f_36, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 1.62/1.10  tff(f_31, axiom, (![A, B]: ((k2_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_zfmisc_1)).
% 1.62/1.10  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, k1_xboole_0)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.62/1.10  tff(c_10, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.62/1.10  tff(c_28, plain, (![A_8, B_9]: (k4_xboole_0(k1_tarski(A_8), k1_tarski(B_9))=k1_tarski(A_8) | B_9=A_8)), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.62/1.10  tff(c_12, plain, (k4_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.62/1.10  tff(c_38, plain, (k1_tarski('#skF_1')=k1_xboole_0 | '#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_28, c_12])).
% 1.62/1.10  tff(c_48, plain, (k1_tarski('#skF_1')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_10, c_38])).
% 1.62/1.10  tff(c_4, plain, (![B_3, A_2]: (B_3=A_2 | k2_xboole_0(k1_tarski(A_2), k1_tarski(B_3))!=k1_tarski(A_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.62/1.10  tff(c_59, plain, (![A_2]: (A_2='#skF_1' | k2_xboole_0(k1_tarski(A_2), k1_xboole_0)!=k1_tarski(A_2))), inference(superposition, [status(thm), theory('equality')], [c_48, c_4])).
% 1.62/1.10  tff(c_81, plain, (![A_12]: (A_12='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_59])).
% 1.62/1.10  tff(c_109, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_81, c_10])).
% 1.62/1.10  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.62/1.10  
% 1.62/1.10  Inference rules
% 1.62/1.10  ----------------------
% 1.62/1.10  #Ref     : 0
% 1.62/1.10  #Sup     : 30
% 1.62/1.10  #Fact    : 0
% 1.62/1.10  #Define  : 0
% 1.62/1.10  #Split   : 0
% 1.62/1.10  #Chain   : 0
% 1.62/1.10  #Close   : 0
% 1.62/1.10  
% 1.62/1.10  Ordering : KBO
% 1.62/1.10  
% 1.62/1.10  Simplification rules
% 1.62/1.10  ----------------------
% 1.62/1.10  #Subsume      : 3
% 1.62/1.11  #Demod        : 8
% 1.62/1.11  #Tautology    : 9
% 1.62/1.11  #SimpNegUnit  : 2
% 1.62/1.11  #BackRed      : 1
% 1.62/1.11  
% 1.62/1.11  #Partial instantiations: 0
% 1.62/1.11  #Strategies tried      : 1
% 1.62/1.11  
% 1.62/1.11  Timing (in seconds)
% 1.62/1.11  ----------------------
% 1.62/1.11  Preprocessing        : 0.26
% 1.62/1.11  Parsing              : 0.13
% 1.62/1.11  CNF conversion       : 0.01
% 1.62/1.11  Main loop            : 0.10
% 1.62/1.11  Inferencing          : 0.04
% 1.62/1.11  Reduction            : 0.03
% 1.62/1.11  Demodulation         : 0.02
% 1.62/1.11  BG Simplification    : 0.01
% 1.62/1.11  Subsumption          : 0.01
% 1.62/1.11  Abstraction          : 0.01
% 1.62/1.11  MUC search           : 0.00
% 1.62/1.11  Cooper               : 0.00
% 1.62/1.11  Total                : 0.38
% 1.62/1.11  Index Insertion      : 0.00
% 1.62/1.11  Index Deletion       : 0.00
% 1.62/1.11  Index Matching       : 0.00
% 1.62/1.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
