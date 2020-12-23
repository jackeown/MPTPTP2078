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
% DateTime   : Thu Dec  3 09:48:53 EST 2020

% Result     : Theorem 1.62s
% Output     : CNFRefutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :   24 (  25 expanded)
%              Number of leaves         :   15 (  16 expanded)
%              Depth                    :    5
%              Number of atoms          :   20 (  22 expanded)
%              Number of equality atoms :   14 (  16 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k2_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_46,negated_conjecture,(
    ~ ! [A,B] :
        ( A != B
       => k4_xboole_0(k2_tarski(A,B),k1_tarski(B)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_zfmisc_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( A != B
     => r1_xboole_0(k1_tarski(A),k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => k4_xboole_0(k2_xboole_0(A,B),B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_xboole_1)).

tff(c_14,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( r1_xboole_0(k1_tarski(A_8),k1_tarski(B_9))
      | B_9 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(k1_tarski(A_3),k1_tarski(B_4)) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_43,plain,(
    ! [A_17,B_18] :
      ( k4_xboole_0(k2_xboole_0(A_17,B_18),B_18) = A_17
      | ~ r1_xboole_0(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_55,plain,(
    ! [A_19,B_20] :
      ( k4_xboole_0(k2_tarski(A_19,B_20),k1_tarski(B_20)) = k1_tarski(A_19)
      | ~ r1_xboole_0(k1_tarski(A_19),k1_tarski(B_20)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_43])).

tff(c_60,plain,(
    ! [A_21,B_22] :
      ( k4_xboole_0(k2_tarski(A_21,B_22),k1_tarski(B_22)) = k1_tarski(A_21)
      | B_22 = A_21 ) ),
    inference(resolution,[status(thm)],[c_10,c_55])).

tff(c_12,plain,(
    k4_xboole_0(k2_tarski('#skF_1','#skF_2'),k1_tarski('#skF_2')) != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_66,plain,(
    '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_12])).

tff(c_77,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_66])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:13:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.62/1.09  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.62/1.10  
% 1.62/1.10  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.62/1.10  %$ r1_xboole_0 > k2_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1
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
% 1.62/1.10  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.62/1.10  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.62/1.10  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.62/1.10  tff('#skF_2', type, '#skF_2': $i).
% 1.62/1.10  tff('#skF_1', type, '#skF_1': $i).
% 1.62/1.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.62/1.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.62/1.10  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.62/1.10  
% 1.62/1.10  tff(f_46, negated_conjecture, ~(![A, B]: (~(A = B) => (k4_xboole_0(k2_tarski(A, B), k1_tarski(B)) = k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_zfmisc_1)).
% 1.62/1.10  tff(f_40, axiom, (![A, B]: (~(A = B) => r1_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 1.62/1.10  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 1.62/1.10  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => (k4_xboole_0(k2_xboole_0(A, B), B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_xboole_1)).
% 1.62/1.10  tff(c_14, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.62/1.10  tff(c_10, plain, (![A_8, B_9]: (r1_xboole_0(k1_tarski(A_8), k1_tarski(B_9)) | B_9=A_8)), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.62/1.10  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(k1_tarski(A_3), k1_tarski(B_4))=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.62/1.10  tff(c_43, plain, (![A_17, B_18]: (k4_xboole_0(k2_xboole_0(A_17, B_18), B_18)=A_17 | ~r1_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.62/1.10  tff(c_55, plain, (![A_19, B_20]: (k4_xboole_0(k2_tarski(A_19, B_20), k1_tarski(B_20))=k1_tarski(A_19) | ~r1_xboole_0(k1_tarski(A_19), k1_tarski(B_20)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_43])).
% 1.62/1.10  tff(c_60, plain, (![A_21, B_22]: (k4_xboole_0(k2_tarski(A_21, B_22), k1_tarski(B_22))=k1_tarski(A_21) | B_22=A_21)), inference(resolution, [status(thm)], [c_10, c_55])).
% 1.62/1.10  tff(c_12, plain, (k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), k1_tarski('#skF_2'))!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.62/1.10  tff(c_66, plain, ('#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_60, c_12])).
% 1.62/1.10  tff(c_77, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14, c_66])).
% 1.62/1.10  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.62/1.10  
% 1.62/1.10  Inference rules
% 1.62/1.10  ----------------------
% 1.62/1.10  #Ref     : 0
% 1.62/1.11  #Sup     : 14
% 1.62/1.11  #Fact    : 0
% 1.62/1.11  #Define  : 0
% 1.62/1.11  #Split   : 0
% 1.62/1.11  #Chain   : 0
% 1.62/1.11  #Close   : 0
% 1.62/1.11  
% 1.62/1.11  Ordering : KBO
% 1.62/1.11  
% 1.62/1.11  Simplification rules
% 1.62/1.11  ----------------------
% 1.62/1.11  #Subsume      : 0
% 1.62/1.11  #Demod        : 0
% 1.62/1.11  #Tautology    : 9
% 1.62/1.11  #SimpNegUnit  : 1
% 1.62/1.11  #BackRed      : 0
% 1.62/1.11  
% 1.62/1.11  #Partial instantiations: 0
% 1.62/1.11  #Strategies tried      : 1
% 1.62/1.11  
% 1.62/1.11  Timing (in seconds)
% 1.62/1.11  ----------------------
% 1.62/1.11  Preprocessing        : 0.27
% 1.62/1.11  Parsing              : 0.14
% 1.62/1.11  CNF conversion       : 0.01
% 1.62/1.11  Main loop            : 0.09
% 1.62/1.11  Inferencing          : 0.04
% 1.62/1.11  Reduction            : 0.02
% 1.62/1.11  Demodulation         : 0.01
% 1.62/1.11  BG Simplification    : 0.01
% 1.62/1.11  Subsumption          : 0.01
% 1.62/1.11  Abstraction          : 0.00
% 1.62/1.11  MUC search           : 0.00
% 1.62/1.11  Cooper               : 0.00
% 1.62/1.11  Total                : 0.38
% 1.62/1.11  Index Insertion      : 0.00
% 1.62/1.11  Index Deletion       : 0.00
% 1.62/1.11  Index Matching       : 0.00
% 1.62/1.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
