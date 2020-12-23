%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:48 EST 2020

% Result     : Theorem 1.69s
% Output     : CNFRefutation 1.69s
% Verified   : 
% Statistics : Number of formulae       :   27 (  28 expanded)
%              Number of leaves         :   18 (  19 expanded)
%              Depth                    :    5
%              Number of atoms          :   16 (  18 expanded)
%              Number of equality atoms :   15 (  17 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_46,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_xboole_0
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_zfmisc_1)).

tff(f_29,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( k2_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_zfmisc_1)).

tff(c_16,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_4,plain,(
    ! [A_3] : k5_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_18,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_59,plain,(
    ! [A_20,B_21] : k5_xboole_0(A_20,k4_xboole_0(B_21,A_20)) = k2_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_68,plain,(
    k2_xboole_0(k1_tarski('#skF_2'),k1_tarski('#skF_1')) = k5_xboole_0(k1_tarski('#skF_2'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_59])).

tff(c_71,plain,(
    k2_xboole_0(k1_tarski('#skF_2'),k1_tarski('#skF_1')) = k1_tarski('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_68])).

tff(c_85,plain,(
    ! [B_25,A_26] :
      ( B_25 = A_26
      | k2_xboole_0(k1_tarski(A_26),k1_tarski(B_25)) != k1_tarski(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_88,plain,(
    '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_85])).

tff(c_92,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_88])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:43:30 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.69/1.09  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.69/1.09  
% 1.69/1.09  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.69/1.09  %$ k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 1.69/1.09  
% 1.69/1.09  %Foreground sorts:
% 1.69/1.09  
% 1.69/1.09  
% 1.69/1.09  %Background operators:
% 1.69/1.09  
% 1.69/1.09  
% 1.69/1.09  %Foreground operators:
% 1.69/1.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.69/1.09  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.69/1.09  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.69/1.09  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.69/1.09  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.69/1.09  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.69/1.09  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.69/1.09  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.69/1.09  tff('#skF_2', type, '#skF_2': $i).
% 1.69/1.09  tff('#skF_1', type, '#skF_1': $i).
% 1.69/1.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.69/1.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.69/1.09  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.69/1.09  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.69/1.10  
% 1.69/1.10  tff(f_46, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_xboole_0) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_zfmisc_1)).
% 1.69/1.10  tff(f_29, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 1.69/1.10  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 1.69/1.10  tff(f_41, axiom, (![A, B]: ((k2_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_zfmisc_1)).
% 1.69/1.10  tff(c_16, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.69/1.10  tff(c_4, plain, (![A_3]: (k5_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.69/1.10  tff(c_18, plain, (k4_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.69/1.10  tff(c_59, plain, (![A_20, B_21]: (k5_xboole_0(A_20, k4_xboole_0(B_21, A_20))=k2_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.69/1.10  tff(c_68, plain, (k2_xboole_0(k1_tarski('#skF_2'), k1_tarski('#skF_1'))=k5_xboole_0(k1_tarski('#skF_2'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_18, c_59])).
% 1.69/1.10  tff(c_71, plain, (k2_xboole_0(k1_tarski('#skF_2'), k1_tarski('#skF_1'))=k1_tarski('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_68])).
% 1.69/1.10  tff(c_85, plain, (![B_25, A_26]: (B_25=A_26 | k2_xboole_0(k1_tarski(A_26), k1_tarski(B_25))!=k1_tarski(A_26))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.69/1.10  tff(c_88, plain, ('#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_71, c_85])).
% 1.69/1.10  tff(c_92, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16, c_88])).
% 1.69/1.10  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.69/1.10  
% 1.69/1.10  Inference rules
% 1.69/1.10  ----------------------
% 1.69/1.10  #Ref     : 0
% 1.69/1.10  #Sup     : 18
% 1.69/1.10  #Fact    : 0
% 1.69/1.10  #Define  : 0
% 1.69/1.10  #Split   : 0
% 1.69/1.10  #Chain   : 0
% 1.69/1.10  #Close   : 0
% 1.69/1.10  
% 1.69/1.10  Ordering : KBO
% 1.69/1.10  
% 1.69/1.10  Simplification rules
% 1.69/1.10  ----------------------
% 1.69/1.10  #Subsume      : 0
% 1.69/1.10  #Demod        : 1
% 1.69/1.10  #Tautology    : 16
% 1.69/1.10  #SimpNegUnit  : 1
% 1.69/1.10  #BackRed      : 0
% 1.69/1.10  
% 1.69/1.10  #Partial instantiations: 0
% 1.69/1.10  #Strategies tried      : 1
% 1.69/1.10  
% 1.69/1.10  Timing (in seconds)
% 1.69/1.10  ----------------------
% 1.69/1.10  Preprocessing        : 0.27
% 1.69/1.10  Parsing              : 0.15
% 1.69/1.11  CNF conversion       : 0.01
% 1.69/1.11  Main loop            : 0.09
% 1.69/1.11  Inferencing          : 0.04
% 1.69/1.11  Reduction            : 0.03
% 1.69/1.11  Demodulation         : 0.02
% 1.69/1.11  BG Simplification    : 0.01
% 1.69/1.11  Subsumption          : 0.01
% 1.69/1.11  Abstraction          : 0.01
% 1.69/1.11  MUC search           : 0.00
% 1.69/1.11  Cooper               : 0.00
% 1.69/1.11  Total                : 0.38
% 1.69/1.11  Index Insertion      : 0.00
% 1.69/1.11  Index Deletion       : 0.00
% 1.69/1.11  Index Matching       : 0.00
% 1.69/1.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
