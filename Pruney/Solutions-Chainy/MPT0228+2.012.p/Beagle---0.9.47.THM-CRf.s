%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:53 EST 2020

% Result     : Theorem 1.77s
% Output     : CNFRefutation 1.77s
% Verified   : 
% Statistics : Number of formulae       :   29 (  30 expanded)
%              Number of leaves         :   20 (  21 expanded)
%              Depth                    :    5
%              Number of atoms          :   16 (  18 expanded)
%              Number of equality atoms :   15 (  17 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_54,negated_conjecture,(
    ~ ! [A,B] :
        ( A != B
       => k4_xboole_0(k2_tarski(A,B),k1_tarski(B)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(c_26,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_22,plain,(
    ! [A_34,B_35] :
      ( k4_xboole_0(k1_tarski(A_34),k1_tarski(B_35)) = k1_tarski(A_34)
      | B_35 = A_34 ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_6,plain,(
    ! [A_5,B_6] : k2_xboole_0(k1_tarski(A_5),k1_tarski(B_6)) = k2_tarski(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_55,plain,(
    ! [A_43,B_44] : k4_xboole_0(k2_xboole_0(A_43,B_44),B_44) = k4_xboole_0(A_43,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_67,plain,(
    ! [A_5,B_6] : k4_xboole_0(k2_tarski(A_5,B_6),k1_tarski(B_6)) = k4_xboole_0(k1_tarski(A_5),k1_tarski(B_6)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_55])).

tff(c_24,plain,(
    k4_xboole_0(k2_tarski('#skF_1','#skF_2'),k1_tarski('#skF_2')) != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_155,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) != k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_24])).

tff(c_171,plain,(
    '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_155])).

tff(c_175,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_171])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:54:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.77/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.77/1.21  
% 1.77/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.77/1.21  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1
% 1.77/1.21  
% 1.77/1.21  %Foreground sorts:
% 1.77/1.21  
% 1.77/1.21  
% 1.77/1.21  %Background operators:
% 1.77/1.21  
% 1.77/1.21  
% 1.77/1.21  %Foreground operators:
% 1.77/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.77/1.21  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.77/1.21  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.77/1.21  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.77/1.21  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.77/1.21  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.77/1.21  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.77/1.21  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.77/1.21  tff('#skF_2', type, '#skF_2': $i).
% 1.77/1.21  tff('#skF_1', type, '#skF_1': $i).
% 1.77/1.21  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.77/1.21  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.77/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.77/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.77/1.21  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.77/1.21  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.77/1.21  
% 1.77/1.22  tff(f_54, negated_conjecture, ~(![A, B]: (~(A = B) => (k4_xboole_0(k2_tarski(A, B), k1_tarski(B)) = k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_zfmisc_1)).
% 1.77/1.22  tff(f_48, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 1.77/1.22  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 1.77/1.22  tff(f_27, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 1.77/1.22  tff(c_26, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.77/1.22  tff(c_22, plain, (![A_34, B_35]: (k4_xboole_0(k1_tarski(A_34), k1_tarski(B_35))=k1_tarski(A_34) | B_35=A_34)), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.77/1.22  tff(c_6, plain, (![A_5, B_6]: (k2_xboole_0(k1_tarski(A_5), k1_tarski(B_6))=k2_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.77/1.22  tff(c_55, plain, (![A_43, B_44]: (k4_xboole_0(k2_xboole_0(A_43, B_44), B_44)=k4_xboole_0(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.77/1.22  tff(c_67, plain, (![A_5, B_6]: (k4_xboole_0(k2_tarski(A_5, B_6), k1_tarski(B_6))=k4_xboole_0(k1_tarski(A_5), k1_tarski(B_6)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_55])).
% 1.77/1.22  tff(c_24, plain, (k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), k1_tarski('#skF_2'))!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.77/1.22  tff(c_155, plain, (k4_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))!=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_67, c_24])).
% 1.77/1.22  tff(c_171, plain, ('#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_22, c_155])).
% 1.77/1.22  tff(c_175, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_171])).
% 1.77/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.77/1.22  
% 1.77/1.22  Inference rules
% 1.77/1.22  ----------------------
% 1.77/1.22  #Ref     : 0
% 1.77/1.22  #Sup     : 34
% 1.77/1.22  #Fact    : 0
% 1.77/1.22  #Define  : 0
% 1.77/1.22  #Split   : 0
% 1.77/1.22  #Chain   : 0
% 1.77/1.22  #Close   : 0
% 1.77/1.22  
% 1.77/1.22  Ordering : KBO
% 1.77/1.22  
% 1.77/1.22  Simplification rules
% 1.77/1.22  ----------------------
% 1.77/1.22  #Subsume      : 0
% 1.77/1.22  #Demod        : 7
% 1.77/1.22  #Tautology    : 24
% 1.77/1.22  #SimpNegUnit  : 1
% 1.77/1.22  #BackRed      : 1
% 1.77/1.22  
% 1.77/1.22  #Partial instantiations: 0
% 1.77/1.22  #Strategies tried      : 1
% 1.77/1.22  
% 1.77/1.22  Timing (in seconds)
% 1.77/1.22  ----------------------
% 1.77/1.22  Preprocessing        : 0.30
% 1.77/1.22  Parsing              : 0.17
% 1.77/1.22  CNF conversion       : 0.02
% 1.77/1.22  Main loop            : 0.13
% 1.77/1.22  Inferencing          : 0.05
% 1.77/1.22  Reduction            : 0.04
% 1.77/1.22  Demodulation         : 0.03
% 1.77/1.22  BG Simplification    : 0.01
% 1.77/1.22  Subsumption          : 0.02
% 1.77/1.22  Abstraction          : 0.01
% 1.77/1.22  MUC search           : 0.00
% 1.77/1.22  Cooper               : 0.00
% 1.77/1.22  Total                : 0.45
% 1.77/1.22  Index Insertion      : 0.00
% 1.77/1.22  Index Deletion       : 0.00
% 1.77/1.22  Index Matching       : 0.00
% 1.77/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
