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
% DateTime   : Thu Dec  3 09:47:48 EST 2020

% Result     : Theorem 1.66s
% Output     : CNFRefutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :   29 (  29 expanded)
%              Number of leaves         :   20 (  20 expanded)
%              Depth                    :    5
%              Number of atoms          :   14 (  14 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_35,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_37,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k2_tarski(A,B),k1_tarski(C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_44,negated_conjecture,(
    ~ ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(c_10,plain,(
    ! [A_10] : k2_tarski(A_10,A_10) = k1_tarski(A_10) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_11,B_12] : k1_enumset1(A_11,A_11,B_12) = k2_tarski(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_65,plain,(
    ! [A_32,B_33,C_34] : k2_xboole_0(k2_tarski(A_32,B_33),k1_tarski(C_34)) = k1_enumset1(A_32,B_33,C_34) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(A_3,k2_xboole_0(A_3,B_4)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_81,plain,(
    ! [A_35,B_36,C_37] : r1_tarski(k2_tarski(A_35,B_36),k1_enumset1(A_35,B_36,C_37)) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_4])).

tff(c_84,plain,(
    ! [A_11,B_12] : r1_tarski(k2_tarski(A_11,A_11),k2_tarski(A_11,B_12)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_81])).

tff(c_88,plain,(
    ! [A_11,B_12] : r1_tarski(k1_tarski(A_11),k2_tarski(A_11,B_12)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_84])).

tff(c_18,plain,(
    ~ r1_tarski(k1_tarski('#skF_1'),k2_tarski('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_101,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_18])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 10:21:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.66/1.10  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.66/1.11  
% 1.66/1.11  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.66/1.11  %$ r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1
% 1.66/1.11  
% 1.66/1.11  %Foreground sorts:
% 1.66/1.11  
% 1.66/1.11  
% 1.66/1.11  %Background operators:
% 1.66/1.11  
% 1.66/1.11  
% 1.66/1.11  %Foreground operators:
% 1.66/1.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.66/1.11  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.66/1.11  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.66/1.11  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.66/1.11  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.66/1.11  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.66/1.11  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.66/1.11  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.66/1.11  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.66/1.11  tff('#skF_2', type, '#skF_2': $i).
% 1.66/1.11  tff('#skF_1', type, '#skF_1': $i).
% 1.66/1.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.66/1.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.66/1.11  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.66/1.11  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.66/1.11  
% 1.66/1.12  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.66/1.12  tff(f_37, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 1.66/1.12  tff(f_33, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k2_tarski(A, B), k1_tarski(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_enumset1)).
% 1.66/1.12  tff(f_29, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.66/1.12  tff(f_44, negated_conjecture, ~(![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 1.66/1.12  tff(c_10, plain, (![A_10]: (k2_tarski(A_10, A_10)=k1_tarski(A_10))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.66/1.12  tff(c_12, plain, (![A_11, B_12]: (k1_enumset1(A_11, A_11, B_12)=k2_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.66/1.12  tff(c_65, plain, (![A_32, B_33, C_34]: (k2_xboole_0(k2_tarski(A_32, B_33), k1_tarski(C_34))=k1_enumset1(A_32, B_33, C_34))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.66/1.12  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(A_3, k2_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.66/1.12  tff(c_81, plain, (![A_35, B_36, C_37]: (r1_tarski(k2_tarski(A_35, B_36), k1_enumset1(A_35, B_36, C_37)))), inference(superposition, [status(thm), theory('equality')], [c_65, c_4])).
% 1.66/1.12  tff(c_84, plain, (![A_11, B_12]: (r1_tarski(k2_tarski(A_11, A_11), k2_tarski(A_11, B_12)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_81])).
% 1.66/1.12  tff(c_88, plain, (![A_11, B_12]: (r1_tarski(k1_tarski(A_11), k2_tarski(A_11, B_12)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_84])).
% 1.66/1.12  tff(c_18, plain, (~r1_tarski(k1_tarski('#skF_1'), k2_tarski('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.66/1.12  tff(c_101, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_88, c_18])).
% 1.66/1.12  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.66/1.12  
% 1.66/1.12  Inference rules
% 1.66/1.12  ----------------------
% 1.66/1.12  #Ref     : 0
% 1.66/1.12  #Sup     : 18
% 1.66/1.12  #Fact    : 0
% 1.66/1.12  #Define  : 0
% 1.66/1.12  #Split   : 0
% 1.66/1.12  #Chain   : 0
% 1.66/1.12  #Close   : 0
% 1.66/1.12  
% 1.66/1.12  Ordering : KBO
% 1.66/1.12  
% 1.66/1.12  Simplification rules
% 1.66/1.12  ----------------------
% 1.66/1.12  #Subsume      : 0
% 1.66/1.12  #Demod        : 4
% 1.66/1.12  #Tautology    : 14
% 1.66/1.12  #SimpNegUnit  : 0
% 1.66/1.12  #BackRed      : 1
% 1.66/1.12  
% 1.66/1.12  #Partial instantiations: 0
% 1.66/1.12  #Strategies tried      : 1
% 1.66/1.12  
% 1.66/1.12  Timing (in seconds)
% 1.66/1.12  ----------------------
% 1.66/1.12  Preprocessing        : 0.28
% 1.66/1.12  Parsing              : 0.15
% 1.66/1.12  CNF conversion       : 0.01
% 1.66/1.12  Main loop            : 0.09
% 1.66/1.12  Inferencing          : 0.04
% 1.66/1.12  Reduction            : 0.03
% 1.66/1.12  Demodulation         : 0.02
% 1.66/1.12  BG Simplification    : 0.01
% 1.66/1.12  Subsumption          : 0.01
% 1.66/1.12  Abstraction          : 0.01
% 1.66/1.12  MUC search           : 0.00
% 1.66/1.12  Cooper               : 0.00
% 1.66/1.12  Total                : 0.38
% 1.66/1.12  Index Insertion      : 0.00
% 1.66/1.12  Index Deletion       : 0.00
% 1.66/1.12  Index Matching       : 0.00
% 1.66/1.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
