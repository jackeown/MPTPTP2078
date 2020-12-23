%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:49 EST 2020

% Result     : Theorem 1.69s
% Output     : CNFRefutation 1.69s
% Verified   : 
% Statistics : Number of formulae       :   22 (  22 expanded)
%              Number of leaves         :   15 (  15 expanded)
%              Depth                    :    4
%              Number of atoms          :   11 (  11 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_33,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_38,negated_conjecture,(
    ~ ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(c_8,plain,(
    ! [A_7,B_8] : k1_enumset1(A_7,A_7,B_8) = k2_tarski(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_41,plain,(
    ! [A_20,B_21,C_22] : k2_xboole_0(k1_tarski(A_20),k2_tarski(B_21,C_22)) = k1_enumset1(A_20,B_21,C_22) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(A_1,k2_xboole_0(A_1,B_2)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_56,plain,(
    ! [A_23,B_24,C_25] : r1_tarski(k1_tarski(A_23),k1_enumset1(A_23,B_24,C_25)) ),
    inference(superposition,[status(thm),theory(equality)],[c_41,c_2])).

tff(c_59,plain,(
    ! [A_7,B_8] : r1_tarski(k1_tarski(A_7),k2_tarski(A_7,B_8)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_56])).

tff(c_12,plain,(
    ~ r1_tarski(k1_tarski('#skF_1'),k2_tarski('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_62,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:51:55 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.69/1.12  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.69/1.12  
% 1.69/1.12  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.69/1.13  %$ r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1
% 1.69/1.13  
% 1.69/1.13  %Foreground sorts:
% 1.69/1.13  
% 1.69/1.13  
% 1.69/1.13  %Background operators:
% 1.69/1.13  
% 1.69/1.13  
% 1.69/1.13  %Foreground operators:
% 1.69/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.69/1.13  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.69/1.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.69/1.13  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.69/1.13  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.69/1.13  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.69/1.13  tff('#skF_2', type, '#skF_2': $i).
% 1.69/1.13  tff('#skF_1', type, '#skF_1': $i).
% 1.69/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.69/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.69/1.13  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.69/1.13  
% 1.69/1.13  tff(f_33, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 1.69/1.13  tff(f_29, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_enumset1)).
% 1.69/1.13  tff(f_27, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.69/1.13  tff(f_38, negated_conjecture, ~(![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 1.69/1.13  tff(c_8, plain, (![A_7, B_8]: (k1_enumset1(A_7, A_7, B_8)=k2_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.69/1.13  tff(c_41, plain, (![A_20, B_21, C_22]: (k2_xboole_0(k1_tarski(A_20), k2_tarski(B_21, C_22))=k1_enumset1(A_20, B_21, C_22))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.69/1.13  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, k2_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.69/1.13  tff(c_56, plain, (![A_23, B_24, C_25]: (r1_tarski(k1_tarski(A_23), k1_enumset1(A_23, B_24, C_25)))), inference(superposition, [status(thm), theory('equality')], [c_41, c_2])).
% 1.69/1.13  tff(c_59, plain, (![A_7, B_8]: (r1_tarski(k1_tarski(A_7), k2_tarski(A_7, B_8)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_56])).
% 1.69/1.13  tff(c_12, plain, (~r1_tarski(k1_tarski('#skF_1'), k2_tarski('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.69/1.13  tff(c_62, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_59, c_12])).
% 1.69/1.13  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.69/1.13  
% 1.69/1.13  Inference rules
% 1.69/1.13  ----------------------
% 1.69/1.13  #Ref     : 0
% 1.69/1.13  #Sup     : 11
% 1.69/1.13  #Fact    : 0
% 1.69/1.13  #Define  : 0
% 1.69/1.13  #Split   : 0
% 1.69/1.13  #Chain   : 0
% 1.69/1.13  #Close   : 0
% 1.69/1.13  
% 1.69/1.13  Ordering : KBO
% 1.69/1.13  
% 1.69/1.13  Simplification rules
% 1.69/1.13  ----------------------
% 1.69/1.13  #Subsume      : 0
% 1.69/1.13  #Demod        : 1
% 1.69/1.13  #Tautology    : 8
% 1.69/1.13  #SimpNegUnit  : 0
% 1.69/1.13  #BackRed      : 1
% 1.69/1.13  
% 1.69/1.13  #Partial instantiations: 0
% 1.69/1.13  #Strategies tried      : 1
% 1.69/1.13  
% 1.69/1.13  Timing (in seconds)
% 1.69/1.13  ----------------------
% 1.69/1.14  Preprocessing        : 0.28
% 1.69/1.14  Parsing              : 0.15
% 1.69/1.14  CNF conversion       : 0.02
% 1.69/1.14  Main loop            : 0.07
% 1.69/1.14  Inferencing          : 0.03
% 1.69/1.14  Reduction            : 0.02
% 1.69/1.14  Demodulation         : 0.02
% 1.69/1.14  BG Simplification    : 0.01
% 1.69/1.14  Subsumption          : 0.01
% 1.69/1.14  Abstraction          : 0.01
% 1.69/1.14  MUC search           : 0.00
% 1.69/1.14  Cooper               : 0.00
% 1.69/1.14  Total                : 0.37
% 1.69/1.14  Index Insertion      : 0.00
% 1.69/1.14  Index Deletion       : 0.00
% 1.69/1.14  Index Matching       : 0.00
% 1.69/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
