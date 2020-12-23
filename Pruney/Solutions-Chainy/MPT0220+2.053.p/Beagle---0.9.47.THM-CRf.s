%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:11 EST 2020

% Result     : Theorem 1.55s
% Output     : CNFRefutation 1.55s
% Verified   : 
% Statistics : Number of formulae       :   20 (  20 expanded)
%              Number of leaves         :   13 (  13 expanded)
%              Depth                    :    4
%              Number of atoms          :   11 (  11 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k2_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff(f_31,axiom,(
    ! [A,B] : k2_enumset1(A,A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_enumset1)).

tff(f_29,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_34,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_zfmisc_1)).

tff(c_6,plain,(
    ! [A_6,B_7] : k2_enumset1(A_6,A_6,A_6,B_7) = k2_tarski(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_5] : k2_tarski(A_5,A_5) = k1_tarski(A_5) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_27,plain,(
    ! [A_11,B_12,C_13,D_14] : k2_xboole_0(k2_tarski(A_11,B_12),k2_tarski(C_13,D_14)) = k2_enumset1(A_11,B_12,C_13,D_14) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_36,plain,(
    ! [A_5,C_13,D_14] : k2_xboole_0(k1_tarski(A_5),k2_tarski(C_13,D_14)) = k2_enumset1(A_5,A_5,C_13,D_14) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_27])).

tff(c_8,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k2_tarski('#skF_1','#skF_2')) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_42,plain,(
    k2_enumset1('#skF_1','#skF_1','#skF_1','#skF_2') != k2_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_8])).

tff(c_45,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:39:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.55/1.10  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.55/1.10  
% 1.55/1.10  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.55/1.11  %$ k2_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1
% 1.55/1.11  
% 1.55/1.11  %Foreground sorts:
% 1.55/1.11  
% 1.55/1.11  
% 1.55/1.11  %Background operators:
% 1.55/1.11  
% 1.55/1.11  
% 1.55/1.11  %Foreground operators:
% 1.55/1.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.55/1.11  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.55/1.11  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.55/1.11  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.55/1.11  tff('#skF_2', type, '#skF_2': $i).
% 1.55/1.11  tff('#skF_1', type, '#skF_1': $i).
% 1.55/1.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.55/1.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.55/1.11  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.55/1.11  
% 1.55/1.11  tff(f_31, axiom, (![A, B]: (k2_enumset1(A, A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_enumset1)).
% 1.55/1.11  tff(f_29, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.55/1.11  tff(f_27, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l53_enumset1)).
% 1.55/1.11  tff(f_34, negated_conjecture, ~(![A, B]: (k2_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_zfmisc_1)).
% 1.55/1.11  tff(c_6, plain, (![A_6, B_7]: (k2_enumset1(A_6, A_6, A_6, B_7)=k2_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.55/1.11  tff(c_4, plain, (![A_5]: (k2_tarski(A_5, A_5)=k1_tarski(A_5))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.55/1.11  tff(c_27, plain, (![A_11, B_12, C_13, D_14]: (k2_xboole_0(k2_tarski(A_11, B_12), k2_tarski(C_13, D_14))=k2_enumset1(A_11, B_12, C_13, D_14))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.55/1.11  tff(c_36, plain, (![A_5, C_13, D_14]: (k2_xboole_0(k1_tarski(A_5), k2_tarski(C_13, D_14))=k2_enumset1(A_5, A_5, C_13, D_14))), inference(superposition, [status(thm), theory('equality')], [c_4, c_27])).
% 1.55/1.11  tff(c_8, plain, (k2_xboole_0(k1_tarski('#skF_1'), k2_tarski('#skF_1', '#skF_2'))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.55/1.11  tff(c_42, plain, (k2_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_2')!=k2_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_8])).
% 1.55/1.11  tff(c_45, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_42])).
% 1.55/1.11  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.55/1.11  
% 1.55/1.11  Inference rules
% 1.55/1.11  ----------------------
% 1.55/1.11  #Ref     : 0
% 1.55/1.11  #Sup     : 8
% 1.55/1.11  #Fact    : 0
% 1.55/1.11  #Define  : 0
% 1.55/1.11  #Split   : 0
% 1.55/1.11  #Chain   : 0
% 1.55/1.11  #Close   : 0
% 1.55/1.11  
% 1.55/1.11  Ordering : KBO
% 1.55/1.11  
% 1.55/1.11  Simplification rules
% 1.55/1.11  ----------------------
% 1.55/1.11  #Subsume      : 0
% 1.55/1.11  #Demod        : 2
% 1.55/1.11  #Tautology    : 6
% 1.55/1.11  #SimpNegUnit  : 0
% 1.55/1.11  #BackRed      : 1
% 1.55/1.11  
% 1.55/1.11  #Partial instantiations: 0
% 1.55/1.11  #Strategies tried      : 1
% 1.55/1.11  
% 1.55/1.11  Timing (in seconds)
% 1.55/1.11  ----------------------
% 1.55/1.12  Preprocessing        : 0.24
% 1.55/1.12  Parsing              : 0.12
% 1.55/1.12  CNF conversion       : 0.01
% 1.55/1.12  Main loop            : 0.06
% 1.55/1.12  Inferencing          : 0.03
% 1.55/1.12  Reduction            : 0.02
% 1.55/1.12  Demodulation         : 0.02
% 1.55/1.12  BG Simplification    : 0.01
% 1.55/1.12  Subsumption          : 0.01
% 1.55/1.12  Abstraction          : 0.01
% 1.55/1.12  MUC search           : 0.00
% 1.55/1.12  Cooper               : 0.00
% 1.55/1.12  Total                : 0.32
% 1.55/1.12  Index Insertion      : 0.00
% 1.55/1.12  Index Deletion       : 0.00
% 1.55/1.12  Index Matching       : 0.00
% 1.55/1.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
