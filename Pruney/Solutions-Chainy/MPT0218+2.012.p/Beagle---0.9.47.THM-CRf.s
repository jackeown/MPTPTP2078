%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:47 EST 2020

% Result     : Theorem 1.77s
% Output     : CNFRefutation 1.77s
% Verified   : 
% Statistics : Number of formulae       :   31 (  31 expanded)
%              Number of leaves         :   20 (  20 expanded)
%              Depth                    :    6
%              Number of atoms          :   17 (  17 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1

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

tff(f_37,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_35,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_42,negated_conjecture,(
    ~ ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(c_12,plain,(
    ! [A_12,B_13] : k1_enumset1(A_12,A_12,B_13) = k2_tarski(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [A_11] : k2_tarski(A_11,A_11) = k1_tarski(A_11) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14,plain,(
    ! [A_14,B_15,C_16] : k2_enumset1(A_14,A_14,B_15,C_16) = k1_enumset1(A_14,B_15,C_16) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_63,plain,(
    ! [A_29,B_30,C_31,D_32] : k2_xboole_0(k2_tarski(A_29,B_30),k2_tarski(C_31,D_32)) = k2_enumset1(A_29,B_30,C_31,D_32) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(A_3,k2_xboole_0(A_3,B_4)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_82,plain,(
    ! [A_33,B_34,C_35,D_36] : r1_tarski(k2_tarski(A_33,B_34),k2_enumset1(A_33,B_34,C_35,D_36)) ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_4])).

tff(c_85,plain,(
    ! [A_14,B_15,C_16] : r1_tarski(k2_tarski(A_14,A_14),k1_enumset1(A_14,B_15,C_16)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_82])).

tff(c_129,plain,(
    ! [A_40,B_41,C_42] : r1_tarski(k1_tarski(A_40),k1_enumset1(A_40,B_41,C_42)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_85])).

tff(c_132,plain,(
    ! [A_12,B_13] : r1_tarski(k1_tarski(A_12),k2_tarski(A_12,B_13)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_129])).

tff(c_16,plain,(
    ~ r1_tarski(k1_tarski('#skF_1'),k2_tarski('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_135,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:24:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.77/1.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.77/1.16  
% 1.77/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.77/1.16  %$ r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1
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
% 1.77/1.16  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.77/1.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.77/1.16  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.77/1.16  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.77/1.16  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.77/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.77/1.16  tff('#skF_1', type, '#skF_1': $i).
% 1.77/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.77/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.77/1.16  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.77/1.16  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.77/1.16  
% 1.77/1.17  tff(f_37, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 1.77/1.17  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.77/1.17  tff(f_39, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 1.77/1.17  tff(f_33, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l53_enumset1)).
% 1.77/1.17  tff(f_29, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.77/1.17  tff(f_42, negated_conjecture, ~(![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 1.77/1.17  tff(c_12, plain, (![A_12, B_13]: (k1_enumset1(A_12, A_12, B_13)=k2_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.77/1.17  tff(c_10, plain, (![A_11]: (k2_tarski(A_11, A_11)=k1_tarski(A_11))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.77/1.17  tff(c_14, plain, (![A_14, B_15, C_16]: (k2_enumset1(A_14, A_14, B_15, C_16)=k1_enumset1(A_14, B_15, C_16))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.77/1.17  tff(c_63, plain, (![A_29, B_30, C_31, D_32]: (k2_xboole_0(k2_tarski(A_29, B_30), k2_tarski(C_31, D_32))=k2_enumset1(A_29, B_30, C_31, D_32))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.77/1.17  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(A_3, k2_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.77/1.17  tff(c_82, plain, (![A_33, B_34, C_35, D_36]: (r1_tarski(k2_tarski(A_33, B_34), k2_enumset1(A_33, B_34, C_35, D_36)))), inference(superposition, [status(thm), theory('equality')], [c_63, c_4])).
% 1.77/1.17  tff(c_85, plain, (![A_14, B_15, C_16]: (r1_tarski(k2_tarski(A_14, A_14), k1_enumset1(A_14, B_15, C_16)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_82])).
% 1.77/1.17  tff(c_129, plain, (![A_40, B_41, C_42]: (r1_tarski(k1_tarski(A_40), k1_enumset1(A_40, B_41, C_42)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_85])).
% 1.77/1.17  tff(c_132, plain, (![A_12, B_13]: (r1_tarski(k1_tarski(A_12), k2_tarski(A_12, B_13)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_129])).
% 1.77/1.17  tff(c_16, plain, (~r1_tarski(k1_tarski('#skF_1'), k2_tarski('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.77/1.17  tff(c_135, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_132, c_16])).
% 1.77/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.77/1.17  
% 1.77/1.17  Inference rules
% 1.77/1.17  ----------------------
% 1.77/1.17  #Ref     : 0
% 1.77/1.17  #Sup     : 27
% 1.77/1.17  #Fact    : 0
% 1.77/1.17  #Define  : 0
% 1.77/1.17  #Split   : 0
% 1.77/1.17  #Chain   : 0
% 1.77/1.17  #Close   : 0
% 1.83/1.17  
% 1.83/1.17  Ordering : KBO
% 1.83/1.17  
% 1.83/1.17  Simplification rules
% 1.83/1.17  ----------------------
% 1.83/1.17  #Subsume      : 0
% 1.83/1.17  #Demod        : 8
% 1.83/1.17  #Tautology    : 18
% 1.83/1.17  #SimpNegUnit  : 0
% 1.83/1.17  #BackRed      : 1
% 1.83/1.17  
% 1.83/1.17  #Partial instantiations: 0
% 1.83/1.17  #Strategies tried      : 1
% 1.83/1.17  
% 1.83/1.17  Timing (in seconds)
% 1.83/1.17  ----------------------
% 1.83/1.17  Preprocessing        : 0.29
% 1.83/1.17  Parsing              : 0.16
% 1.83/1.18  CNF conversion       : 0.01
% 1.83/1.18  Main loop            : 0.11
% 1.83/1.18  Inferencing          : 0.05
% 1.83/1.18  Reduction            : 0.04
% 1.83/1.18  Demodulation         : 0.03
% 1.83/1.18  BG Simplification    : 0.01
% 1.83/1.18  Subsumption          : 0.01
% 1.83/1.18  Abstraction          : 0.01
% 1.83/1.18  MUC search           : 0.00
% 1.83/1.18  Cooper               : 0.00
% 1.83/1.18  Total                : 0.42
% 1.83/1.18  Index Insertion      : 0.00
% 1.83/1.18  Index Deletion       : 0.00
% 1.83/1.18  Index Matching       : 0.00
% 1.83/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
