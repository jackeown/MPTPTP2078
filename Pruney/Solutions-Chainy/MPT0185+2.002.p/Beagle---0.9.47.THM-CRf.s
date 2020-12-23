%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:46 EST 2020

% Result     : Theorem 2.10s
% Output     : CNFRefutation 2.30s
% Verified   : 
% Statistics : Number of formulae       :   31 (  37 expanded)
%              Number of leaves         :   20 (  23 expanded)
%              Depth                    :    5
%              Number of atoms          :   16 (  22 expanded)
%              Number of equality atoms :   15 (  21 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_37,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_33,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_enumset1(A,B,C),k2_tarski(D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l57_enumset1)).

tff(f_29,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_42,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,B,D,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_enumset1)).

tff(c_12,plain,(
    ! [A_15,B_16,C_17,D_18] : k3_enumset1(A_15,A_15,B_16,C_17,D_18) = k2_enumset1(A_15,B_16,C_17,D_18) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_8,plain,(
    ! [A_10,B_11] : k1_enumset1(A_10,A_10,B_11) = k2_tarski(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_95,plain,(
    ! [B_43,A_45,E_46,D_42,C_44] : k2_xboole_0(k1_enumset1(A_45,B_43,C_44),k2_tarski(D_42,E_46)) = k3_enumset1(A_45,B_43,C_44,D_42,E_46) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_104,plain,(
    ! [A_10,B_11,D_42,E_46] : k3_enumset1(A_10,A_10,B_11,D_42,E_46) = k2_xboole_0(k2_tarski(A_10,B_11),k2_tarski(D_42,E_46)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_95])).

tff(c_113,plain,(
    ! [A_10,B_11,D_42,E_46] : k2_xboole_0(k2_tarski(A_10,B_11),k2_tarski(D_42,E_46)) = k2_enumset1(A_10,B_11,D_42,E_46) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_104])).

tff(c_4,plain,(
    ! [B_4,A_3] : k2_tarski(B_4,A_3) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_304,plain,(
    ! [B_70,B_67,C_71,A_69,A_68] : k2_xboole_0(k1_enumset1(A_68,B_67,C_71),k2_tarski(A_69,B_70)) = k3_enumset1(A_68,B_67,C_71,B_70,A_69) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_95])).

tff(c_319,plain,(
    ! [A_10,B_11,B_70,A_69] : k3_enumset1(A_10,A_10,B_11,B_70,A_69) = k2_xboole_0(k2_tarski(A_10,B_11),k2_tarski(A_69,B_70)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_304])).

tff(c_328,plain,(
    ! [A_10,B_11,B_70,A_69] : k2_enumset1(A_10,B_11,B_70,A_69) = k2_enumset1(A_10,B_11,A_69,B_70) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_12,c_319])).

tff(c_16,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_2','#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_475,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_328,c_16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.31  % Computer   : n025.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % DateTime   : Tue Dec  1 16:59:20 EST 2020
% 0.11/0.31  % CPUTime    : 
% 0.17/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.10/1.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.23  
% 2.10/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.23  %$ k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.10/1.23  
% 2.10/1.23  %Foreground sorts:
% 2.10/1.23  
% 2.10/1.23  
% 2.10/1.23  %Background operators:
% 2.10/1.23  
% 2.10/1.23  
% 2.10/1.23  %Foreground operators:
% 2.10/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.10/1.23  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.10/1.23  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.10/1.23  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.10/1.23  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.10/1.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.10/1.23  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.10/1.23  tff('#skF_2', type, '#skF_2': $i).
% 2.10/1.23  tff('#skF_3', type, '#skF_3': $i).
% 2.10/1.23  tff('#skF_1', type, '#skF_1': $i).
% 2.10/1.23  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.10/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.10/1.23  tff('#skF_4', type, '#skF_4': $i).
% 2.10/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.10/1.23  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.10/1.23  
% 2.30/1.24  tff(f_37, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 2.30/1.24  tff(f_33, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.30/1.24  tff(f_31, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_enumset1(A, B, C), k2_tarski(D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l57_enumset1)).
% 2.30/1.24  tff(f_29, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.30/1.24  tff(f_42, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, B, D, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_enumset1)).
% 2.30/1.24  tff(c_12, plain, (![A_15, B_16, C_17, D_18]: (k3_enumset1(A_15, A_15, B_16, C_17, D_18)=k2_enumset1(A_15, B_16, C_17, D_18))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.30/1.24  tff(c_8, plain, (![A_10, B_11]: (k1_enumset1(A_10, A_10, B_11)=k2_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.30/1.24  tff(c_95, plain, (![B_43, A_45, E_46, D_42, C_44]: (k2_xboole_0(k1_enumset1(A_45, B_43, C_44), k2_tarski(D_42, E_46))=k3_enumset1(A_45, B_43, C_44, D_42, E_46))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.30/1.24  tff(c_104, plain, (![A_10, B_11, D_42, E_46]: (k3_enumset1(A_10, A_10, B_11, D_42, E_46)=k2_xboole_0(k2_tarski(A_10, B_11), k2_tarski(D_42, E_46)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_95])).
% 2.30/1.24  tff(c_113, plain, (![A_10, B_11, D_42, E_46]: (k2_xboole_0(k2_tarski(A_10, B_11), k2_tarski(D_42, E_46))=k2_enumset1(A_10, B_11, D_42, E_46))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_104])).
% 2.30/1.24  tff(c_4, plain, (![B_4, A_3]: (k2_tarski(B_4, A_3)=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.30/1.24  tff(c_304, plain, (![B_70, B_67, C_71, A_69, A_68]: (k2_xboole_0(k1_enumset1(A_68, B_67, C_71), k2_tarski(A_69, B_70))=k3_enumset1(A_68, B_67, C_71, B_70, A_69))), inference(superposition, [status(thm), theory('equality')], [c_4, c_95])).
% 2.30/1.24  tff(c_319, plain, (![A_10, B_11, B_70, A_69]: (k3_enumset1(A_10, A_10, B_11, B_70, A_69)=k2_xboole_0(k2_tarski(A_10, B_11), k2_tarski(A_69, B_70)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_304])).
% 2.30/1.24  tff(c_328, plain, (![A_10, B_11, B_70, A_69]: (k2_enumset1(A_10, B_11, B_70, A_69)=k2_enumset1(A_10, B_11, A_69, B_70))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_12, c_319])).
% 2.30/1.24  tff(c_16, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_2', '#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.30/1.24  tff(c_475, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_328, c_16])).
% 2.30/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.30/1.24  
% 2.30/1.24  Inference rules
% 2.30/1.24  ----------------------
% 2.30/1.24  #Ref     : 0
% 2.30/1.24  #Sup     : 116
% 2.30/1.24  #Fact    : 0
% 2.30/1.24  #Define  : 0
% 2.30/1.24  #Split   : 0
% 2.30/1.24  #Chain   : 0
% 2.30/1.24  #Close   : 0
% 2.30/1.24  
% 2.30/1.24  Ordering : KBO
% 2.30/1.24  
% 2.30/1.24  Simplification rules
% 2.30/1.24  ----------------------
% 2.30/1.24  #Subsume      : 4
% 2.30/1.24  #Demod        : 28
% 2.30/1.24  #Tautology    : 78
% 2.30/1.24  #SimpNegUnit  : 0
% 2.30/1.24  #BackRed      : 1
% 2.30/1.24  
% 2.30/1.24  #Partial instantiations: 0
% 2.30/1.24  #Strategies tried      : 1
% 2.30/1.24  
% 2.30/1.24  Timing (in seconds)
% 2.30/1.24  ----------------------
% 2.30/1.24  Preprocessing        : 0.26
% 2.30/1.24  Parsing              : 0.14
% 2.30/1.24  CNF conversion       : 0.02
% 2.30/1.24  Main loop            : 0.24
% 2.30/1.24  Inferencing          : 0.09
% 2.30/1.24  Reduction            : 0.09
% 2.30/1.24  Demodulation         : 0.08
% 2.30/1.24  BG Simplification    : 0.01
% 2.30/1.24  Subsumption          : 0.03
% 2.30/1.24  Abstraction          : 0.01
% 2.30/1.24  MUC search           : 0.00
% 2.30/1.24  Cooper               : 0.00
% 2.30/1.24  Total                : 0.52
% 2.30/1.24  Index Insertion      : 0.00
% 2.30/1.24  Index Deletion       : 0.00
% 2.30/1.24  Index Matching       : 0.00
% 2.30/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
