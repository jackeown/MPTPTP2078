%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:11 EST 2020

% Result     : Theorem 1.56s
% Output     : CNFRefutation 1.56s
% Verified   : 
% Statistics : Number of formulae       :   31 (  33 expanded)
%              Number of leaves         :   20 (  21 expanded)
%              Depth                    :    6
%              Number of atoms          :   17 (  19 expanded)
%              Number of equality atoms :   16 (  18 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_35,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_33,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_tarski(A,B),k1_enumset1(C,D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_enumset1)).

tff(f_42,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_zfmisc_1)).

tff(c_10,plain,(
    ! [A_11,B_12] : k1_enumset1(A_11,A_11,B_12) = k2_tarski(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_13,B_14,C_15] : k2_enumset1(A_13,A_13,B_14,C_15) = k1_enumset1(A_13,B_14,C_15) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [A_16,B_17,C_18,D_19] : k3_enumset1(A_16,A_16,B_17,C_18,D_19) = k2_enumset1(A_16,B_17,C_18,D_19) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8,plain,(
    ! [A_10] : k2_tarski(A_10,A_10) = k1_tarski(A_10) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_71,plain,(
    ! [A_37,D_34,B_35,C_36,E_38] : k2_xboole_0(k2_tarski(A_37,B_35),k1_enumset1(C_36,D_34,E_38)) = k3_enumset1(A_37,B_35,C_36,D_34,E_38) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_83,plain,(
    ! [A_10,C_36,D_34,E_38] : k3_enumset1(A_10,A_10,C_36,D_34,E_38) = k2_xboole_0(k1_tarski(A_10),k1_enumset1(C_36,D_34,E_38)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_71])).

tff(c_87,plain,(
    ! [A_39,C_40,D_41,E_42] : k2_xboole_0(k1_tarski(A_39),k1_enumset1(C_40,D_41,E_42)) = k2_enumset1(A_39,C_40,D_41,E_42) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_83])).

tff(c_96,plain,(
    ! [A_39,A_11,B_12] : k2_xboole_0(k1_tarski(A_39),k2_tarski(A_11,B_12)) = k2_enumset1(A_39,A_11,A_11,B_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_87])).

tff(c_16,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k2_tarski('#skF_1','#skF_2')) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_99,plain,(
    k2_enumset1('#skF_1','#skF_1','#skF_1','#skF_2') != k2_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_16])).

tff(c_102,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_12,c_99])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:54:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.56/1.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.56/1.15  
% 1.56/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.56/1.15  %$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1
% 1.56/1.15  
% 1.56/1.15  %Foreground sorts:
% 1.56/1.15  
% 1.56/1.15  
% 1.56/1.15  %Background operators:
% 1.56/1.15  
% 1.56/1.15  
% 1.56/1.15  %Foreground operators:
% 1.56/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.56/1.15  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.56/1.15  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.56/1.15  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.56/1.15  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.56/1.15  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.56/1.15  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.56/1.15  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.56/1.15  tff('#skF_2', type, '#skF_2': $i).
% 1.56/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.56/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.56/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.56/1.15  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.56/1.15  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.56/1.15  
% 1.56/1.16  tff(f_35, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 1.56/1.16  tff(f_37, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 1.56/1.16  tff(f_39, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 1.56/1.16  tff(f_33, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.56/1.16  tff(f_31, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_tarski(A, B), k1_enumset1(C, D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_enumset1)).
% 1.56/1.16  tff(f_42, negated_conjecture, ~(![A, B]: (k2_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_zfmisc_1)).
% 1.56/1.16  tff(c_10, plain, (![A_11, B_12]: (k1_enumset1(A_11, A_11, B_12)=k2_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.56/1.16  tff(c_12, plain, (![A_13, B_14, C_15]: (k2_enumset1(A_13, A_13, B_14, C_15)=k1_enumset1(A_13, B_14, C_15))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.56/1.16  tff(c_14, plain, (![A_16, B_17, C_18, D_19]: (k3_enumset1(A_16, A_16, B_17, C_18, D_19)=k2_enumset1(A_16, B_17, C_18, D_19))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.56/1.16  tff(c_8, plain, (![A_10]: (k2_tarski(A_10, A_10)=k1_tarski(A_10))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.56/1.16  tff(c_71, plain, (![A_37, D_34, B_35, C_36, E_38]: (k2_xboole_0(k2_tarski(A_37, B_35), k1_enumset1(C_36, D_34, E_38))=k3_enumset1(A_37, B_35, C_36, D_34, E_38))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.56/1.16  tff(c_83, plain, (![A_10, C_36, D_34, E_38]: (k3_enumset1(A_10, A_10, C_36, D_34, E_38)=k2_xboole_0(k1_tarski(A_10), k1_enumset1(C_36, D_34, E_38)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_71])).
% 1.56/1.16  tff(c_87, plain, (![A_39, C_40, D_41, E_42]: (k2_xboole_0(k1_tarski(A_39), k1_enumset1(C_40, D_41, E_42))=k2_enumset1(A_39, C_40, D_41, E_42))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_83])).
% 1.56/1.16  tff(c_96, plain, (![A_39, A_11, B_12]: (k2_xboole_0(k1_tarski(A_39), k2_tarski(A_11, B_12))=k2_enumset1(A_39, A_11, A_11, B_12))), inference(superposition, [status(thm), theory('equality')], [c_10, c_87])).
% 1.56/1.16  tff(c_16, plain, (k2_xboole_0(k1_tarski('#skF_1'), k2_tarski('#skF_1', '#skF_2'))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.56/1.16  tff(c_99, plain, (k2_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_2')!=k2_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_16])).
% 1.56/1.16  tff(c_102, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_12, c_99])).
% 1.56/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.56/1.16  
% 1.56/1.16  Inference rules
% 1.56/1.16  ----------------------
% 1.56/1.16  #Ref     : 0
% 1.56/1.16  #Sup     : 19
% 1.56/1.16  #Fact    : 0
% 1.56/1.16  #Define  : 0
% 1.56/1.16  #Split   : 0
% 1.56/1.16  #Chain   : 0
% 1.56/1.16  #Close   : 0
% 1.56/1.16  
% 1.56/1.16  Ordering : KBO
% 1.56/1.16  
% 1.56/1.16  Simplification rules
% 1.56/1.16  ----------------------
% 1.56/1.16  #Subsume      : 0
% 1.56/1.16  #Demod        : 4
% 1.56/1.16  #Tautology    : 16
% 1.56/1.16  #SimpNegUnit  : 0
% 1.56/1.16  #BackRed      : 1
% 1.56/1.16  
% 1.56/1.16  #Partial instantiations: 0
% 1.56/1.16  #Strategies tried      : 1
% 1.56/1.16  
% 1.56/1.16  Timing (in seconds)
% 1.56/1.16  ----------------------
% 1.56/1.16  Preprocessing        : 0.27
% 1.56/1.16  Parsing              : 0.14
% 1.56/1.16  CNF conversion       : 0.02
% 1.56/1.16  Main loop            : 0.09
% 1.56/1.16  Inferencing          : 0.04
% 1.56/1.16  Reduction            : 0.03
% 1.56/1.16  Demodulation         : 0.02
% 1.56/1.16  BG Simplification    : 0.01
% 1.56/1.16  Subsumption          : 0.01
% 1.56/1.16  Abstraction          : 0.01
% 1.56/1.16  MUC search           : 0.00
% 1.56/1.16  Cooper               : 0.00
% 1.56/1.16  Total                : 0.39
% 1.56/1.16  Index Insertion      : 0.00
% 1.56/1.16  Index Deletion       : 0.00
% 1.56/1.16  Index Matching       : 0.00
% 1.56/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
