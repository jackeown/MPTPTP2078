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
% DateTime   : Thu Dec  3 09:46:48 EST 2020

% Result     : Theorem 3.49s
% Output     : CNFRefutation 3.49s
% Verified   : 
% Statistics : Number of formulae       :   30 (  51 expanded)
%              Number of leaves         :   17 (  26 expanded)
%              Depth                    :    7
%              Number of atoms          :   18 (  39 expanded)
%              Number of equality atoms :   17 (  38 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,B,D,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_tarski(A,B),k1_enumset1(C,D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(B,C,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_40,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,C,B,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_enumset1)).

tff(c_4,plain,(
    ! [A_4,B_5,D_7,C_6] : k2_enumset1(A_4,B_5,D_7,C_6) = k2_enumset1(A_4,B_5,C_6,D_7) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [E_12,D_11,A_8,C_10,B_9] : k2_xboole_0(k2_tarski(A_8,B_9),k1_enumset1(C_10,D_11,E_12)) = k3_enumset1(A_8,B_9,C_10,D_11,E_12) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2,plain,(
    ! [B_2,C_3,A_1] : k1_enumset1(B_2,C_3,A_1) = k1_enumset1(A_1,B_2,C_3) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_603,plain,(
    ! [E_55,B_56,C_57,D_58,A_54] : k2_xboole_0(k2_tarski(A_54,B_56),k1_enumset1(C_57,D_58,E_55)) = k3_enumset1(A_54,B_56,C_57,D_58,E_55) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_767,plain,(
    ! [A_70,C_72,B_69,A_73,B_71] : k2_xboole_0(k2_tarski(A_70,B_69),k1_enumset1(B_71,C_72,A_73)) = k3_enumset1(A_70,B_69,A_73,B_71,C_72) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_603])).

tff(c_840,plain,(
    ! [D_81,A_77,C_80,B_79,E_78] : k3_enumset1(A_77,B_79,E_78,C_80,D_81) = k3_enumset1(A_77,B_79,C_80,D_81,E_78) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_767])).

tff(c_12,plain,(
    ! [A_18,B_19,C_20,D_21] : k3_enumset1(A_18,A_18,B_19,C_20,D_21) = k2_enumset1(A_18,B_19,C_20,D_21) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_914,plain,(
    ! [B_82,E_83,C_84,D_85] : k3_enumset1(B_82,B_82,E_83,C_84,D_85) = k2_enumset1(B_82,C_84,D_85,E_83) ),
    inference(superposition,[status(thm),theory(equality)],[c_840,c_12])).

tff(c_930,plain,(
    ! [B_82,E_83,C_84,D_85] : k2_enumset1(B_82,E_83,C_84,D_85) = k2_enumset1(B_82,C_84,D_85,E_83) ),
    inference(superposition,[status(thm),theory(equality)],[c_914,c_12])).

tff(c_14,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_3','#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_15,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_4','#skF_3') != k2_enumset1('#skF_1','#skF_3','#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_4,c_14])).

tff(c_953,plain,(
    k2_enumset1('#skF_1','#skF_4','#skF_2','#skF_3') != k2_enumset1('#skF_1','#skF_4','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_930,c_930,c_15])).

tff(c_956,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_953])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n022.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 13:24:40 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.49/1.82  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.49/1.83  
% 3.49/1.83  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.49/1.83  %$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.49/1.83  
% 3.49/1.83  %Foreground sorts:
% 3.49/1.83  
% 3.49/1.83  
% 3.49/1.83  %Background operators:
% 3.49/1.83  
% 3.49/1.83  
% 3.49/1.83  %Foreground operators:
% 3.49/1.83  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.49/1.83  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.49/1.83  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.49/1.83  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.49/1.83  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.49/1.83  tff('#skF_2', type, '#skF_2': $i).
% 3.49/1.83  tff('#skF_3', type, '#skF_3': $i).
% 3.49/1.83  tff('#skF_1', type, '#skF_1': $i).
% 3.49/1.83  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.49/1.83  tff('#skF_4', type, '#skF_4': $i).
% 3.49/1.83  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.49/1.83  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.49/1.83  
% 3.49/1.85  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, B, D, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_enumset1)).
% 3.49/1.85  tff(f_31, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_tarski(A, B), k1_enumset1(C, D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_enumset1)).
% 3.49/1.85  tff(f_27, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(B, C, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_enumset1)).
% 3.49/1.85  tff(f_37, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 3.49/1.85  tff(f_40, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, C, B, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t104_enumset1)).
% 3.49/1.85  tff(c_4, plain, (![A_4, B_5, D_7, C_6]: (k2_enumset1(A_4, B_5, D_7, C_6)=k2_enumset1(A_4, B_5, C_6, D_7))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.49/1.85  tff(c_6, plain, (![E_12, D_11, A_8, C_10, B_9]: (k2_xboole_0(k2_tarski(A_8, B_9), k1_enumset1(C_10, D_11, E_12))=k3_enumset1(A_8, B_9, C_10, D_11, E_12))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.49/1.85  tff(c_2, plain, (![B_2, C_3, A_1]: (k1_enumset1(B_2, C_3, A_1)=k1_enumset1(A_1, B_2, C_3))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.49/1.85  tff(c_603, plain, (![E_55, B_56, C_57, D_58, A_54]: (k2_xboole_0(k2_tarski(A_54, B_56), k1_enumset1(C_57, D_58, E_55))=k3_enumset1(A_54, B_56, C_57, D_58, E_55))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.49/1.85  tff(c_767, plain, (![A_70, C_72, B_69, A_73, B_71]: (k2_xboole_0(k2_tarski(A_70, B_69), k1_enumset1(B_71, C_72, A_73))=k3_enumset1(A_70, B_69, A_73, B_71, C_72))), inference(superposition, [status(thm), theory('equality')], [c_2, c_603])).
% 3.49/1.85  tff(c_840, plain, (![D_81, A_77, C_80, B_79, E_78]: (k3_enumset1(A_77, B_79, E_78, C_80, D_81)=k3_enumset1(A_77, B_79, C_80, D_81, E_78))), inference(superposition, [status(thm), theory('equality')], [c_6, c_767])).
% 3.49/1.85  tff(c_12, plain, (![A_18, B_19, C_20, D_21]: (k3_enumset1(A_18, A_18, B_19, C_20, D_21)=k2_enumset1(A_18, B_19, C_20, D_21))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.49/1.85  tff(c_914, plain, (![B_82, E_83, C_84, D_85]: (k3_enumset1(B_82, B_82, E_83, C_84, D_85)=k2_enumset1(B_82, C_84, D_85, E_83))), inference(superposition, [status(thm), theory('equality')], [c_840, c_12])).
% 3.49/1.85  tff(c_930, plain, (![B_82, E_83, C_84, D_85]: (k2_enumset1(B_82, E_83, C_84, D_85)=k2_enumset1(B_82, C_84, D_85, E_83))), inference(superposition, [status(thm), theory('equality')], [c_914, c_12])).
% 3.49/1.85  tff(c_14, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_3', '#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.49/1.85  tff(c_15, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_4', '#skF_3')!=k2_enumset1('#skF_1', '#skF_3', '#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_4, c_14])).
% 3.49/1.85  tff(c_953, plain, (k2_enumset1('#skF_1', '#skF_4', '#skF_2', '#skF_3')!=k2_enumset1('#skF_1', '#skF_4', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_930, c_930, c_15])).
% 3.49/1.85  tff(c_956, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_953])).
% 3.49/1.85  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.49/1.85  
% 3.49/1.85  Inference rules
% 3.49/1.85  ----------------------
% 3.49/1.85  #Ref     : 0
% 3.49/1.85  #Sup     : 246
% 3.49/1.85  #Fact    : 0
% 3.49/1.85  #Define  : 0
% 3.49/1.85  #Split   : 0
% 3.49/1.85  #Chain   : 0
% 3.49/1.85  #Close   : 0
% 3.49/1.85  
% 3.49/1.85  Ordering : KBO
% 3.49/1.85  
% 3.49/1.85  Simplification rules
% 3.49/1.85  ----------------------
% 3.49/1.85  #Subsume      : 69
% 3.49/1.85  #Demod        : 55
% 3.49/1.85  #Tautology    : 130
% 3.49/1.85  #SimpNegUnit  : 0
% 3.49/1.85  #BackRed      : 1
% 3.49/1.85  
% 3.49/1.85  #Partial instantiations: 0
% 3.49/1.85  #Strategies tried      : 1
% 3.49/1.85  
% 3.49/1.85  Timing (in seconds)
% 3.49/1.85  ----------------------
% 3.49/1.85  Preprocessing        : 0.44
% 3.49/1.85  Parsing              : 0.22
% 3.49/1.85  CNF conversion       : 0.03
% 3.49/1.85  Main loop            : 0.57
% 3.49/1.85  Inferencing          : 0.21
% 3.49/1.85  Reduction            : 0.23
% 3.49/1.85  Demodulation         : 0.19
% 3.49/1.85  BG Simplification    : 0.03
% 3.49/1.85  Subsumption          : 0.08
% 3.49/1.85  Abstraction          : 0.03
% 3.49/1.85  MUC search           : 0.00
% 3.49/1.86  Cooper               : 0.00
% 3.49/1.86  Total                : 1.05
% 3.49/1.86  Index Insertion      : 0.00
% 3.49/1.86  Index Deletion       : 0.00
% 3.49/1.86  Index Matching       : 0.00
% 3.49/1.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
