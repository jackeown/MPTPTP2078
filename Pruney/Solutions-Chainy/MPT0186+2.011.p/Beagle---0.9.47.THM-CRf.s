%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:48 EST 2020

% Result     : Theorem 1.70s
% Output     : CNFRefutation 1.70s
% Verified   : 
% Statistics : Number of formulae       :   29 (  51 expanded)
%              Number of leaves         :   16 (  26 expanded)
%              Depth                    :    7
%              Number of atoms          :   17 (  39 expanded)
%              Number of equality atoms :   16 (  38 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff(f_27,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,B,D,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_38,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,C,B,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_enumset1)).

tff(c_2,plain,(
    ! [A_1,B_2,D_4,C_3] : k2_enumset1(A_1,B_2,D_4,C_3) = k2_enumset1(A_1,B_2,C_3,D_4) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_23,plain,(
    ! [A_24,B_25,D_26,C_27] : k2_enumset1(A_24,B_25,D_26,C_27) = k2_enumset1(A_24,B_25,C_27,D_26) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_14,B_15,C_16] : k2_enumset1(A_14,A_14,B_15,C_16) = k1_enumset1(A_14,B_15,C_16) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_70,plain,(
    ! [B_28,D_29,C_30] : k2_enumset1(B_28,B_28,D_29,C_30) = k1_enumset1(B_28,C_30,D_29) ),
    inference(superposition,[status(thm),theory(equality)],[c_23,c_8])).

tff(c_82,plain,(
    ! [B_28,D_29,C_30] : k1_enumset1(B_28,D_29,C_30) = k1_enumset1(B_28,C_30,D_29) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_8])).

tff(c_148,plain,(
    ! [A_38,B_39,C_40,D_41] : k2_xboole_0(k1_enumset1(A_38,B_39,C_40),k1_tarski(D_41)) = k2_enumset1(A_38,B_39,C_40,D_41) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_163,plain,(
    ! [B_42,D_43,C_44,D_45] : k2_xboole_0(k1_enumset1(B_42,D_43,C_44),k1_tarski(D_45)) = k2_enumset1(B_42,C_44,D_43,D_45) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_148])).

tff(c_4,plain,(
    ! [A_5,B_6,C_7,D_8] : k2_xboole_0(k1_enumset1(A_5,B_6,C_7),k1_tarski(D_8)) = k2_enumset1(A_5,B_6,C_7,D_8) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_169,plain,(
    ! [B_42,D_43,C_44,D_45] : k2_enumset1(B_42,D_43,C_44,D_45) = k2_enumset1(B_42,C_44,D_43,D_45) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_4])).

tff(c_12,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_3','#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_13,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_4','#skF_3') != k2_enumset1('#skF_1','#skF_3','#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_12])).

tff(c_186,plain,(
    k2_enumset1('#skF_1','#skF_4','#skF_2','#skF_3') != k2_enumset1('#skF_1','#skF_4','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_169,c_13])).

tff(c_189,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_186])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:21:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.70/1.11  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.70/1.11  
% 1.70/1.11  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.70/1.11  %$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.70/1.11  
% 1.70/1.11  %Foreground sorts:
% 1.70/1.11  
% 1.70/1.11  
% 1.70/1.11  %Background operators:
% 1.70/1.11  
% 1.70/1.11  
% 1.70/1.11  %Foreground operators:
% 1.70/1.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.70/1.11  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.70/1.11  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.70/1.11  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.70/1.11  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.70/1.11  tff('#skF_2', type, '#skF_2': $i).
% 1.70/1.11  tff('#skF_3', type, '#skF_3': $i).
% 1.70/1.11  tff('#skF_1', type, '#skF_1': $i).
% 1.70/1.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.70/1.11  tff('#skF_4', type, '#skF_4': $i).
% 1.70/1.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.70/1.11  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.70/1.11  
% 1.70/1.12  tff(f_27, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, B, D, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_enumset1)).
% 1.70/1.12  tff(f_33, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 1.70/1.12  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 1.70/1.12  tff(f_38, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, C, B, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t104_enumset1)).
% 1.70/1.12  tff(c_2, plain, (![A_1, B_2, D_4, C_3]: (k2_enumset1(A_1, B_2, D_4, C_3)=k2_enumset1(A_1, B_2, C_3, D_4))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.70/1.12  tff(c_23, plain, (![A_24, B_25, D_26, C_27]: (k2_enumset1(A_24, B_25, D_26, C_27)=k2_enumset1(A_24, B_25, C_27, D_26))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.70/1.12  tff(c_8, plain, (![A_14, B_15, C_16]: (k2_enumset1(A_14, A_14, B_15, C_16)=k1_enumset1(A_14, B_15, C_16))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.70/1.12  tff(c_70, plain, (![B_28, D_29, C_30]: (k2_enumset1(B_28, B_28, D_29, C_30)=k1_enumset1(B_28, C_30, D_29))), inference(superposition, [status(thm), theory('equality')], [c_23, c_8])).
% 1.70/1.12  tff(c_82, plain, (![B_28, D_29, C_30]: (k1_enumset1(B_28, D_29, C_30)=k1_enumset1(B_28, C_30, D_29))), inference(superposition, [status(thm), theory('equality')], [c_70, c_8])).
% 1.70/1.12  tff(c_148, plain, (![A_38, B_39, C_40, D_41]: (k2_xboole_0(k1_enumset1(A_38, B_39, C_40), k1_tarski(D_41))=k2_enumset1(A_38, B_39, C_40, D_41))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.70/1.12  tff(c_163, plain, (![B_42, D_43, C_44, D_45]: (k2_xboole_0(k1_enumset1(B_42, D_43, C_44), k1_tarski(D_45))=k2_enumset1(B_42, C_44, D_43, D_45))), inference(superposition, [status(thm), theory('equality')], [c_82, c_148])).
% 1.70/1.12  tff(c_4, plain, (![A_5, B_6, C_7, D_8]: (k2_xboole_0(k1_enumset1(A_5, B_6, C_7), k1_tarski(D_8))=k2_enumset1(A_5, B_6, C_7, D_8))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.70/1.12  tff(c_169, plain, (![B_42, D_43, C_44, D_45]: (k2_enumset1(B_42, D_43, C_44, D_45)=k2_enumset1(B_42, C_44, D_43, D_45))), inference(superposition, [status(thm), theory('equality')], [c_163, c_4])).
% 1.70/1.12  tff(c_12, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_3', '#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.70/1.12  tff(c_13, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_4', '#skF_3')!=k2_enumset1('#skF_1', '#skF_3', '#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2, c_12])).
% 1.70/1.12  tff(c_186, plain, (k2_enumset1('#skF_1', '#skF_4', '#skF_2', '#skF_3')!=k2_enumset1('#skF_1', '#skF_4', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_169, c_169, c_13])).
% 1.70/1.12  tff(c_189, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_186])).
% 1.70/1.12  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.70/1.12  
% 1.70/1.12  Inference rules
% 1.70/1.12  ----------------------
% 1.70/1.12  #Ref     : 0
% 1.70/1.12  #Sup     : 42
% 1.70/1.12  #Fact    : 0
% 1.70/1.12  #Define  : 0
% 1.70/1.12  #Split   : 0
% 1.70/1.12  #Chain   : 0
% 1.70/1.12  #Close   : 0
% 1.70/1.12  
% 1.70/1.12  Ordering : KBO
% 1.70/1.12  
% 1.70/1.12  Simplification rules
% 1.70/1.12  ----------------------
% 1.70/1.12  #Subsume      : 1
% 1.70/1.12  #Demod        : 14
% 1.70/1.12  #Tautology    : 35
% 1.70/1.12  #SimpNegUnit  : 0
% 1.70/1.12  #BackRed      : 1
% 1.70/1.12  
% 1.70/1.12  #Partial instantiations: 0
% 1.70/1.12  #Strategies tried      : 1
% 1.70/1.12  
% 1.70/1.12  Timing (in seconds)
% 1.70/1.12  ----------------------
% 1.70/1.13  Preprocessing        : 0.28
% 1.70/1.13  Parsing              : 0.15
% 1.70/1.13  CNF conversion       : 0.01
% 1.70/1.13  Main loop            : 0.13
% 1.70/1.13  Inferencing          : 0.05
% 1.70/1.13  Reduction            : 0.05
% 1.70/1.13  Demodulation         : 0.04
% 1.70/1.13  BG Simplification    : 0.01
% 1.70/1.13  Subsumption          : 0.02
% 1.70/1.13  Abstraction          : 0.01
% 1.70/1.13  MUC search           : 0.00
% 1.70/1.13  Cooper               : 0.00
% 1.70/1.13  Total                : 0.43
% 1.70/1.13  Index Insertion      : 0.00
% 1.70/1.13  Index Deletion       : 0.00
% 1.70/1.13  Index Matching       : 0.00
% 1.70/1.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
