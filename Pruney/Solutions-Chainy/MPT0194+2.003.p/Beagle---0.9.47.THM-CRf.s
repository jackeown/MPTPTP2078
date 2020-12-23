%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:59 EST 2020

% Result     : Theorem 3.99s
% Output     : CNFRefutation 3.99s
% Verified   : 
% Statistics : Number of formulae       :   31 (  63 expanded)
%              Number of leaves         :   14 (  29 expanded)
%              Depth                    :    6
%              Number of atoms          :   21 (  53 expanded)
%              Number of equality atoms :   20 (  52 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k2_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_31,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,D,A,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_enumset1)).

tff(f_34,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,D,C,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_enumset1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_tarski(B_2,A_1) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_130,plain,(
    ! [A_21,B_22,C_23,D_24] : k2_xboole_0(k2_tarski(A_21,B_22),k2_tarski(C_23,D_24)) = k2_enumset1(A_21,B_22,C_23,D_24) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_151,plain,(
    ! [A_25,B_26,B_27,A_28] : k2_xboole_0(k2_tarski(A_25,B_26),k2_tarski(B_27,A_28)) = k2_enumset1(A_25,B_26,A_28,B_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_130])).

tff(c_6,plain,(
    ! [A_7,B_8,C_9,D_10] : k2_xboole_0(k2_tarski(A_7,B_8),k2_tarski(C_9,D_10)) = k2_enumset1(A_7,B_8,C_9,D_10) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_157,plain,(
    ! [A_25,B_26,B_27,A_28] : k2_enumset1(A_25,B_26,B_27,A_28) = k2_enumset1(A_25,B_26,A_28,B_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_6])).

tff(c_4,plain,(
    ! [B_4,D_6,A_3,C_5] : k2_enumset1(B_4,D_6,A_3,C_5) = k2_enumset1(A_3,B_4,C_5,D_6) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_638,plain,(
    ! [A_45,B_46,C_47,D_48] : k2_xboole_0(k2_tarski(A_45,B_46),k2_tarski(C_47,D_48)) = k2_enumset1(B_46,A_45,C_47,D_48) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_130])).

tff(c_850,plain,(
    ! [B_53,A_54,C_55,D_56] : k2_enumset1(B_53,A_54,C_55,D_56) = k2_enumset1(A_54,B_53,C_55,D_56) ),
    inference(superposition,[status(thm),theory(equality)],[c_638,c_6])).

tff(c_1033,plain,(
    ! [B_4,D_6,A_3,C_5] : k2_enumset1(B_4,D_6,A_3,C_5) = k2_enumset1(B_4,A_3,C_5,D_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_850])).

tff(c_43,plain,(
    ! [B_13,D_14,A_15,C_16] : k2_enumset1(B_13,D_14,A_15,C_16) = k2_enumset1(A_15,B_13,C_16,D_14) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_67,plain,(
    ! [D_6,C_5,B_4,A_3] : k2_enumset1(D_6,C_5,B_4,A_3) = k2_enumset1(A_3,B_4,C_5,D_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_43])).

tff(c_8,plain,(
    k2_enumset1('#skF_2','#skF_4','#skF_3','#skF_1') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_9,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_enumset1('#skF_4','#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_4,c_4,c_8])).

tff(c_72,plain,(
    k2_enumset1('#skF_4','#skF_3','#skF_2','#skF_1') != k2_enumset1('#skF_4','#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_9])).

tff(c_180,plain,(
    k2_enumset1('#skF_4','#skF_3','#skF_1','#skF_2') != k2_enumset1('#skF_4','#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_157,c_72])).

tff(c_1838,plain,(
    k2_enumset1('#skF_4','#skF_1','#skF_2','#skF_3') != k2_enumset1('#skF_4','#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1033,c_180])).

tff(c_1841,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_1838])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:42:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.99/1.65  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.99/1.65  
% 3.99/1.65  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.99/1.65  %$ k2_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.99/1.65  
% 3.99/1.65  %Foreground sorts:
% 3.99/1.65  
% 3.99/1.65  
% 3.99/1.65  %Background operators:
% 3.99/1.65  
% 3.99/1.65  
% 3.99/1.65  %Foreground operators:
% 3.99/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.99/1.65  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.99/1.65  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.99/1.65  tff('#skF_2', type, '#skF_2': $i).
% 3.99/1.65  tff('#skF_3', type, '#skF_3': $i).
% 3.99/1.65  tff('#skF_1', type, '#skF_1': $i).
% 3.99/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.99/1.65  tff('#skF_4', type, '#skF_4': $i).
% 3.99/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.99/1.65  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.99/1.65  
% 3.99/1.66  tff(f_27, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.99/1.66  tff(f_31, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_enumset1)).
% 3.99/1.66  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, D, A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t112_enumset1)).
% 3.99/1.66  tff(f_34, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, D, C, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_enumset1)).
% 3.99/1.66  tff(c_2, plain, (![B_2, A_1]: (k2_tarski(B_2, A_1)=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.99/1.66  tff(c_130, plain, (![A_21, B_22, C_23, D_24]: (k2_xboole_0(k2_tarski(A_21, B_22), k2_tarski(C_23, D_24))=k2_enumset1(A_21, B_22, C_23, D_24))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.99/1.66  tff(c_151, plain, (![A_25, B_26, B_27, A_28]: (k2_xboole_0(k2_tarski(A_25, B_26), k2_tarski(B_27, A_28))=k2_enumset1(A_25, B_26, A_28, B_27))), inference(superposition, [status(thm), theory('equality')], [c_2, c_130])).
% 3.99/1.66  tff(c_6, plain, (![A_7, B_8, C_9, D_10]: (k2_xboole_0(k2_tarski(A_7, B_8), k2_tarski(C_9, D_10))=k2_enumset1(A_7, B_8, C_9, D_10))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.99/1.66  tff(c_157, plain, (![A_25, B_26, B_27, A_28]: (k2_enumset1(A_25, B_26, B_27, A_28)=k2_enumset1(A_25, B_26, A_28, B_27))), inference(superposition, [status(thm), theory('equality')], [c_151, c_6])).
% 3.99/1.66  tff(c_4, plain, (![B_4, D_6, A_3, C_5]: (k2_enumset1(B_4, D_6, A_3, C_5)=k2_enumset1(A_3, B_4, C_5, D_6))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.99/1.66  tff(c_638, plain, (![A_45, B_46, C_47, D_48]: (k2_xboole_0(k2_tarski(A_45, B_46), k2_tarski(C_47, D_48))=k2_enumset1(B_46, A_45, C_47, D_48))), inference(superposition, [status(thm), theory('equality')], [c_2, c_130])).
% 3.99/1.66  tff(c_850, plain, (![B_53, A_54, C_55, D_56]: (k2_enumset1(B_53, A_54, C_55, D_56)=k2_enumset1(A_54, B_53, C_55, D_56))), inference(superposition, [status(thm), theory('equality')], [c_638, c_6])).
% 3.99/1.66  tff(c_1033, plain, (![B_4, D_6, A_3, C_5]: (k2_enumset1(B_4, D_6, A_3, C_5)=k2_enumset1(B_4, A_3, C_5, D_6))), inference(superposition, [status(thm), theory('equality')], [c_4, c_850])).
% 3.99/1.66  tff(c_43, plain, (![B_13, D_14, A_15, C_16]: (k2_enumset1(B_13, D_14, A_15, C_16)=k2_enumset1(A_15, B_13, C_16, D_14))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.99/1.66  tff(c_67, plain, (![D_6, C_5, B_4, A_3]: (k2_enumset1(D_6, C_5, B_4, A_3)=k2_enumset1(A_3, B_4, C_5, D_6))), inference(superposition, [status(thm), theory('equality')], [c_4, c_43])).
% 3.99/1.66  tff(c_8, plain, (k2_enumset1('#skF_2', '#skF_4', '#skF_3', '#skF_1')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.99/1.66  tff(c_9, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_enumset1('#skF_4', '#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_4, c_4, c_8])).
% 3.99/1.66  tff(c_72, plain, (k2_enumset1('#skF_4', '#skF_3', '#skF_2', '#skF_1')!=k2_enumset1('#skF_4', '#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_67, c_9])).
% 3.99/1.66  tff(c_180, plain, (k2_enumset1('#skF_4', '#skF_3', '#skF_1', '#skF_2')!=k2_enumset1('#skF_4', '#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_157, c_157, c_72])).
% 3.99/1.66  tff(c_1838, plain, (k2_enumset1('#skF_4', '#skF_1', '#skF_2', '#skF_3')!=k2_enumset1('#skF_4', '#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1033, c_180])).
% 3.99/1.66  tff(c_1841, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_157, c_1838])).
% 3.99/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.99/1.66  
% 3.99/1.66  Inference rules
% 3.99/1.66  ----------------------
% 3.99/1.66  #Ref     : 0
% 3.99/1.66  #Sup     : 572
% 3.99/1.66  #Fact    : 0
% 3.99/1.66  #Define  : 0
% 3.99/1.66  #Split   : 0
% 3.99/1.66  #Chain   : 0
% 3.99/1.66  #Close   : 0
% 3.99/1.66  
% 3.99/1.66  Ordering : KBO
% 3.99/1.66  
% 3.99/1.66  Simplification rules
% 3.99/1.66  ----------------------
% 3.99/1.66  #Subsume      : 259
% 3.99/1.66  #Demod        : 18
% 3.99/1.66  #Tautology    : 94
% 3.99/1.66  #SimpNegUnit  : 0
% 3.99/1.66  #BackRed      : 3
% 3.99/1.66  
% 3.99/1.66  #Partial instantiations: 0
% 3.99/1.66  #Strategies tried      : 1
% 3.99/1.66  
% 3.99/1.66  Timing (in seconds)
% 3.99/1.66  ----------------------
% 3.99/1.66  Preprocessing        : 0.25
% 3.99/1.66  Parsing              : 0.13
% 3.99/1.67  CNF conversion       : 0.01
% 3.99/1.67  Main loop            : 0.66
% 3.99/1.67  Inferencing          : 0.18
% 3.99/1.67  Reduction            : 0.34
% 3.99/1.67  Demodulation         : 0.31
% 3.99/1.67  BG Simplification    : 0.02
% 3.99/1.67  Subsumption          : 0.09
% 3.99/1.67  Abstraction          : 0.03
% 3.99/1.67  MUC search           : 0.00
% 3.99/1.67  Cooper               : 0.00
% 3.99/1.67  Total                : 0.93
% 3.99/1.67  Index Insertion      : 0.00
% 3.99/1.67  Index Deletion       : 0.00
% 3.99/1.67  Index Matching       : 0.00
% 3.99/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
