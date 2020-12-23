%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:50 EST 2020

% Result     : Theorem 2.91s
% Output     : CNFRefutation 2.91s
% Verified   : 
% Statistics : Number of formulae       :   28 (  43 expanded)
%              Number of leaves         :   15 (  22 expanded)
%              Depth                    :    6
%              Number of atoms          :   17 (  32 expanded)
%              Number of equality atoms :   16 (  31 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k2_enumset1 > k1_enumset1 > k2_xboole_0 > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff(f_33,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(B,A,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(B,C,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_enumset1)).

tff(f_36,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,D,C,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_enumset1)).

tff(c_8,plain,(
    ! [B_13,A_12,C_14] : k1_enumset1(B_13,A_12,C_14) = k1_enumset1(A_12,B_13,C_14) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_316,plain,(
    ! [A_31,B_32,C_33,D_34] : k2_xboole_0(k1_tarski(A_31),k1_enumset1(B_32,C_33,D_34)) = k2_enumset1(A_31,B_32,C_33,D_34) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_349,plain,(
    ! [A_35,A_36,B_37,C_38] : k2_xboole_0(k1_tarski(A_35),k1_enumset1(A_36,B_37,C_38)) = k2_enumset1(A_35,B_37,A_36,C_38) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_316])).

tff(c_4,plain,(
    ! [A_4,B_5,C_6,D_7] : k2_xboole_0(k1_tarski(A_4),k1_enumset1(B_5,C_6,D_7)) = k2_enumset1(A_4,B_5,C_6,D_7) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_355,plain,(
    ! [A_35,B_37,A_36,C_38] : k2_enumset1(A_35,B_37,A_36,C_38) = k2_enumset1(A_35,A_36,B_37,C_38) ),
    inference(superposition,[status(thm),theory(equality)],[c_349,c_4])).

tff(c_2,plain,(
    ! [B_2,C_3,A_1] : k1_enumset1(B_2,C_3,A_1) = k1_enumset1(A_1,B_2,C_3) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_424,plain,(
    ! [A_43,A_44,B_45,C_46] : k2_xboole_0(k1_tarski(A_43),k1_enumset1(A_44,B_45,C_46)) = k2_enumset1(A_43,B_45,C_46,A_44) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_316])).

tff(c_346,plain,(
    ! [A_31,A_12,B_13,C_14] : k2_xboole_0(k1_tarski(A_31),k1_enumset1(A_12,B_13,C_14)) = k2_enumset1(A_31,B_13,A_12,C_14) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_316])).

tff(c_430,plain,(
    ! [A_43,B_45,C_46,A_44] : k2_enumset1(A_43,B_45,C_46,A_44) = k2_enumset1(A_43,B_45,A_44,C_46) ),
    inference(superposition,[status(thm),theory(equality)],[c_424,c_346])).

tff(c_10,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_4','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_390,plain,(
    k2_enumset1('#skF_1','#skF_3','#skF_2','#skF_4') != k2_enumset1('#skF_1','#skF_4','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_355,c_10])).

tff(c_472,plain,(
    k2_enumset1('#skF_1','#skF_3','#skF_4','#skF_2') != k2_enumset1('#skF_1','#skF_4','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_430,c_390])).

tff(c_475,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_355,c_472])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:20:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.91/1.71  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.91/1.72  
% 2.91/1.72  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.91/1.72  %$ k2_enumset1 > k1_enumset1 > k2_xboole_0 > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.91/1.72  
% 2.91/1.72  %Foreground sorts:
% 2.91/1.72  
% 2.91/1.72  
% 2.91/1.72  %Background operators:
% 2.91/1.72  
% 2.91/1.72  
% 2.91/1.72  %Foreground operators:
% 2.91/1.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.91/1.72  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.91/1.72  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.91/1.72  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.91/1.72  tff('#skF_2', type, '#skF_2': $i).
% 2.91/1.72  tff('#skF_3', type, '#skF_3': $i).
% 2.91/1.72  tff('#skF_1', type, '#skF_1': $i).
% 2.91/1.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.91/1.72  tff('#skF_4', type, '#skF_4': $i).
% 2.91/1.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.91/1.72  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.91/1.72  
% 2.91/1.73  tff(f_33, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(B, A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_enumset1)).
% 2.91/1.73  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_enumset1)).
% 2.91/1.73  tff(f_27, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(B, C, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_enumset1)).
% 2.91/1.73  tff(f_36, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, D, C, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t107_enumset1)).
% 2.91/1.73  tff(c_8, plain, (![B_13, A_12, C_14]: (k1_enumset1(B_13, A_12, C_14)=k1_enumset1(A_12, B_13, C_14))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.91/1.73  tff(c_316, plain, (![A_31, B_32, C_33, D_34]: (k2_xboole_0(k1_tarski(A_31), k1_enumset1(B_32, C_33, D_34))=k2_enumset1(A_31, B_32, C_33, D_34))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.91/1.73  tff(c_349, plain, (![A_35, A_36, B_37, C_38]: (k2_xboole_0(k1_tarski(A_35), k1_enumset1(A_36, B_37, C_38))=k2_enumset1(A_35, B_37, A_36, C_38))), inference(superposition, [status(thm), theory('equality')], [c_8, c_316])).
% 2.91/1.73  tff(c_4, plain, (![A_4, B_5, C_6, D_7]: (k2_xboole_0(k1_tarski(A_4), k1_enumset1(B_5, C_6, D_7))=k2_enumset1(A_4, B_5, C_6, D_7))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.91/1.73  tff(c_355, plain, (![A_35, B_37, A_36, C_38]: (k2_enumset1(A_35, B_37, A_36, C_38)=k2_enumset1(A_35, A_36, B_37, C_38))), inference(superposition, [status(thm), theory('equality')], [c_349, c_4])).
% 2.91/1.73  tff(c_2, plain, (![B_2, C_3, A_1]: (k1_enumset1(B_2, C_3, A_1)=k1_enumset1(A_1, B_2, C_3))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.91/1.73  tff(c_424, plain, (![A_43, A_44, B_45, C_46]: (k2_xboole_0(k1_tarski(A_43), k1_enumset1(A_44, B_45, C_46))=k2_enumset1(A_43, B_45, C_46, A_44))), inference(superposition, [status(thm), theory('equality')], [c_2, c_316])).
% 2.91/1.73  tff(c_346, plain, (![A_31, A_12, B_13, C_14]: (k2_xboole_0(k1_tarski(A_31), k1_enumset1(A_12, B_13, C_14))=k2_enumset1(A_31, B_13, A_12, C_14))), inference(superposition, [status(thm), theory('equality')], [c_8, c_316])).
% 2.91/1.73  tff(c_430, plain, (![A_43, B_45, C_46, A_44]: (k2_enumset1(A_43, B_45, C_46, A_44)=k2_enumset1(A_43, B_45, A_44, C_46))), inference(superposition, [status(thm), theory('equality')], [c_424, c_346])).
% 2.91/1.73  tff(c_10, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_4', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.91/1.73  tff(c_390, plain, (k2_enumset1('#skF_1', '#skF_3', '#skF_2', '#skF_4')!=k2_enumset1('#skF_1', '#skF_4', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_355, c_10])).
% 2.91/1.73  tff(c_472, plain, (k2_enumset1('#skF_1', '#skF_3', '#skF_4', '#skF_2')!=k2_enumset1('#skF_1', '#skF_4', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_430, c_390])).
% 2.91/1.73  tff(c_475, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_355, c_472])).
% 2.91/1.73  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.91/1.73  
% 2.91/1.73  Inference rules
% 2.91/1.73  ----------------------
% 2.91/1.73  #Ref     : 0
% 2.91/1.73  #Sup     : 134
% 2.91/1.73  #Fact    : 0
% 2.91/1.73  #Define  : 0
% 2.91/1.73  #Split   : 0
% 2.91/1.73  #Chain   : 0
% 2.91/1.73  #Close   : 0
% 2.91/1.73  
% 2.91/1.73  Ordering : KBO
% 2.91/1.73  
% 2.91/1.73  Simplification rules
% 2.91/1.73  ----------------------
% 2.91/1.73  #Subsume      : 51
% 2.91/1.73  #Demod        : 8
% 2.91/1.73  #Tautology    : 49
% 2.91/1.73  #SimpNegUnit  : 0
% 2.91/1.73  #BackRed      : 2
% 2.91/1.73  
% 2.91/1.73  #Partial instantiations: 0
% 2.91/1.73  #Strategies tried      : 1
% 2.91/1.73  
% 2.91/1.73  Timing (in seconds)
% 2.91/1.73  ----------------------
% 2.91/1.74  Preprocessing        : 0.42
% 2.91/1.74  Parsing              : 0.21
% 2.91/1.74  CNF conversion       : 0.02
% 2.91/1.74  Main loop            : 0.41
% 2.91/1.74  Inferencing          : 0.14
% 2.91/1.74  Reduction            : 0.17
% 2.91/1.74  Demodulation         : 0.15
% 2.91/1.74  BG Simplification    : 0.02
% 2.91/1.74  Subsumption          : 0.06
% 2.91/1.74  Abstraction          : 0.02
% 2.91/1.74  MUC search           : 0.00
% 2.91/1.74  Cooper               : 0.00
% 2.91/1.74  Total                : 0.86
% 2.91/1.74  Index Insertion      : 0.00
% 2.91/1.74  Index Deletion       : 0.00
% 2.91/1.74  Index Matching       : 0.00
% 2.91/1.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
