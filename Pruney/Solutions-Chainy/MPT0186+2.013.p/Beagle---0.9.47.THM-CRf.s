%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:48 EST 2020

% Result     : Theorem 2.04s
% Output     : CNFRefutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :   32 (  63 expanded)
%              Number of leaves         :   19 (  32 expanded)
%              Depth                    :    6
%              Number of atoms          :   18 (  49 expanded)
%              Number of equality atoms :   17 (  48 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_27,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,B,D,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_tarski(E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).

tff(f_42,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,C,B,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_enumset1)).

tff(c_2,plain,(
    ! [A_1,B_2,D_4,C_3] : k2_enumset1(A_1,B_2,D_4,C_3) = k2_enumset1(A_1,B_2,C_3,D_4) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_16,B_17,C_18,D_19] : k3_enumset1(A_16,A_16,B_17,C_18,D_19) = k2_enumset1(A_16,B_17,C_18,D_19) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [A_13,B_14,C_15] : k2_enumset1(A_13,A_13,B_14,C_15) = k1_enumset1(A_13,B_14,C_15) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_231,plain,(
    ! [D_52,B_53,A_55,E_56,C_54] : k2_xboole_0(k2_enumset1(A_55,B_53,C_54,D_52),k1_tarski(E_56)) = k3_enumset1(A_55,B_53,C_54,D_52,E_56) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_249,plain,(
    ! [A_13,B_14,C_15,E_56] : k3_enumset1(A_13,A_13,B_14,C_15,E_56) = k2_xboole_0(k1_enumset1(A_13,B_14,C_15),k1_tarski(E_56)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_231])).

tff(c_253,plain,(
    ! [A_13,B_14,C_15,E_56] : k2_xboole_0(k1_enumset1(A_13,B_14,C_15),k1_tarski(E_56)) = k2_enumset1(A_13,B_14,C_15,E_56) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_249])).

tff(c_278,plain,(
    ! [B_63,E_61,A_65,D_62,C_64] : k2_xboole_0(k2_enumset1(A_65,B_63,D_62,C_64),k1_tarski(E_61)) = k3_enumset1(A_65,B_63,C_64,D_62,E_61) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_231])).

tff(c_302,plain,(
    ! [A_13,C_15,B_14,E_61] : k3_enumset1(A_13,A_13,C_15,B_14,E_61) = k2_xboole_0(k1_enumset1(A_13,B_14,C_15),k1_tarski(E_61)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_278])).

tff(c_308,plain,(
    ! [A_13,C_15,B_14,E_61] : k2_enumset1(A_13,C_15,B_14,E_61) = k2_enumset1(A_13,B_14,C_15,E_61) ),
    inference(demodulation,[status(thm),theory(equality)],[c_253,c_12,c_302])).

tff(c_16,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_3','#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_17,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_4','#skF_3') != k2_enumset1('#skF_1','#skF_3','#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_16])).

tff(c_331,plain,(
    k2_enumset1('#skF_1','#skF_4','#skF_2','#skF_3') != k2_enumset1('#skF_1','#skF_4','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_308,c_308,c_17])).

tff(c_334,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_331])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:43:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.04/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.04/1.25  
% 2.04/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.04/1.25  %$ k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.04/1.25  
% 2.04/1.25  %Foreground sorts:
% 2.04/1.25  
% 2.04/1.25  
% 2.04/1.25  %Background operators:
% 2.04/1.25  
% 2.04/1.25  
% 2.04/1.25  %Foreground operators:
% 2.04/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.04/1.25  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.04/1.25  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.04/1.25  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.04/1.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.04/1.25  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.04/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.04/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.04/1.25  tff('#skF_1', type, '#skF_1': $i).
% 2.04/1.25  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.04/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.04/1.25  tff('#skF_4', type, '#skF_4': $i).
% 2.04/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.04/1.25  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.04/1.25  
% 2.04/1.26  tff(f_27, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, B, D, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_enumset1)).
% 2.04/1.26  tff(f_37, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 2.04/1.26  tff(f_35, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.04/1.26  tff(f_29, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_tarski(E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_enumset1)).
% 2.04/1.26  tff(f_42, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, C, B, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t104_enumset1)).
% 2.04/1.26  tff(c_2, plain, (![A_1, B_2, D_4, C_3]: (k2_enumset1(A_1, B_2, D_4, C_3)=k2_enumset1(A_1, B_2, C_3, D_4))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.04/1.26  tff(c_12, plain, (![A_16, B_17, C_18, D_19]: (k3_enumset1(A_16, A_16, B_17, C_18, D_19)=k2_enumset1(A_16, B_17, C_18, D_19))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.04/1.26  tff(c_10, plain, (![A_13, B_14, C_15]: (k2_enumset1(A_13, A_13, B_14, C_15)=k1_enumset1(A_13, B_14, C_15))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.04/1.26  tff(c_231, plain, (![D_52, B_53, A_55, E_56, C_54]: (k2_xboole_0(k2_enumset1(A_55, B_53, C_54, D_52), k1_tarski(E_56))=k3_enumset1(A_55, B_53, C_54, D_52, E_56))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.04/1.26  tff(c_249, plain, (![A_13, B_14, C_15, E_56]: (k3_enumset1(A_13, A_13, B_14, C_15, E_56)=k2_xboole_0(k1_enumset1(A_13, B_14, C_15), k1_tarski(E_56)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_231])).
% 2.04/1.26  tff(c_253, plain, (![A_13, B_14, C_15, E_56]: (k2_xboole_0(k1_enumset1(A_13, B_14, C_15), k1_tarski(E_56))=k2_enumset1(A_13, B_14, C_15, E_56))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_249])).
% 2.04/1.26  tff(c_278, plain, (![B_63, E_61, A_65, D_62, C_64]: (k2_xboole_0(k2_enumset1(A_65, B_63, D_62, C_64), k1_tarski(E_61))=k3_enumset1(A_65, B_63, C_64, D_62, E_61))), inference(superposition, [status(thm), theory('equality')], [c_2, c_231])).
% 2.04/1.26  tff(c_302, plain, (![A_13, C_15, B_14, E_61]: (k3_enumset1(A_13, A_13, C_15, B_14, E_61)=k2_xboole_0(k1_enumset1(A_13, B_14, C_15), k1_tarski(E_61)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_278])).
% 2.04/1.26  tff(c_308, plain, (![A_13, C_15, B_14, E_61]: (k2_enumset1(A_13, C_15, B_14, E_61)=k2_enumset1(A_13, B_14, C_15, E_61))), inference(demodulation, [status(thm), theory('equality')], [c_253, c_12, c_302])).
% 2.04/1.26  tff(c_16, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_3', '#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.04/1.26  tff(c_17, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_4', '#skF_3')!=k2_enumset1('#skF_1', '#skF_3', '#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2, c_16])).
% 2.04/1.26  tff(c_331, plain, (k2_enumset1('#skF_1', '#skF_4', '#skF_2', '#skF_3')!=k2_enumset1('#skF_1', '#skF_4', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_308, c_308, c_17])).
% 2.04/1.26  tff(c_334, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_331])).
% 2.04/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.04/1.26  
% 2.04/1.26  Inference rules
% 2.04/1.26  ----------------------
% 2.04/1.26  #Ref     : 0
% 2.04/1.26  #Sup     : 75
% 2.04/1.26  #Fact    : 0
% 2.04/1.26  #Define  : 0
% 2.04/1.26  #Split   : 0
% 2.04/1.26  #Chain   : 0
% 2.04/1.26  #Close   : 0
% 2.04/1.26  
% 2.04/1.26  Ordering : KBO
% 2.04/1.26  
% 2.04/1.26  Simplification rules
% 2.04/1.26  ----------------------
% 2.04/1.26  #Subsume      : 1
% 2.04/1.26  #Demod        : 33
% 2.04/1.26  #Tautology    : 59
% 2.04/1.26  #SimpNegUnit  : 0
% 2.04/1.26  #BackRed      : 1
% 2.04/1.26  
% 2.04/1.26  #Partial instantiations: 0
% 2.04/1.26  #Strategies tried      : 1
% 2.04/1.26  
% 2.04/1.26  Timing (in seconds)
% 2.04/1.26  ----------------------
% 2.04/1.26  Preprocessing        : 0.27
% 2.04/1.26  Parsing              : 0.14
% 2.04/1.26  CNF conversion       : 0.02
% 2.04/1.26  Main loop            : 0.19
% 2.04/1.26  Inferencing          : 0.08
% 2.04/1.26  Reduction            : 0.07
% 2.04/1.26  Demodulation         : 0.06
% 2.04/1.26  BG Simplification    : 0.01
% 2.04/1.26  Subsumption          : 0.02
% 2.04/1.26  Abstraction          : 0.01
% 2.04/1.26  MUC search           : 0.00
% 2.04/1.26  Cooper               : 0.00
% 2.04/1.26  Total                : 0.49
% 2.04/1.26  Index Insertion      : 0.00
% 2.04/1.26  Index Deletion       : 0.00
% 2.04/1.26  Index Matching       : 0.00
% 2.04/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
