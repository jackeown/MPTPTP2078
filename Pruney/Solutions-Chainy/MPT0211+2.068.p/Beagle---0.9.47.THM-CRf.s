%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:24 EST 2020

% Result     : Theorem 4.22s
% Output     : CNFRefutation 4.60s
% Verified   : 
% Statistics : Number of formulae       :   40 (  69 expanded)
%              Number of leaves         :   21 (  34 expanded)
%              Depth                    :    7
%              Number of atoms          :   26 (  55 expanded)
%              Number of equality atoms :   25 (  54 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_35,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,D,A,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,C,D,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_37,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_enumset1(A,B,C),k2_tarski(D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l57_enumset1)).

tff(f_44,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(B,A),k2_tarski(C,A)) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_enumset1)).

tff(c_10,plain,(
    ! [B_15,D_17,A_14,C_16] : k2_enumset1(B_15,D_17,A_14,C_16) = k2_enumset1(A_14,B_15,C_16,D_17) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14,plain,(
    ! [A_20,B_21,C_22] : k2_enumset1(A_20,A_20,B_21,C_22) = k1_enumset1(A_20,B_21,C_22) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_98,plain,(
    ! [A_40,C_41,D_42,B_43] : k2_enumset1(A_40,C_41,D_42,B_43) = k2_enumset1(A_40,B_43,C_41,D_42) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_237,plain,(
    ! [A_49,B_50,C_51] : k2_enumset1(A_49,B_50,C_51,A_49) = k1_enumset1(A_49,B_50,C_51) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_98])).

tff(c_602,plain,(
    ! [A_72,C_73,D_74] : k2_enumset1(A_72,C_73,C_73,D_74) = k1_enumset1(C_73,D_74,A_72) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_237])).

tff(c_55,plain,(
    ! [B_36,D_37,A_38,C_39] : k2_enumset1(B_36,D_37,A_38,C_39) = k2_enumset1(A_38,B_36,C_39,D_37) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_299,plain,(
    ! [A_52,D_53,C_54] : k2_enumset1(A_52,D_53,C_54,D_53) = k1_enumset1(D_53,A_52,C_54) ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_14])).

tff(c_8,plain,(
    ! [A_10,C_12,D_13,B_11] : k2_enumset1(A_10,C_12,D_13,B_11) = k2_enumset1(A_10,B_11,C_12,D_13) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_313,plain,(
    ! [A_52,D_53,C_54] : k2_enumset1(A_52,D_53,D_53,C_54) = k1_enumset1(D_53,A_52,C_54) ),
    inference(superposition,[status(thm),theory(equality)],[c_299,c_8])).

tff(c_612,plain,(
    ! [C_73,D_74,A_72] : k1_enumset1(C_73,D_74,A_72) = k1_enumset1(C_73,A_72,D_74) ),
    inference(superposition,[status(thm),theory(equality)],[c_602,c_313])).

tff(c_16,plain,(
    ! [A_23,B_24,C_25,D_26] : k3_enumset1(A_23,A_23,B_24,C_25,D_26) = k2_enumset1(A_23,B_24,C_25,D_26) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_12,plain,(
    ! [A_18,B_19] : k1_enumset1(A_18,A_18,B_19) = k2_tarski(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_410,plain,(
    ! [B_62,E_65,C_63,D_61,A_64] : k2_xboole_0(k1_enumset1(A_64,B_62,C_63),k2_tarski(D_61,E_65)) = k3_enumset1(A_64,B_62,C_63,D_61,E_65) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_428,plain,(
    ! [A_18,B_19,D_61,E_65] : k3_enumset1(A_18,A_18,B_19,D_61,E_65) = k2_xboole_0(k2_tarski(A_18,B_19),k2_tarski(D_61,E_65)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_410])).

tff(c_431,plain,(
    ! [A_18,B_19,D_61,E_65] : k2_xboole_0(k2_tarski(A_18,B_19),k2_tarski(D_61,E_65)) = k2_enumset1(A_18,B_19,D_61,E_65) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_428])).

tff(c_18,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_888,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_612,c_18])).

tff(c_3455,plain,(
    k2_enumset1('#skF_2','#skF_1','#skF_3','#skF_1') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_431,c_888])).

tff(c_3458,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_612,c_14,c_10,c_10,c_10,c_3455])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:46:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.22/1.78  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.54/1.78  
% 4.54/1.78  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.54/1.78  %$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1
% 4.54/1.78  
% 4.54/1.78  %Foreground sorts:
% 4.54/1.78  
% 4.54/1.78  
% 4.54/1.78  %Background operators:
% 4.54/1.78  
% 4.54/1.78  
% 4.54/1.78  %Foreground operators:
% 4.54/1.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.54/1.78  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.54/1.78  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.54/1.78  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.54/1.78  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.54/1.78  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.54/1.78  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.54/1.78  tff('#skF_2', type, '#skF_2': $i).
% 4.54/1.78  tff('#skF_3', type, '#skF_3': $i).
% 4.54/1.78  tff('#skF_1', type, '#skF_1': $i).
% 4.54/1.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.54/1.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.54/1.78  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.54/1.78  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.54/1.78  
% 4.60/1.79  tff(f_35, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, D, A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t112_enumset1)).
% 4.60/1.79  tff(f_39, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 4.60/1.79  tff(f_33, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, C, D, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t105_enumset1)).
% 4.60/1.79  tff(f_41, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 4.60/1.79  tff(f_37, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 4.60/1.79  tff(f_31, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_enumset1(A, B, C), k2_tarski(D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l57_enumset1)).
% 4.60/1.79  tff(f_44, negated_conjecture, ~(![A, B, C]: (k2_xboole_0(k2_tarski(B, A), k2_tarski(C, A)) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t137_enumset1)).
% 4.60/1.79  tff(c_10, plain, (![B_15, D_17, A_14, C_16]: (k2_enumset1(B_15, D_17, A_14, C_16)=k2_enumset1(A_14, B_15, C_16, D_17))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.60/1.79  tff(c_14, plain, (![A_20, B_21, C_22]: (k2_enumset1(A_20, A_20, B_21, C_22)=k1_enumset1(A_20, B_21, C_22))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.60/1.79  tff(c_98, plain, (![A_40, C_41, D_42, B_43]: (k2_enumset1(A_40, C_41, D_42, B_43)=k2_enumset1(A_40, B_43, C_41, D_42))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.60/1.79  tff(c_237, plain, (![A_49, B_50, C_51]: (k2_enumset1(A_49, B_50, C_51, A_49)=k1_enumset1(A_49, B_50, C_51))), inference(superposition, [status(thm), theory('equality')], [c_14, c_98])).
% 4.60/1.79  tff(c_602, plain, (![A_72, C_73, D_74]: (k2_enumset1(A_72, C_73, C_73, D_74)=k1_enumset1(C_73, D_74, A_72))), inference(superposition, [status(thm), theory('equality')], [c_10, c_237])).
% 4.60/1.79  tff(c_55, plain, (![B_36, D_37, A_38, C_39]: (k2_enumset1(B_36, D_37, A_38, C_39)=k2_enumset1(A_38, B_36, C_39, D_37))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.60/1.79  tff(c_299, plain, (![A_52, D_53, C_54]: (k2_enumset1(A_52, D_53, C_54, D_53)=k1_enumset1(D_53, A_52, C_54))), inference(superposition, [status(thm), theory('equality')], [c_55, c_14])).
% 4.60/1.79  tff(c_8, plain, (![A_10, C_12, D_13, B_11]: (k2_enumset1(A_10, C_12, D_13, B_11)=k2_enumset1(A_10, B_11, C_12, D_13))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.60/1.79  tff(c_313, plain, (![A_52, D_53, C_54]: (k2_enumset1(A_52, D_53, D_53, C_54)=k1_enumset1(D_53, A_52, C_54))), inference(superposition, [status(thm), theory('equality')], [c_299, c_8])).
% 4.60/1.79  tff(c_612, plain, (![C_73, D_74, A_72]: (k1_enumset1(C_73, D_74, A_72)=k1_enumset1(C_73, A_72, D_74))), inference(superposition, [status(thm), theory('equality')], [c_602, c_313])).
% 4.60/1.79  tff(c_16, plain, (![A_23, B_24, C_25, D_26]: (k3_enumset1(A_23, A_23, B_24, C_25, D_26)=k2_enumset1(A_23, B_24, C_25, D_26))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.60/1.79  tff(c_12, plain, (![A_18, B_19]: (k1_enumset1(A_18, A_18, B_19)=k2_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.60/1.79  tff(c_410, plain, (![B_62, E_65, C_63, D_61, A_64]: (k2_xboole_0(k1_enumset1(A_64, B_62, C_63), k2_tarski(D_61, E_65))=k3_enumset1(A_64, B_62, C_63, D_61, E_65))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.60/1.79  tff(c_428, plain, (![A_18, B_19, D_61, E_65]: (k3_enumset1(A_18, A_18, B_19, D_61, E_65)=k2_xboole_0(k2_tarski(A_18, B_19), k2_tarski(D_61, E_65)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_410])).
% 4.60/1.79  tff(c_431, plain, (![A_18, B_19, D_61, E_65]: (k2_xboole_0(k2_tarski(A_18, B_19), k2_tarski(D_61, E_65))=k2_enumset1(A_18, B_19, D_61, E_65))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_428])).
% 4.60/1.79  tff(c_18, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.60/1.79  tff(c_888, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_612, c_18])).
% 4.60/1.79  tff(c_3455, plain, (k2_enumset1('#skF_2', '#skF_1', '#skF_3', '#skF_1')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_431, c_888])).
% 4.60/1.79  tff(c_3458, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_612, c_14, c_10, c_10, c_10, c_3455])).
% 4.60/1.79  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.60/1.79  
% 4.60/1.79  Inference rules
% 4.60/1.79  ----------------------
% 4.60/1.79  #Ref     : 0
% 4.60/1.79  #Sup     : 848
% 4.60/1.79  #Fact    : 0
% 4.60/1.79  #Define  : 0
% 4.60/1.79  #Split   : 0
% 4.60/1.79  #Chain   : 0
% 4.60/1.79  #Close   : 0
% 4.60/1.79  
% 4.60/1.79  Ordering : KBO
% 4.60/1.79  
% 4.60/1.79  Simplification rules
% 4.60/1.79  ----------------------
% 4.60/1.79  #Subsume      : 127
% 4.60/1.79  #Demod        : 556
% 4.60/1.79  #Tautology    : 554
% 4.60/1.79  #SimpNegUnit  : 0
% 4.60/1.79  #BackRed      : 2
% 4.60/1.79  
% 4.60/1.79  #Partial instantiations: 0
% 4.60/1.79  #Strategies tried      : 1
% 4.60/1.79  
% 4.60/1.79  Timing (in seconds)
% 4.60/1.79  ----------------------
% 4.60/1.80  Preprocessing        : 0.27
% 4.60/1.80  Parsing              : 0.14
% 4.60/1.80  CNF conversion       : 0.01
% 4.60/1.80  Main loop            : 0.76
% 4.60/1.80  Inferencing          : 0.24
% 4.60/1.80  Reduction            : 0.37
% 4.60/1.80  Demodulation         : 0.33
% 4.60/1.80  BG Simplification    : 0.03
% 4.60/1.80  Subsumption          : 0.09
% 4.60/1.80  Abstraction          : 0.05
% 4.60/1.80  MUC search           : 0.00
% 4.60/1.80  Cooper               : 0.00
% 4.60/1.80  Total                : 1.06
% 4.60/1.80  Index Insertion      : 0.00
% 4.60/1.80  Index Deletion       : 0.00
% 4.60/1.80  Index Matching       : 0.00
% 4.60/1.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
