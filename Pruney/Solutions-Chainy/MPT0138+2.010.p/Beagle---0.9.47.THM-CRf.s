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
% DateTime   : Thu Dec  3 09:45:46 EST 2020

% Result     : Theorem 1.92s
% Output     : CNFRefutation 1.92s
% Verified   : 
% Statistics : Number of formulae       :   37 (  40 expanded)
%              Number of leaves         :   23 (  25 expanded)
%              Depth                    :    6
%              Number of atoms          :   20 (  23 expanded)
%              Number of equality atoms :   19 (  22 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_enumset1 > k3_enumset1 > k2_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_tarski(A),k3_enumset1(B,C,D,E,F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_tarski(E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_tarski(A),k2_enumset1(B,C,D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_40,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k2_enumset1(A,B,C,D),k2_tarski(E,F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_enumset1)).

tff(c_12,plain,(
    ! [E_22,D_21,F_23,A_18,C_20,B_19] : k2_xboole_0(k1_tarski(A_18),k3_enumset1(B_19,C_20,D_21,E_22,F_23)) = k4_enumset1(A_18,B_19,C_20,D_21,E_22,F_23) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [E_17,A_13,B_14,C_15,D_16] : k2_xboole_0(k2_enumset1(A_13,B_14,C_15,D_16),k1_tarski(E_17)) = k3_enumset1(A_13,B_14,C_15,D_16,E_17) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_88,plain,(
    ! [D_41,B_39,A_37,C_40,E_38] : k2_xboole_0(k1_tarski(A_37),k2_enumset1(B_39,C_40,D_41,E_38)) = k3_enumset1(A_37,B_39,C_40,D_41,E_38) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_xboole_0(k2_xboole_0(A_1,B_2),C_3) = k2_xboole_0(A_1,k2_xboole_0(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_130,plain,(
    ! [C_56,A_53,E_54,C_57,B_55,D_58] : k2_xboole_0(k1_tarski(A_53),k2_xboole_0(k2_enumset1(B_55,C_56,D_58,E_54),C_57)) = k2_xboole_0(k3_enumset1(A_53,B_55,C_56,D_58,E_54),C_57) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_2])).

tff(c_145,plain,(
    ! [A_53,E_17,A_13,B_14,C_15,D_16] : k2_xboole_0(k3_enumset1(A_53,A_13,B_14,C_15,D_16),k1_tarski(E_17)) = k2_xboole_0(k1_tarski(A_53),k3_enumset1(A_13,B_14,C_15,D_16,E_17)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_130])).

tff(c_149,plain,(
    ! [A_53,E_17,A_13,B_14,C_15,D_16] : k2_xboole_0(k3_enumset1(A_53,A_13,B_14,C_15,D_16),k1_tarski(E_17)) = k4_enumset1(A_53,A_13,B_14,C_15,D_16,E_17) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_145])).

tff(c_6,plain,(
    ! [A_6,B_7] : k2_xboole_0(k1_tarski(A_6),k1_tarski(B_7)) = k2_tarski(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_103,plain,(
    ! [C_46,E_44,B_43,A_45,D_42] : k2_xboole_0(k2_enumset1(A_45,B_43,C_46,D_42),k1_tarski(E_44)) = k3_enumset1(A_45,B_43,C_46,D_42,E_44) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_194,plain,(
    ! [B_70,D_73,C_74,A_72,E_69,C_71] : k2_xboole_0(k2_enumset1(A_72,B_70,C_71,D_73),k2_xboole_0(k1_tarski(E_69),C_74)) = k2_xboole_0(k3_enumset1(A_72,B_70,C_71,D_73,E_69),C_74) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_2])).

tff(c_221,plain,(
    ! [B_7,B_70,D_73,A_72,C_71,A_6] : k2_xboole_0(k3_enumset1(A_72,B_70,C_71,D_73,A_6),k1_tarski(B_7)) = k2_xboole_0(k2_enumset1(A_72,B_70,C_71,D_73),k2_tarski(A_6,B_7)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_194])).

tff(c_225,plain,(
    ! [B_7,B_70,D_73,A_72,C_71,A_6] : k2_xboole_0(k2_enumset1(A_72,B_70,C_71,D_73),k2_tarski(A_6,B_7)) = k4_enumset1(A_72,B_70,C_71,D_73,A_6,B_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_221])).

tff(c_14,plain,(
    k2_xboole_0(k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4'),k2_tarski('#skF_5','#skF_6')) != k4_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_253,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_225,c_14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n011.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:30:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.92/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.92/1.22  
% 1.92/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.92/1.22  %$ k4_enumset1 > k3_enumset1 > k2_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.92/1.22  
% 1.92/1.22  %Foreground sorts:
% 1.92/1.22  
% 1.92/1.22  
% 1.92/1.22  %Background operators:
% 1.92/1.22  
% 1.92/1.22  
% 1.92/1.22  %Foreground operators:
% 1.92/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.92/1.22  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.92/1.22  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.92/1.22  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.92/1.22  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.92/1.22  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.92/1.22  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.92/1.22  tff('#skF_5', type, '#skF_5': $i).
% 1.92/1.22  tff('#skF_6', type, '#skF_6': $i).
% 1.92/1.22  tff('#skF_2', type, '#skF_2': $i).
% 1.92/1.22  tff('#skF_3', type, '#skF_3': $i).
% 1.92/1.22  tff('#skF_1', type, '#skF_1': $i).
% 1.92/1.22  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.92/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.92/1.22  tff('#skF_4', type, '#skF_4': $i).
% 1.92/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.92/1.22  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.92/1.22  
% 1.92/1.23  tff(f_37, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_tarski(A), k3_enumset1(B, C, D, E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_enumset1)).
% 1.92/1.23  tff(f_35, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_tarski(E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_enumset1)).
% 1.92/1.23  tff(f_33, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_tarski(A), k2_enumset1(B, C, D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_enumset1)).
% 1.92/1.23  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 1.92/1.23  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 1.92/1.23  tff(f_40, negated_conjecture, ~(![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k2_enumset1(A, B, C, D), k2_tarski(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_enumset1)).
% 1.92/1.23  tff(c_12, plain, (![E_22, D_21, F_23, A_18, C_20, B_19]: (k2_xboole_0(k1_tarski(A_18), k3_enumset1(B_19, C_20, D_21, E_22, F_23))=k4_enumset1(A_18, B_19, C_20, D_21, E_22, F_23))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.92/1.23  tff(c_10, plain, (![E_17, A_13, B_14, C_15, D_16]: (k2_xboole_0(k2_enumset1(A_13, B_14, C_15, D_16), k1_tarski(E_17))=k3_enumset1(A_13, B_14, C_15, D_16, E_17))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.92/1.23  tff(c_88, plain, (![D_41, B_39, A_37, C_40, E_38]: (k2_xboole_0(k1_tarski(A_37), k2_enumset1(B_39, C_40, D_41, E_38))=k3_enumset1(A_37, B_39, C_40, D_41, E_38))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.92/1.23  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_xboole_0(k2_xboole_0(A_1, B_2), C_3)=k2_xboole_0(A_1, k2_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.92/1.23  tff(c_130, plain, (![C_56, A_53, E_54, C_57, B_55, D_58]: (k2_xboole_0(k1_tarski(A_53), k2_xboole_0(k2_enumset1(B_55, C_56, D_58, E_54), C_57))=k2_xboole_0(k3_enumset1(A_53, B_55, C_56, D_58, E_54), C_57))), inference(superposition, [status(thm), theory('equality')], [c_88, c_2])).
% 1.92/1.23  tff(c_145, plain, (![A_53, E_17, A_13, B_14, C_15, D_16]: (k2_xboole_0(k3_enumset1(A_53, A_13, B_14, C_15, D_16), k1_tarski(E_17))=k2_xboole_0(k1_tarski(A_53), k3_enumset1(A_13, B_14, C_15, D_16, E_17)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_130])).
% 1.92/1.23  tff(c_149, plain, (![A_53, E_17, A_13, B_14, C_15, D_16]: (k2_xboole_0(k3_enumset1(A_53, A_13, B_14, C_15, D_16), k1_tarski(E_17))=k4_enumset1(A_53, A_13, B_14, C_15, D_16, E_17))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_145])).
% 1.92/1.23  tff(c_6, plain, (![A_6, B_7]: (k2_xboole_0(k1_tarski(A_6), k1_tarski(B_7))=k2_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.92/1.23  tff(c_103, plain, (![C_46, E_44, B_43, A_45, D_42]: (k2_xboole_0(k2_enumset1(A_45, B_43, C_46, D_42), k1_tarski(E_44))=k3_enumset1(A_45, B_43, C_46, D_42, E_44))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.92/1.23  tff(c_194, plain, (![B_70, D_73, C_74, A_72, E_69, C_71]: (k2_xboole_0(k2_enumset1(A_72, B_70, C_71, D_73), k2_xboole_0(k1_tarski(E_69), C_74))=k2_xboole_0(k3_enumset1(A_72, B_70, C_71, D_73, E_69), C_74))), inference(superposition, [status(thm), theory('equality')], [c_103, c_2])).
% 1.92/1.23  tff(c_221, plain, (![B_7, B_70, D_73, A_72, C_71, A_6]: (k2_xboole_0(k3_enumset1(A_72, B_70, C_71, D_73, A_6), k1_tarski(B_7))=k2_xboole_0(k2_enumset1(A_72, B_70, C_71, D_73), k2_tarski(A_6, B_7)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_194])).
% 1.92/1.23  tff(c_225, plain, (![B_7, B_70, D_73, A_72, C_71, A_6]: (k2_xboole_0(k2_enumset1(A_72, B_70, C_71, D_73), k2_tarski(A_6, B_7))=k4_enumset1(A_72, B_70, C_71, D_73, A_6, B_7))), inference(demodulation, [status(thm), theory('equality')], [c_149, c_221])).
% 1.92/1.23  tff(c_14, plain, (k2_xboole_0(k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k2_tarski('#skF_5', '#skF_6'))!=k4_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.92/1.23  tff(c_253, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_225, c_14])).
% 1.92/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.92/1.23  
% 1.92/1.23  Inference rules
% 1.92/1.23  ----------------------
% 1.92/1.23  #Ref     : 0
% 1.92/1.23  #Sup     : 61
% 1.92/1.23  #Fact    : 0
% 1.92/1.23  #Define  : 0
% 1.92/1.23  #Split   : 0
% 1.92/1.23  #Chain   : 0
% 1.92/1.23  #Close   : 0
% 1.92/1.23  
% 1.92/1.23  Ordering : KBO
% 1.92/1.23  
% 1.92/1.23  Simplification rules
% 1.92/1.23  ----------------------
% 1.92/1.23  #Subsume      : 0
% 1.92/1.23  #Demod        : 32
% 1.92/1.23  #Tautology    : 37
% 1.92/1.23  #SimpNegUnit  : 0
% 1.92/1.23  #BackRed      : 1
% 1.92/1.23  
% 1.92/1.23  #Partial instantiations: 0
% 1.92/1.23  #Strategies tried      : 1
% 1.92/1.23  
% 1.92/1.23  Timing (in seconds)
% 1.92/1.23  ----------------------
% 1.92/1.23  Preprocessing        : 0.27
% 1.92/1.23  Parsing              : 0.15
% 1.92/1.23  CNF conversion       : 0.02
% 1.92/1.23  Main loop            : 0.21
% 1.92/1.23  Inferencing          : 0.10
% 1.92/1.23  Reduction            : 0.07
% 1.92/1.23  Demodulation         : 0.06
% 1.92/1.23  BG Simplification    : 0.02
% 1.92/1.23  Subsumption          : 0.02
% 1.92/1.23  Abstraction          : 0.02
% 1.92/1.23  MUC search           : 0.00
% 1.92/1.23  Cooper               : 0.00
% 1.92/1.23  Total                : 0.51
% 1.92/1.23  Index Insertion      : 0.00
% 1.92/1.23  Index Deletion       : 0.00
% 1.92/1.23  Index Matching       : 0.00
% 1.92/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
