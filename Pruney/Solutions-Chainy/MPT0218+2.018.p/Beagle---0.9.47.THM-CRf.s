%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:48 EST 2020

% Result     : Theorem 1.69s
% Output     : CNFRefutation 1.69s
% Verified   : 
% Statistics : Number of formulae       :   37 (  41 expanded)
%              Number of leaves         :   22 (  24 expanded)
%              Depth                    :    9
%              Number of atoms          :   22 (  26 expanded)
%              Number of equality atoms :   10 (  14 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1

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

tff(f_35,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_37,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_tarski(E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_enumset1)).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_44,negated_conjecture,(
    ~ ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(c_10,plain,(
    ! [A_12] : k2_tarski(A_12,A_12) = k1_tarski(A_12) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_13,B_14] : k1_enumset1(A_13,A_13,B_14) = k2_tarski(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [A_15,B_16,C_17] : k2_enumset1(A_15,A_15,B_16,C_17) = k1_enumset1(A_15,B_16,C_17) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ! [A_18,B_19,C_20,D_21] : k3_enumset1(A_18,A_18,B_19,C_20,D_21) = k2_enumset1(A_18,B_19,C_20,D_21) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_74,plain,(
    ! [B_39,D_38,A_41,E_42,C_40] : k2_xboole_0(k2_enumset1(A_41,B_39,C_40,D_38),k1_tarski(E_42)) = k3_enumset1(A_41,B_39,C_40,D_38,E_42) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(A_3,k2_xboole_0(A_3,B_4)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_90,plain,(
    ! [C_46,A_43,E_45,D_47,B_44] : r1_tarski(k2_enumset1(A_43,B_44,C_46,D_47),k3_enumset1(A_43,B_44,C_46,D_47,E_45)) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_4])).

tff(c_93,plain,(
    ! [A_18,B_19,C_20,D_21] : r1_tarski(k2_enumset1(A_18,A_18,B_19,C_20),k2_enumset1(A_18,B_19,C_20,D_21)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_90])).

tff(c_99,plain,(
    ! [A_48,B_49,C_50,D_51] : r1_tarski(k1_enumset1(A_48,B_49,C_50),k2_enumset1(A_48,B_49,C_50,D_51)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_93])).

tff(c_102,plain,(
    ! [A_15,B_16,C_17] : r1_tarski(k1_enumset1(A_15,A_15,B_16),k1_enumset1(A_15,B_16,C_17)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_99])).

tff(c_108,plain,(
    ! [A_52,B_53,C_54] : r1_tarski(k2_tarski(A_52,B_53),k1_enumset1(A_52,B_53,C_54)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_102])).

tff(c_111,plain,(
    ! [A_13,B_14] : r1_tarski(k2_tarski(A_13,A_13),k2_tarski(A_13,B_14)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_108])).

tff(c_115,plain,(
    ! [A_13,B_14] : r1_tarski(k1_tarski(A_13),k2_tarski(A_13,B_14)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_111])).

tff(c_18,plain,(
    ~ r1_tarski(k1_tarski('#skF_1'),k2_tarski('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_119,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:15:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.69/1.11  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.69/1.11  
% 1.69/1.11  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.69/1.12  %$ r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1
% 1.69/1.12  
% 1.69/1.12  %Foreground sorts:
% 1.69/1.12  
% 1.69/1.12  
% 1.69/1.12  %Background operators:
% 1.69/1.12  
% 1.69/1.12  
% 1.69/1.12  %Foreground operators:
% 1.69/1.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.69/1.12  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.69/1.12  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.69/1.12  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.69/1.12  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.69/1.12  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.69/1.12  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.69/1.12  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.69/1.12  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.69/1.12  tff('#skF_2', type, '#skF_2': $i).
% 1.69/1.12  tff('#skF_1', type, '#skF_1': $i).
% 1.69/1.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.69/1.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.69/1.12  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.69/1.12  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.69/1.12  
% 1.69/1.13  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.69/1.13  tff(f_37, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 1.69/1.13  tff(f_39, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 1.69/1.13  tff(f_41, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 1.69/1.13  tff(f_33, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_tarski(E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_enumset1)).
% 1.69/1.13  tff(f_29, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.69/1.13  tff(f_44, negated_conjecture, ~(![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 1.69/1.13  tff(c_10, plain, (![A_12]: (k2_tarski(A_12, A_12)=k1_tarski(A_12))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.69/1.13  tff(c_12, plain, (![A_13, B_14]: (k1_enumset1(A_13, A_13, B_14)=k2_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.69/1.13  tff(c_14, plain, (![A_15, B_16, C_17]: (k2_enumset1(A_15, A_15, B_16, C_17)=k1_enumset1(A_15, B_16, C_17))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.69/1.13  tff(c_16, plain, (![A_18, B_19, C_20, D_21]: (k3_enumset1(A_18, A_18, B_19, C_20, D_21)=k2_enumset1(A_18, B_19, C_20, D_21))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.69/1.13  tff(c_74, plain, (![B_39, D_38, A_41, E_42, C_40]: (k2_xboole_0(k2_enumset1(A_41, B_39, C_40, D_38), k1_tarski(E_42))=k3_enumset1(A_41, B_39, C_40, D_38, E_42))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.69/1.13  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(A_3, k2_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.69/1.13  tff(c_90, plain, (![C_46, A_43, E_45, D_47, B_44]: (r1_tarski(k2_enumset1(A_43, B_44, C_46, D_47), k3_enumset1(A_43, B_44, C_46, D_47, E_45)))), inference(superposition, [status(thm), theory('equality')], [c_74, c_4])).
% 1.69/1.13  tff(c_93, plain, (![A_18, B_19, C_20, D_21]: (r1_tarski(k2_enumset1(A_18, A_18, B_19, C_20), k2_enumset1(A_18, B_19, C_20, D_21)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_90])).
% 1.69/1.13  tff(c_99, plain, (![A_48, B_49, C_50, D_51]: (r1_tarski(k1_enumset1(A_48, B_49, C_50), k2_enumset1(A_48, B_49, C_50, D_51)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_93])).
% 1.69/1.13  tff(c_102, plain, (![A_15, B_16, C_17]: (r1_tarski(k1_enumset1(A_15, A_15, B_16), k1_enumset1(A_15, B_16, C_17)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_99])).
% 1.69/1.13  tff(c_108, plain, (![A_52, B_53, C_54]: (r1_tarski(k2_tarski(A_52, B_53), k1_enumset1(A_52, B_53, C_54)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_102])).
% 1.69/1.13  tff(c_111, plain, (![A_13, B_14]: (r1_tarski(k2_tarski(A_13, A_13), k2_tarski(A_13, B_14)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_108])).
% 1.69/1.13  tff(c_115, plain, (![A_13, B_14]: (r1_tarski(k1_tarski(A_13), k2_tarski(A_13, B_14)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_111])).
% 1.69/1.13  tff(c_18, plain, (~r1_tarski(k1_tarski('#skF_1'), k2_tarski('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.69/1.13  tff(c_119, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_115, c_18])).
% 1.69/1.13  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.69/1.13  
% 1.69/1.13  Inference rules
% 1.69/1.13  ----------------------
% 1.69/1.13  #Ref     : 0
% 1.69/1.13  #Sup     : 22
% 1.69/1.13  #Fact    : 0
% 1.69/1.13  #Define  : 0
% 1.69/1.13  #Split   : 0
% 1.69/1.13  #Chain   : 0
% 1.69/1.13  #Close   : 0
% 1.69/1.13  
% 1.69/1.13  Ordering : KBO
% 1.69/1.13  
% 1.69/1.13  Simplification rules
% 1.69/1.13  ----------------------
% 1.69/1.13  #Subsume      : 0
% 1.69/1.13  #Demod        : 8
% 1.69/1.13  #Tautology    : 14
% 1.69/1.13  #SimpNegUnit  : 0
% 1.69/1.13  #BackRed      : 1
% 1.69/1.13  
% 1.69/1.13  #Partial instantiations: 0
% 1.69/1.13  #Strategies tried      : 1
% 1.69/1.13  
% 1.69/1.13  Timing (in seconds)
% 1.69/1.13  ----------------------
% 1.69/1.13  Preprocessing        : 0.28
% 1.69/1.13  Parsing              : 0.15
% 1.69/1.13  CNF conversion       : 0.02
% 1.69/1.13  Main loop            : 0.10
% 1.69/1.13  Inferencing          : 0.05
% 1.69/1.13  Reduction            : 0.03
% 1.69/1.13  Demodulation         : 0.03
% 1.69/1.13  BG Simplification    : 0.01
% 1.69/1.13  Subsumption          : 0.01
% 1.69/1.13  Abstraction          : 0.01
% 1.69/1.13  MUC search           : 0.00
% 1.69/1.13  Cooper               : 0.00
% 1.69/1.13  Total                : 0.40
% 1.69/1.13  Index Insertion      : 0.00
% 1.69/1.13  Index Deletion       : 0.00
% 1.69/1.13  Index Matching       : 0.00
% 1.69/1.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
