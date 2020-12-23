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
% DateTime   : Thu Dec  3 09:47:50 EST 2020

% Result     : Theorem 1.75s
% Output     : CNFRefutation 1.75s
% Verified   : 
% Statistics : Number of formulae       :   35 (  39 expanded)
%              Number of leaves         :   20 (  22 expanded)
%              Depth                    :    9
%              Number of atoms          :   22 (  26 expanded)
%              Number of equality atoms :   10 (  14 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_33,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_tarski(E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_42,negated_conjecture,(
    ~ ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(c_6,plain,(
    ! [A_8] : k2_tarski(A_8,A_8) = k1_tarski(A_8) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_9,B_10] : k1_enumset1(A_9,A_9,B_10) = k2_tarski(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_11,B_12,C_13] : k2_enumset1(A_11,A_11,B_12,C_13) = k1_enumset1(A_11,B_12,C_13) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_14,B_15,C_16,D_17] : k3_enumset1(A_14,A_14,B_15,C_16,D_17) = k2_enumset1(A_14,B_15,C_16,D_17) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_63,plain,(
    ! [D_41,A_42,C_43,E_40,B_44] : k2_xboole_0(k2_enumset1(A_42,B_44,C_43,D_41),k1_tarski(E_40)) = k3_enumset1(A_42,B_44,C_43,D_41,E_40) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(A_1,k2_xboole_0(A_1,B_2)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_79,plain,(
    ! [A_46,E_48,B_47,D_49,C_45] : r1_tarski(k2_enumset1(A_46,B_47,C_45,D_49),k3_enumset1(A_46,B_47,C_45,D_49,E_48)) ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_2])).

tff(c_82,plain,(
    ! [A_14,B_15,C_16,D_17] : r1_tarski(k2_enumset1(A_14,A_14,B_15,C_16),k2_enumset1(A_14,B_15,C_16,D_17)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_79])).

tff(c_88,plain,(
    ! [A_50,B_51,C_52,D_53] : r1_tarski(k1_enumset1(A_50,B_51,C_52),k2_enumset1(A_50,B_51,C_52,D_53)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_82])).

tff(c_91,plain,(
    ! [A_11,B_12,C_13] : r1_tarski(k1_enumset1(A_11,A_11,B_12),k1_enumset1(A_11,B_12,C_13)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_88])).

tff(c_97,plain,(
    ! [A_54,B_55,C_56] : r1_tarski(k2_tarski(A_54,B_55),k1_enumset1(A_54,B_55,C_56)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_91])).

tff(c_100,plain,(
    ! [A_9,B_10] : r1_tarski(k2_tarski(A_9,A_9),k2_tarski(A_9,B_10)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_97])).

tff(c_104,plain,(
    ! [A_9,B_10] : r1_tarski(k1_tarski(A_9),k2_tarski(A_9,B_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_100])).

tff(c_16,plain,(
    ~ r1_tarski(k1_tarski('#skF_1'),k2_tarski('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_108,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n014.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 17:02:37 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.75/1.13  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.75/1.14  
% 1.75/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.75/1.14  %$ r1_tarski > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1
% 1.75/1.14  
% 1.75/1.14  %Foreground sorts:
% 1.75/1.14  
% 1.75/1.14  
% 1.75/1.14  %Background operators:
% 1.75/1.14  
% 1.75/1.14  
% 1.75/1.14  %Foreground operators:
% 1.75/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.75/1.14  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.75/1.14  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.75/1.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.75/1.14  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.75/1.14  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.75/1.14  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.75/1.14  tff('#skF_2', type, '#skF_2': $i).
% 1.75/1.14  tff('#skF_1', type, '#skF_1': $i).
% 1.75/1.14  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.75/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.75/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.75/1.14  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.75/1.14  
% 1.75/1.15  tff(f_31, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.75/1.15  tff(f_33, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 1.75/1.15  tff(f_35, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 1.75/1.15  tff(f_37, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 1.75/1.15  tff(f_29, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_tarski(E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_enumset1)).
% 1.75/1.15  tff(f_27, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.75/1.15  tff(f_42, negated_conjecture, ~(![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 1.75/1.15  tff(c_6, plain, (![A_8]: (k2_tarski(A_8, A_8)=k1_tarski(A_8))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.75/1.15  tff(c_8, plain, (![A_9, B_10]: (k1_enumset1(A_9, A_9, B_10)=k2_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.75/1.15  tff(c_10, plain, (![A_11, B_12, C_13]: (k2_enumset1(A_11, A_11, B_12, C_13)=k1_enumset1(A_11, B_12, C_13))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.75/1.15  tff(c_12, plain, (![A_14, B_15, C_16, D_17]: (k3_enumset1(A_14, A_14, B_15, C_16, D_17)=k2_enumset1(A_14, B_15, C_16, D_17))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.75/1.15  tff(c_63, plain, (![D_41, A_42, C_43, E_40, B_44]: (k2_xboole_0(k2_enumset1(A_42, B_44, C_43, D_41), k1_tarski(E_40))=k3_enumset1(A_42, B_44, C_43, D_41, E_40))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.75/1.15  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, k2_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.75/1.15  tff(c_79, plain, (![A_46, E_48, B_47, D_49, C_45]: (r1_tarski(k2_enumset1(A_46, B_47, C_45, D_49), k3_enumset1(A_46, B_47, C_45, D_49, E_48)))), inference(superposition, [status(thm), theory('equality')], [c_63, c_2])).
% 1.75/1.15  tff(c_82, plain, (![A_14, B_15, C_16, D_17]: (r1_tarski(k2_enumset1(A_14, A_14, B_15, C_16), k2_enumset1(A_14, B_15, C_16, D_17)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_79])).
% 1.75/1.15  tff(c_88, plain, (![A_50, B_51, C_52, D_53]: (r1_tarski(k1_enumset1(A_50, B_51, C_52), k2_enumset1(A_50, B_51, C_52, D_53)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_82])).
% 1.75/1.15  tff(c_91, plain, (![A_11, B_12, C_13]: (r1_tarski(k1_enumset1(A_11, A_11, B_12), k1_enumset1(A_11, B_12, C_13)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_88])).
% 1.75/1.15  tff(c_97, plain, (![A_54, B_55, C_56]: (r1_tarski(k2_tarski(A_54, B_55), k1_enumset1(A_54, B_55, C_56)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_91])).
% 1.75/1.15  tff(c_100, plain, (![A_9, B_10]: (r1_tarski(k2_tarski(A_9, A_9), k2_tarski(A_9, B_10)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_97])).
% 1.75/1.15  tff(c_104, plain, (![A_9, B_10]: (r1_tarski(k1_tarski(A_9), k2_tarski(A_9, B_10)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_100])).
% 1.75/1.15  tff(c_16, plain, (~r1_tarski(k1_tarski('#skF_1'), k2_tarski('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.75/1.15  tff(c_108, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_104, c_16])).
% 1.75/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.75/1.15  
% 1.75/1.15  Inference rules
% 1.75/1.15  ----------------------
% 1.75/1.15  #Ref     : 0
% 1.75/1.15  #Sup     : 20
% 1.75/1.15  #Fact    : 0
% 1.75/1.15  #Define  : 0
% 1.75/1.15  #Split   : 0
% 1.75/1.15  #Chain   : 0
% 1.75/1.15  #Close   : 0
% 1.75/1.15  
% 1.75/1.15  Ordering : KBO
% 1.75/1.15  
% 1.75/1.15  Simplification rules
% 1.75/1.15  ----------------------
% 1.75/1.15  #Subsume      : 0
% 1.75/1.15  #Demod        : 8
% 1.75/1.15  #Tautology    : 12
% 1.75/1.15  #SimpNegUnit  : 0
% 1.75/1.15  #BackRed      : 1
% 1.75/1.15  
% 1.75/1.15  #Partial instantiations: 0
% 1.75/1.15  #Strategies tried      : 1
% 1.75/1.15  
% 1.75/1.15  Timing (in seconds)
% 1.75/1.15  ----------------------
% 1.75/1.15  Preprocessing        : 0.27
% 1.75/1.15  Parsing              : 0.14
% 1.75/1.15  CNF conversion       : 0.01
% 1.75/1.15  Main loop            : 0.10
% 1.75/1.15  Inferencing          : 0.04
% 1.75/1.15  Reduction            : 0.03
% 1.75/1.15  Demodulation         : 0.03
% 1.75/1.15  BG Simplification    : 0.01
% 1.75/1.15  Subsumption          : 0.01
% 1.75/1.15  Abstraction          : 0.01
% 1.75/1.15  MUC search           : 0.00
% 1.75/1.15  Cooper               : 0.00
% 1.75/1.15  Total                : 0.40
% 1.75/1.15  Index Insertion      : 0.00
% 1.75/1.15  Index Deletion       : 0.00
% 1.75/1.15  Index Matching       : 0.00
% 1.75/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
