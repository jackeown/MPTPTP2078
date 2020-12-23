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
% DateTime   : Thu Dec  3 09:47:49 EST 2020

% Result     : Theorem 1.73s
% Output     : CNFRefutation 1.77s
% Verified   : 
% Statistics : Number of formulae       :   29 (  29 expanded)
%              Number of leaves         :   18 (  18 expanded)
%              Depth                    :    6
%              Number of atoms          :   17 (  17 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_33,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_tarski(A),k2_enumset1(B,C,D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_40,negated_conjecture,(
    ~ ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(c_8,plain,(
    ! [A_9,B_10] : k1_enumset1(A_9,A_9,B_10) = k2_tarski(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_11,B_12,C_13] : k2_enumset1(A_11,A_11,B_12,C_13) = k1_enumset1(A_11,B_12,C_13) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_14,B_15,C_16,D_17] : k3_enumset1(A_14,A_14,B_15,C_16,D_17) = k2_enumset1(A_14,B_15,C_16,D_17) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_52,plain,(
    ! [C_33,D_31,E_30,B_34,A_32] : k2_xboole_0(k1_tarski(A_32),k2_enumset1(B_34,C_33,D_31,E_30)) = k3_enumset1(A_32,B_34,C_33,D_31,E_30) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(A_1,k2_xboole_0(A_1,B_2)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_67,plain,(
    ! [A_35,B_38,D_37,E_39,C_36] : r1_tarski(k1_tarski(A_35),k3_enumset1(A_35,B_38,C_36,D_37,E_39)) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_2])).

tff(c_71,plain,(
    ! [A_40,B_41,C_42,D_43] : r1_tarski(k1_tarski(A_40),k2_enumset1(A_40,B_41,C_42,D_43)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_67])).

tff(c_75,plain,(
    ! [A_44,B_45,C_46] : r1_tarski(k1_tarski(A_44),k1_enumset1(A_44,B_45,C_46)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_71])).

tff(c_78,plain,(
    ! [A_9,B_10] : r1_tarski(k1_tarski(A_9),k2_tarski(A_9,B_10)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_75])).

tff(c_14,plain,(
    ~ r1_tarski(k1_tarski('#skF_1'),k2_tarski('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_81,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:45:00 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.73/1.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.73/1.15  
% 1.73/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.73/1.15  %$ r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1
% 1.73/1.15  
% 1.73/1.15  %Foreground sorts:
% 1.73/1.15  
% 1.73/1.15  
% 1.73/1.15  %Background operators:
% 1.73/1.15  
% 1.73/1.15  
% 1.73/1.15  %Foreground operators:
% 1.73/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.73/1.15  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.73/1.15  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.73/1.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.73/1.15  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.73/1.15  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.73/1.15  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.73/1.15  tff('#skF_2', type, '#skF_2': $i).
% 1.73/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.73/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.73/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.73/1.15  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.73/1.15  
% 1.73/1.17  tff(f_33, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 1.73/1.17  tff(f_35, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 1.73/1.17  tff(f_37, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 1.73/1.17  tff(f_29, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_tarski(A), k2_enumset1(B, C, D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_enumset1)).
% 1.73/1.17  tff(f_27, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.73/1.17  tff(f_40, negated_conjecture, ~(![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 1.73/1.17  tff(c_8, plain, (![A_9, B_10]: (k1_enumset1(A_9, A_9, B_10)=k2_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.73/1.17  tff(c_10, plain, (![A_11, B_12, C_13]: (k2_enumset1(A_11, A_11, B_12, C_13)=k1_enumset1(A_11, B_12, C_13))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.73/1.17  tff(c_12, plain, (![A_14, B_15, C_16, D_17]: (k3_enumset1(A_14, A_14, B_15, C_16, D_17)=k2_enumset1(A_14, B_15, C_16, D_17))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.73/1.17  tff(c_52, plain, (![C_33, D_31, E_30, B_34, A_32]: (k2_xboole_0(k1_tarski(A_32), k2_enumset1(B_34, C_33, D_31, E_30))=k3_enumset1(A_32, B_34, C_33, D_31, E_30))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.73/1.17  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, k2_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.73/1.17  tff(c_67, plain, (![A_35, B_38, D_37, E_39, C_36]: (r1_tarski(k1_tarski(A_35), k3_enumset1(A_35, B_38, C_36, D_37, E_39)))), inference(superposition, [status(thm), theory('equality')], [c_52, c_2])).
% 1.73/1.17  tff(c_71, plain, (![A_40, B_41, C_42, D_43]: (r1_tarski(k1_tarski(A_40), k2_enumset1(A_40, B_41, C_42, D_43)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_67])).
% 1.77/1.17  tff(c_75, plain, (![A_44, B_45, C_46]: (r1_tarski(k1_tarski(A_44), k1_enumset1(A_44, B_45, C_46)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_71])).
% 1.77/1.17  tff(c_78, plain, (![A_9, B_10]: (r1_tarski(k1_tarski(A_9), k2_tarski(A_9, B_10)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_75])).
% 1.77/1.17  tff(c_14, plain, (~r1_tarski(k1_tarski('#skF_1'), k2_tarski('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.77/1.17  tff(c_81, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_14])).
% 1.77/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.77/1.17  
% 1.77/1.17  Inference rules
% 1.77/1.17  ----------------------
% 1.77/1.17  #Ref     : 0
% 1.77/1.17  #Sup     : 15
% 1.77/1.17  #Fact    : 0
% 1.77/1.17  #Define  : 0
% 1.77/1.17  #Split   : 0
% 1.77/1.17  #Chain   : 0
% 1.77/1.17  #Close   : 0
% 1.77/1.17  
% 1.77/1.17  Ordering : KBO
% 1.77/1.17  
% 1.77/1.17  Simplification rules
% 1.77/1.17  ----------------------
% 1.77/1.17  #Subsume      : 0
% 1.77/1.17  #Demod        : 1
% 1.77/1.17  #Tautology    : 10
% 1.77/1.17  #SimpNegUnit  : 0
% 1.77/1.17  #BackRed      : 1
% 1.77/1.17  
% 1.77/1.17  #Partial instantiations: 0
% 1.77/1.17  #Strategies tried      : 1
% 1.77/1.17  
% 1.77/1.17  Timing (in seconds)
% 1.77/1.17  ----------------------
% 1.77/1.18  Preprocessing        : 0.26
% 1.77/1.18  Parsing              : 0.14
% 1.77/1.18  CNF conversion       : 0.01
% 1.77/1.18  Main loop            : 0.12
% 1.77/1.18  Inferencing          : 0.06
% 1.77/1.18  Reduction            : 0.04
% 1.77/1.18  Demodulation         : 0.03
% 1.77/1.18  BG Simplification    : 0.01
% 1.77/1.18  Subsumption          : 0.01
% 1.77/1.18  Abstraction          : 0.01
% 1.77/1.18  MUC search           : 0.00
% 1.77/1.18  Cooper               : 0.00
% 1.77/1.18  Total                : 0.41
% 1.77/1.18  Index Insertion      : 0.00
% 1.77/1.18  Index Deletion       : 0.00
% 1.77/1.18  Index Matching       : 0.00
% 1.77/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
