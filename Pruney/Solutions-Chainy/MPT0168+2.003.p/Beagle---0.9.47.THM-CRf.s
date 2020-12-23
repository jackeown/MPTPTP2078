%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:27 EST 2020

% Result     : Theorem 1.62s
% Output     : CNFRefutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :   29 (  31 expanded)
%              Number of leaves         :   19 (  20 expanded)
%              Depth                    :    6
%              Number of atoms          :   15 (  17 expanded)
%              Number of equality atoms :   14 (  16 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_33,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_tarski(A),k3_enumset1(B,C,D,E,F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_enumset1)).

tff(f_40,negated_conjecture,(
    ~ ! [A,B,C] : k4_enumset1(A,A,A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_enumset1)).

tff(c_8,plain,(
    ! [A_12,B_13,C_14] : k2_enumset1(A_12,A_12,B_13,C_14) = k1_enumset1(A_12,B_13,C_14) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3,D_4] : k2_xboole_0(k1_tarski(A_1),k1_enumset1(B_2,C_3,D_4)) = k2_enumset1(A_1,B_2,C_3,D_4) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_15,B_16,C_17,D_18] : k3_enumset1(A_15,A_15,B_16,C_17,D_18) = k2_enumset1(A_15,B_16,C_17,D_18) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_60,plain,(
    ! [C_46,A_47,E_48,F_44,B_45,D_43] : k2_xboole_0(k1_tarski(A_47),k3_enumset1(B_45,C_46,D_43,E_48,F_44)) = k4_enumset1(A_47,B_45,C_46,D_43,E_48,F_44) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_72,plain,(
    ! [B_52,A_53,D_51,C_50,A_49] : k4_enumset1(A_49,A_53,A_53,B_52,C_50,D_51) = k2_xboole_0(k1_tarski(A_49),k2_enumset1(A_53,B_52,C_50,D_51)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_60])).

tff(c_87,plain,(
    ! [A_49,A_12,B_13,C_14] : k4_enumset1(A_49,A_12,A_12,A_12,B_13,C_14) = k2_xboole_0(k1_tarski(A_49),k1_enumset1(A_12,B_13,C_14)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_72])).

tff(c_92,plain,(
    ! [A_49,A_12,B_13,C_14] : k4_enumset1(A_49,A_12,A_12,A_12,B_13,C_14) = k2_enumset1(A_49,A_12,B_13,C_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_87])).

tff(c_14,plain,(
    k4_enumset1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_93,plain,(
    k2_enumset1('#skF_1','#skF_1','#skF_2','#skF_3') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_14])).

tff(c_96,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_93])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:20:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.62/1.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.62/1.15  
% 1.62/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.62/1.15  %$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 1.62/1.15  
% 1.62/1.15  %Foreground sorts:
% 1.62/1.15  
% 1.62/1.15  
% 1.62/1.15  %Background operators:
% 1.62/1.15  
% 1.62/1.15  
% 1.62/1.15  %Foreground operators:
% 1.62/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.62/1.15  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.62/1.15  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.62/1.15  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.62/1.15  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.62/1.15  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.62/1.15  tff('#skF_2', type, '#skF_2': $i).
% 1.62/1.15  tff('#skF_3', type, '#skF_3': $i).
% 1.62/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.62/1.15  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.62/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.62/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.62/1.15  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.62/1.15  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.62/1.15  
% 1.62/1.16  tff(f_33, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 1.62/1.16  tff(f_27, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_enumset1)).
% 1.62/1.16  tff(f_35, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 1.62/1.16  tff(f_29, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_tarski(A), k3_enumset1(B, C, D, E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_enumset1)).
% 1.62/1.16  tff(f_40, negated_conjecture, ~(![A, B, C]: (k4_enumset1(A, A, A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_enumset1)).
% 1.62/1.16  tff(c_8, plain, (![A_12, B_13, C_14]: (k2_enumset1(A_12, A_12, B_13, C_14)=k1_enumset1(A_12, B_13, C_14))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.62/1.16  tff(c_2, plain, (![A_1, B_2, C_3, D_4]: (k2_xboole_0(k1_tarski(A_1), k1_enumset1(B_2, C_3, D_4))=k2_enumset1(A_1, B_2, C_3, D_4))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.62/1.16  tff(c_10, plain, (![A_15, B_16, C_17, D_18]: (k3_enumset1(A_15, A_15, B_16, C_17, D_18)=k2_enumset1(A_15, B_16, C_17, D_18))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.62/1.16  tff(c_60, plain, (![C_46, A_47, E_48, F_44, B_45, D_43]: (k2_xboole_0(k1_tarski(A_47), k3_enumset1(B_45, C_46, D_43, E_48, F_44))=k4_enumset1(A_47, B_45, C_46, D_43, E_48, F_44))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.62/1.16  tff(c_72, plain, (![B_52, A_53, D_51, C_50, A_49]: (k4_enumset1(A_49, A_53, A_53, B_52, C_50, D_51)=k2_xboole_0(k1_tarski(A_49), k2_enumset1(A_53, B_52, C_50, D_51)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_60])).
% 1.62/1.16  tff(c_87, plain, (![A_49, A_12, B_13, C_14]: (k4_enumset1(A_49, A_12, A_12, A_12, B_13, C_14)=k2_xboole_0(k1_tarski(A_49), k1_enumset1(A_12, B_13, C_14)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_72])).
% 1.62/1.16  tff(c_92, plain, (![A_49, A_12, B_13, C_14]: (k4_enumset1(A_49, A_12, A_12, A_12, B_13, C_14)=k2_enumset1(A_49, A_12, B_13, C_14))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_87])).
% 1.62/1.16  tff(c_14, plain, (k4_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.62/1.16  tff(c_93, plain, (k2_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_14])).
% 1.62/1.16  tff(c_96, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_93])).
% 1.62/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.62/1.16  
% 1.62/1.16  Inference rules
% 1.62/1.16  ----------------------
% 1.62/1.16  #Ref     : 0
% 1.62/1.16  #Sup     : 18
% 1.62/1.16  #Fact    : 0
% 1.62/1.16  #Define  : 0
% 1.62/1.16  #Split   : 0
% 1.62/1.16  #Chain   : 0
% 1.62/1.16  #Close   : 0
% 1.62/1.16  
% 1.62/1.16  Ordering : KBO
% 1.62/1.16  
% 1.62/1.16  Simplification rules
% 1.62/1.16  ----------------------
% 1.62/1.16  #Subsume      : 0
% 1.62/1.16  #Demod        : 3
% 1.62/1.16  #Tautology    : 16
% 1.62/1.16  #SimpNegUnit  : 0
% 1.62/1.16  #BackRed      : 1
% 1.62/1.16  
% 1.62/1.16  #Partial instantiations: 0
% 1.62/1.16  #Strategies tried      : 1
% 1.62/1.16  
% 1.62/1.16  Timing (in seconds)
% 1.62/1.16  ----------------------
% 1.62/1.16  Preprocessing        : 0.27
% 1.62/1.16  Parsing              : 0.14
% 1.62/1.16  CNF conversion       : 0.02
% 1.62/1.16  Main loop            : 0.10
% 1.62/1.16  Inferencing          : 0.05
% 1.62/1.16  Reduction            : 0.03
% 1.62/1.16  Demodulation         : 0.02
% 1.62/1.16  BG Simplification    : 0.01
% 1.62/1.16  Subsumption          : 0.01
% 1.62/1.16  Abstraction          : 0.01
% 1.62/1.16  MUC search           : 0.00
% 1.62/1.17  Cooper               : 0.00
% 1.62/1.17  Total                : 0.39
% 1.62/1.17  Index Insertion      : 0.00
% 1.62/1.17  Index Deletion       : 0.00
% 1.62/1.17  Index Matching       : 0.00
% 1.62/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
