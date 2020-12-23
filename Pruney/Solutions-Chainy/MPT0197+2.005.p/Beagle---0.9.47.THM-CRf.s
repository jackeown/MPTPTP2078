%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:04 EST 2020

% Result     : Theorem 2.17s
% Output     : CNFRefutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :   28 (  34 expanded)
%              Number of leaves         :   16 (  19 expanded)
%              Depth                    :    6
%              Number of atoms          :   17 (  23 expanded)
%              Number of equality atoms :   16 (  22 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(C,B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_enumset1(A,B,C),k1_enumset1(D,E,F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D] : k4_enumset1(A,A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(C,B,A,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_enumset1)).

tff(f_36,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(C,D,A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_enumset1)).

tff(c_2,plain,(
    ! [C_3,B_2,A_1] : k1_enumset1(C_3,B_2,A_1) = k1_enumset1(A_1,B_2,C_3) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_87,plain,(
    ! [C_33,F_29,B_32,A_30,D_34,E_31] : k2_xboole_0(k1_enumset1(A_30,B_32,C_33),k1_enumset1(D_34,E_31,F_29)) = k4_enumset1(A_30,B_32,C_33,D_34,E_31,F_29) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_171,plain,(
    ! [C_51,B_47,C_48,B_50,A_52,A_49] : k2_xboole_0(k1_enumset1(A_49,B_47,C_48),k1_enumset1(C_51,B_50,A_52)) = k4_enumset1(A_49,B_47,C_48,A_52,B_50,C_51) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_87])).

tff(c_96,plain,(
    ! [F_29,B_2,C_3,A_1,D_34,E_31] : k2_xboole_0(k1_enumset1(C_3,B_2,A_1),k1_enumset1(D_34,E_31,F_29)) = k4_enumset1(A_1,B_2,C_3,D_34,E_31,F_29) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_87])).

tff(c_206,plain,(
    ! [A_58,B_56,C_57,A_55,C_53,B_54] : k4_enumset1(C_57,B_54,A_58,C_53,B_56,A_55) = k4_enumset1(A_58,B_54,C_57,A_55,B_56,C_53) ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_96])).

tff(c_8,plain,(
    ! [A_14,B_15,C_16,D_17] : k4_enumset1(A_14,A_14,A_14,B_15,C_16,D_17) = k2_enumset1(A_14,B_15,C_16,D_17) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_277,plain,(
    ! [C_59,C_60,B_61,A_62] : k4_enumset1(C_59,C_59,C_59,C_60,B_61,A_62) = k2_enumset1(C_59,A_62,B_61,C_60) ),
    inference(superposition,[status(thm),theory(equality)],[c_206,c_8])).

tff(c_289,plain,(
    ! [C_59,C_60,B_61,A_62] : k2_enumset1(C_59,C_60,B_61,A_62) = k2_enumset1(C_59,A_62,B_61,C_60) ),
    inference(superposition,[status(thm),theory(equality)],[c_277,c_8])).

tff(c_4,plain,(
    ! [C_6,B_5,A_4,D_7] : k2_enumset1(C_6,B_5,A_4,D_7) = k2_enumset1(A_4,B_5,C_6,D_7) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_10,plain,(
    k2_enumset1('#skF_3','#skF_4','#skF_1','#skF_2') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_11,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_4','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_10])).

tff(c_312,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_289,c_11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:15:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.17/1.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.23  
% 2.17/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.23  %$ k4_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.17/1.23  
% 2.17/1.23  %Foreground sorts:
% 2.17/1.23  
% 2.17/1.23  
% 2.17/1.23  %Background operators:
% 2.17/1.23  
% 2.17/1.23  
% 2.17/1.23  %Foreground operators:
% 2.17/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.17/1.23  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.17/1.23  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.17/1.23  tff('#skF_2', type, '#skF_2': $i).
% 2.17/1.23  tff('#skF_3', type, '#skF_3': $i).
% 2.17/1.23  tff('#skF_1', type, '#skF_1': $i).
% 2.17/1.23  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.17/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.17/1.23  tff('#skF_4', type, '#skF_4': $i).
% 2.17/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.17/1.23  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.17/1.23  
% 2.21/1.24  tff(f_27, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(C, B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t102_enumset1)).
% 2.21/1.24  tff(f_31, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_enumset1(A, B, C), k1_enumset1(D, E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_enumset1)).
% 2.21/1.24  tff(f_33, axiom, (![A, B, C, D]: (k4_enumset1(A, A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_enumset1)).
% 2.21/1.24  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(C, B, A, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t116_enumset1)).
% 2.21/1.24  tff(f_36, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(C, D, A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t118_enumset1)).
% 2.21/1.24  tff(c_2, plain, (![C_3, B_2, A_1]: (k1_enumset1(C_3, B_2, A_1)=k1_enumset1(A_1, B_2, C_3))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.21/1.24  tff(c_87, plain, (![C_33, F_29, B_32, A_30, D_34, E_31]: (k2_xboole_0(k1_enumset1(A_30, B_32, C_33), k1_enumset1(D_34, E_31, F_29))=k4_enumset1(A_30, B_32, C_33, D_34, E_31, F_29))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.21/1.24  tff(c_171, plain, (![C_51, B_47, C_48, B_50, A_52, A_49]: (k2_xboole_0(k1_enumset1(A_49, B_47, C_48), k1_enumset1(C_51, B_50, A_52))=k4_enumset1(A_49, B_47, C_48, A_52, B_50, C_51))), inference(superposition, [status(thm), theory('equality')], [c_2, c_87])).
% 2.21/1.24  tff(c_96, plain, (![F_29, B_2, C_3, A_1, D_34, E_31]: (k2_xboole_0(k1_enumset1(C_3, B_2, A_1), k1_enumset1(D_34, E_31, F_29))=k4_enumset1(A_1, B_2, C_3, D_34, E_31, F_29))), inference(superposition, [status(thm), theory('equality')], [c_2, c_87])).
% 2.21/1.24  tff(c_206, plain, (![A_58, B_56, C_57, A_55, C_53, B_54]: (k4_enumset1(C_57, B_54, A_58, C_53, B_56, A_55)=k4_enumset1(A_58, B_54, C_57, A_55, B_56, C_53))), inference(superposition, [status(thm), theory('equality')], [c_171, c_96])).
% 2.21/1.24  tff(c_8, plain, (![A_14, B_15, C_16, D_17]: (k4_enumset1(A_14, A_14, A_14, B_15, C_16, D_17)=k2_enumset1(A_14, B_15, C_16, D_17))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.21/1.24  tff(c_277, plain, (![C_59, C_60, B_61, A_62]: (k4_enumset1(C_59, C_59, C_59, C_60, B_61, A_62)=k2_enumset1(C_59, A_62, B_61, C_60))), inference(superposition, [status(thm), theory('equality')], [c_206, c_8])).
% 2.21/1.24  tff(c_289, plain, (![C_59, C_60, B_61, A_62]: (k2_enumset1(C_59, C_60, B_61, A_62)=k2_enumset1(C_59, A_62, B_61, C_60))), inference(superposition, [status(thm), theory('equality')], [c_277, c_8])).
% 2.21/1.24  tff(c_4, plain, (![C_6, B_5, A_4, D_7]: (k2_enumset1(C_6, B_5, A_4, D_7)=k2_enumset1(A_4, B_5, C_6, D_7))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.21/1.24  tff(c_10, plain, (k2_enumset1('#skF_3', '#skF_4', '#skF_1', '#skF_2')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.21/1.24  tff(c_11, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_4', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_10])).
% 2.21/1.24  tff(c_312, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_289, c_11])).
% 2.21/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.24  
% 2.21/1.24  Inference rules
% 2.21/1.24  ----------------------
% 2.21/1.24  #Ref     : 0
% 2.21/1.24  #Sup     : 78
% 2.21/1.24  #Fact    : 0
% 2.21/1.24  #Define  : 0
% 2.21/1.24  #Split   : 0
% 2.21/1.24  #Chain   : 0
% 2.21/1.24  #Close   : 0
% 2.21/1.24  
% 2.21/1.24  Ordering : KBO
% 2.21/1.24  
% 2.21/1.24  Simplification rules
% 2.21/1.24  ----------------------
% 2.21/1.24  #Subsume      : 1
% 2.21/1.24  #Demod        : 11
% 2.21/1.24  #Tautology    : 51
% 2.21/1.24  #SimpNegUnit  : 0
% 2.21/1.24  #BackRed      : 1
% 2.21/1.24  
% 2.21/1.24  #Partial instantiations: 0
% 2.21/1.24  #Strategies tried      : 1
% 2.21/1.24  
% 2.21/1.24  Timing (in seconds)
% 2.21/1.24  ----------------------
% 2.21/1.24  Preprocessing        : 0.25
% 2.21/1.24  Parsing              : 0.13
% 2.21/1.24  CNF conversion       : 0.01
% 2.21/1.25  Main loop            : 0.23
% 2.21/1.25  Inferencing          : 0.09
% 2.21/1.25  Reduction            : 0.09
% 2.21/1.25  Demodulation         : 0.08
% 2.21/1.25  BG Simplification    : 0.01
% 2.21/1.25  Subsumption          : 0.03
% 2.21/1.25  Abstraction          : 0.01
% 2.21/1.25  MUC search           : 0.00
% 2.21/1.25  Cooper               : 0.00
% 2.21/1.25  Total                : 0.50
% 2.21/1.25  Index Insertion      : 0.00
% 2.21/1.25  Index Deletion       : 0.00
% 2.21/1.25  Index Matching       : 0.00
% 2.21/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
