%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:48 EST 2020

% Result     : Theorem 1.76s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   30 (  53 expanded)
%              Number of leaves         :   18 (  28 expanded)
%              Depth                    :    7
%              Number of atoms          :   16 (  39 expanded)
%              Number of equality atoms :   15 (  38 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k2_xboole_0 > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,B,D,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_tarski(E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_40,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,C,B,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_enumset1)).

tff(c_2,plain,(
    ! [A_1,B_2,D_4,C_3] : k2_enumset1(A_1,B_2,D_4,C_3) = k2_enumset1(A_1,B_2,C_3,D_4) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_67,plain,(
    ! [C_47,D_45,A_48,B_46,E_49] : k2_xboole_0(k2_enumset1(A_48,B_46,C_47,D_45),k1_tarski(E_49)) = k3_enumset1(A_48,B_46,C_47,D_45,E_49) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_91,plain,(
    ! [A_60,D_56,B_57,E_58,C_59] : k2_xboole_0(k2_enumset1(A_60,B_57,D_56,C_59),k1_tarski(E_58)) = k3_enumset1(A_60,B_57,C_59,D_56,E_58) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_67])).

tff(c_4,plain,(
    ! [B_6,C_7,E_9,D_8,A_5] : k2_xboole_0(k2_enumset1(A_5,B_6,C_7,D_8),k1_tarski(E_9)) = k3_enumset1(A_5,B_6,C_7,D_8,E_9) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_114,plain,(
    ! [E_61,B_62,C_65,D_64,A_63] : k3_enumset1(A_63,B_62,D_64,C_65,E_61) = k3_enumset1(A_63,B_62,C_65,D_64,E_61) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_4])).

tff(c_6,plain,(
    ! [A_10,B_11,C_12,D_13] : k3_enumset1(A_10,A_10,B_11,C_12,D_13) = k2_enumset1(A_10,B_11,C_12,D_13) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_161,plain,(
    ! [B_66,D_67,C_68,E_69] : k3_enumset1(B_66,B_66,D_67,C_68,E_69) = k2_enumset1(B_66,C_68,D_67,E_69) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_6])).

tff(c_173,plain,(
    ! [B_66,D_67,C_68,E_69] : k2_enumset1(B_66,D_67,C_68,E_69) = k2_enumset1(B_66,C_68,D_67,E_69) ),
    inference(superposition,[status(thm),theory(equality)],[c_161,c_6])).

tff(c_14,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_3','#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_15,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_4','#skF_3') != k2_enumset1('#skF_1','#skF_3','#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_14])).

tff(c_203,plain,(
    k2_enumset1('#skF_1','#skF_4','#skF_2','#skF_3') != k2_enumset1('#skF_1','#skF_4','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_173,c_15])).

tff(c_206,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_203])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:55:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.76/1.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.76/1.24  
% 1.76/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.76/1.24  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k2_xboole_0 > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.76/1.24  
% 1.76/1.24  %Foreground sorts:
% 1.76/1.24  
% 1.76/1.24  
% 1.76/1.24  %Background operators:
% 1.76/1.24  
% 1.76/1.24  
% 1.76/1.24  %Foreground operators:
% 1.76/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.76/1.24  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.76/1.24  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.76/1.24  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.76/1.24  tff('#skF_2', type, '#skF_2': $i).
% 1.76/1.24  tff('#skF_3', type, '#skF_3': $i).
% 1.76/1.24  tff('#skF_1', type, '#skF_1': $i).
% 1.76/1.24  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.76/1.24  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.76/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.76/1.24  tff('#skF_4', type, '#skF_4': $i).
% 1.76/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.76/1.24  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.76/1.24  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.76/1.24  
% 1.93/1.25  tff(f_27, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, B, D, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_enumset1)).
% 1.93/1.25  tff(f_29, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_tarski(E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_enumset1)).
% 1.93/1.25  tff(f_31, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 1.93/1.25  tff(f_40, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, C, B, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t104_enumset1)).
% 1.93/1.25  tff(c_2, plain, (![A_1, B_2, D_4, C_3]: (k2_enumset1(A_1, B_2, D_4, C_3)=k2_enumset1(A_1, B_2, C_3, D_4))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.93/1.25  tff(c_67, plain, (![C_47, D_45, A_48, B_46, E_49]: (k2_xboole_0(k2_enumset1(A_48, B_46, C_47, D_45), k1_tarski(E_49))=k3_enumset1(A_48, B_46, C_47, D_45, E_49))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.93/1.25  tff(c_91, plain, (![A_60, D_56, B_57, E_58, C_59]: (k2_xboole_0(k2_enumset1(A_60, B_57, D_56, C_59), k1_tarski(E_58))=k3_enumset1(A_60, B_57, C_59, D_56, E_58))), inference(superposition, [status(thm), theory('equality')], [c_2, c_67])).
% 1.93/1.25  tff(c_4, plain, (![B_6, C_7, E_9, D_8, A_5]: (k2_xboole_0(k2_enumset1(A_5, B_6, C_7, D_8), k1_tarski(E_9))=k3_enumset1(A_5, B_6, C_7, D_8, E_9))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.93/1.25  tff(c_114, plain, (![E_61, B_62, C_65, D_64, A_63]: (k3_enumset1(A_63, B_62, D_64, C_65, E_61)=k3_enumset1(A_63, B_62, C_65, D_64, E_61))), inference(superposition, [status(thm), theory('equality')], [c_91, c_4])).
% 1.93/1.25  tff(c_6, plain, (![A_10, B_11, C_12, D_13]: (k3_enumset1(A_10, A_10, B_11, C_12, D_13)=k2_enumset1(A_10, B_11, C_12, D_13))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.93/1.25  tff(c_161, plain, (![B_66, D_67, C_68, E_69]: (k3_enumset1(B_66, B_66, D_67, C_68, E_69)=k2_enumset1(B_66, C_68, D_67, E_69))), inference(superposition, [status(thm), theory('equality')], [c_114, c_6])).
% 1.93/1.25  tff(c_173, plain, (![B_66, D_67, C_68, E_69]: (k2_enumset1(B_66, D_67, C_68, E_69)=k2_enumset1(B_66, C_68, D_67, E_69))), inference(superposition, [status(thm), theory('equality')], [c_161, c_6])).
% 1.93/1.25  tff(c_14, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_3', '#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.93/1.25  tff(c_15, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_4', '#skF_3')!=k2_enumset1('#skF_1', '#skF_3', '#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2, c_14])).
% 1.93/1.25  tff(c_203, plain, (k2_enumset1('#skF_1', '#skF_4', '#skF_2', '#skF_3')!=k2_enumset1('#skF_1', '#skF_4', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_173, c_173, c_15])).
% 1.93/1.25  tff(c_206, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_203])).
% 1.93/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.25  
% 1.93/1.25  Inference rules
% 1.93/1.25  ----------------------
% 1.93/1.25  #Ref     : 0
% 1.93/1.25  #Sup     : 46
% 1.93/1.25  #Fact    : 0
% 1.93/1.25  #Define  : 0
% 1.93/1.25  #Split   : 0
% 1.93/1.25  #Chain   : 0
% 1.93/1.25  #Close   : 0
% 1.93/1.25  
% 1.93/1.25  Ordering : KBO
% 1.93/1.25  
% 1.93/1.25  Simplification rules
% 1.93/1.25  ----------------------
% 1.93/1.25  #Subsume      : 0
% 1.93/1.25  #Demod        : 11
% 1.93/1.25  #Tautology    : 36
% 1.93/1.25  #SimpNegUnit  : 0
% 1.93/1.25  #BackRed      : 1
% 1.93/1.25  
% 1.93/1.25  #Partial instantiations: 0
% 1.93/1.25  #Strategies tried      : 1
% 1.93/1.25  
% 1.93/1.25  Timing (in seconds)
% 1.93/1.25  ----------------------
% 1.93/1.25  Preprocessing        : 0.27
% 1.93/1.25  Parsing              : 0.14
% 1.93/1.25  CNF conversion       : 0.02
% 1.93/1.25  Main loop            : 0.15
% 1.93/1.25  Inferencing          : 0.06
% 1.93/1.25  Reduction            : 0.05
% 1.93/1.25  Demodulation         : 0.04
% 1.93/1.25  BG Simplification    : 0.01
% 1.93/1.25  Subsumption          : 0.02
% 1.93/1.25  Abstraction          : 0.01
% 1.93/1.25  MUC search           : 0.00
% 1.93/1.25  Cooper               : 0.00
% 1.93/1.25  Total                : 0.44
% 1.93/1.25  Index Insertion      : 0.00
% 1.93/1.25  Index Deletion       : 0.00
% 1.93/1.25  Index Matching       : 0.00
% 1.93/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
