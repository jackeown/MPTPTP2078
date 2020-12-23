%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:49 EST 2020

% Result     : Theorem 2.09s
% Output     : CNFRefutation 2.34s
% Verified   : 
% Statistics : Number of formulae       :   32 (  41 expanded)
%              Number of leaves         :   18 (  22 expanded)
%              Depth                    :    8
%              Number of atoms          :   20 (  29 expanded)
%              Number of equality atoms :   19 (  28 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(f_35,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(B,A,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C] : k3_enumset1(A,A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k1_enumset1(F,G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E] : k6_enumset1(A,A,A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_38,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,C,B,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_enumset1)).

tff(c_10,plain,(
    ! [B_22,A_21,C_23] : k1_enumset1(B_22,A_21,C_23) = k1_enumset1(A_21,B_22,C_23) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6,plain,(
    ! [A_13,B_14,C_15] : k3_enumset1(A_13,A_13,A_13,B_14,C_15) = k1_enumset1(A_13,B_14,C_15) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_90,plain,(
    ! [E_44,H_49,C_47,D_45,A_48,F_42,G_43,B_46] : k2_xboole_0(k3_enumset1(A_48,B_46,C_47,D_45,E_44),k1_enumset1(F_42,G_43,H_49)) = k6_enumset1(A_48,B_46,C_47,D_45,E_44,F_42,G_43,H_49) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_111,plain,(
    ! [H_52,A_53,B_50,G_55,C_54,F_51] : k6_enumset1(A_53,A_53,A_53,B_50,C_54,F_51,G_55,H_52) = k2_xboole_0(k1_enumset1(A_53,B_50,C_54),k1_enumset1(F_51,G_55,H_52)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_90])).

tff(c_8,plain,(
    ! [C_18,B_17,A_16,D_19,E_20] : k6_enumset1(A_16,A_16,A_16,A_16,B_17,C_18,D_19,E_20) = k3_enumset1(A_16,B_17,C_18,D_19,E_20) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_147,plain,(
    ! [F_56,B_57,H_59,G_58,C_60] : k2_xboole_0(k1_enumset1(B_57,B_57,C_60),k1_enumset1(F_56,G_58,H_59)) = k3_enumset1(B_57,C_60,F_56,G_58,H_59) ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_8])).

tff(c_172,plain,(
    ! [B_64,C_63,C_65,B_61,A_62] : k2_xboole_0(k1_enumset1(B_61,B_61,C_65),k1_enumset1(B_64,A_62,C_63)) = k3_enumset1(B_61,C_65,A_62,B_64,C_63) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_147])).

tff(c_121,plain,(
    ! [H_52,B_50,G_55,C_54,F_51] : k2_xboole_0(k1_enumset1(B_50,B_50,C_54),k1_enumset1(F_51,G_55,H_52)) = k3_enumset1(B_50,C_54,F_51,G_55,H_52) ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_8])).

tff(c_202,plain,(
    ! [B_70,C_67,B_69,C_66,A_68] : k3_enumset1(B_70,C_66,B_69,A_68,C_67) = k3_enumset1(B_70,C_66,A_68,B_69,C_67) ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_121])).

tff(c_4,plain,(
    ! [A_9,B_10,C_11,D_12] : k3_enumset1(A_9,A_9,B_10,C_11,D_12) = k2_enumset1(A_9,B_10,C_11,D_12) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_382,plain,(
    ! [C_84,A_85,B_86,C_87] : k3_enumset1(C_84,C_84,A_85,B_86,C_87) = k2_enumset1(C_84,B_86,A_85,C_87) ),
    inference(superposition,[status(thm),theory(equality)],[c_202,c_4])).

tff(c_401,plain,(
    ! [C_84,B_86,A_85,C_87] : k2_enumset1(C_84,B_86,A_85,C_87) = k2_enumset1(C_84,A_85,B_86,C_87) ),
    inference(superposition,[status(thm),theory(equality)],[c_382,c_4])).

tff(c_12,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_3','#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_438,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_401,c_12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:43:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.09/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.31  
% 2.09/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.31  %$ k6_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.09/1.31  
% 2.09/1.31  %Foreground sorts:
% 2.09/1.31  
% 2.09/1.31  
% 2.09/1.31  %Background operators:
% 2.09/1.31  
% 2.09/1.31  
% 2.09/1.31  %Foreground operators:
% 2.09/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.09/1.31  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.09/1.31  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.09/1.31  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.09/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.09/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.09/1.31  tff('#skF_1', type, '#skF_1': $i).
% 2.09/1.31  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.09/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.09/1.31  tff('#skF_4', type, '#skF_4': $i).
% 2.09/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.09/1.31  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.09/1.31  
% 2.34/1.32  tff(f_35, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(B, A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_enumset1)).
% 2.34/1.32  tff(f_31, axiom, (![A, B, C]: (k3_enumset1(A, A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_enumset1)).
% 2.34/1.32  tff(f_27, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k1_enumset1(F, G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_enumset1)).
% 2.34/1.32  tff(f_33, axiom, (![A, B, C, D, E]: (k6_enumset1(A, A, A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_enumset1)).
% 2.34/1.32  tff(f_29, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 2.34/1.32  tff(f_38, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, C, B, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t104_enumset1)).
% 2.34/1.32  tff(c_10, plain, (![B_22, A_21, C_23]: (k1_enumset1(B_22, A_21, C_23)=k1_enumset1(A_21, B_22, C_23))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.34/1.32  tff(c_6, plain, (![A_13, B_14, C_15]: (k3_enumset1(A_13, A_13, A_13, B_14, C_15)=k1_enumset1(A_13, B_14, C_15))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.34/1.32  tff(c_90, plain, (![E_44, H_49, C_47, D_45, A_48, F_42, G_43, B_46]: (k2_xboole_0(k3_enumset1(A_48, B_46, C_47, D_45, E_44), k1_enumset1(F_42, G_43, H_49))=k6_enumset1(A_48, B_46, C_47, D_45, E_44, F_42, G_43, H_49))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.34/1.32  tff(c_111, plain, (![H_52, A_53, B_50, G_55, C_54, F_51]: (k6_enumset1(A_53, A_53, A_53, B_50, C_54, F_51, G_55, H_52)=k2_xboole_0(k1_enumset1(A_53, B_50, C_54), k1_enumset1(F_51, G_55, H_52)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_90])).
% 2.34/1.32  tff(c_8, plain, (![C_18, B_17, A_16, D_19, E_20]: (k6_enumset1(A_16, A_16, A_16, A_16, B_17, C_18, D_19, E_20)=k3_enumset1(A_16, B_17, C_18, D_19, E_20))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.34/1.32  tff(c_147, plain, (![F_56, B_57, H_59, G_58, C_60]: (k2_xboole_0(k1_enumset1(B_57, B_57, C_60), k1_enumset1(F_56, G_58, H_59))=k3_enumset1(B_57, C_60, F_56, G_58, H_59))), inference(superposition, [status(thm), theory('equality')], [c_111, c_8])).
% 2.34/1.32  tff(c_172, plain, (![B_64, C_63, C_65, B_61, A_62]: (k2_xboole_0(k1_enumset1(B_61, B_61, C_65), k1_enumset1(B_64, A_62, C_63))=k3_enumset1(B_61, C_65, A_62, B_64, C_63))), inference(superposition, [status(thm), theory('equality')], [c_10, c_147])).
% 2.34/1.32  tff(c_121, plain, (![H_52, B_50, G_55, C_54, F_51]: (k2_xboole_0(k1_enumset1(B_50, B_50, C_54), k1_enumset1(F_51, G_55, H_52))=k3_enumset1(B_50, C_54, F_51, G_55, H_52))), inference(superposition, [status(thm), theory('equality')], [c_111, c_8])).
% 2.34/1.32  tff(c_202, plain, (![B_70, C_67, B_69, C_66, A_68]: (k3_enumset1(B_70, C_66, B_69, A_68, C_67)=k3_enumset1(B_70, C_66, A_68, B_69, C_67))), inference(superposition, [status(thm), theory('equality')], [c_172, c_121])).
% 2.34/1.32  tff(c_4, plain, (![A_9, B_10, C_11, D_12]: (k3_enumset1(A_9, A_9, B_10, C_11, D_12)=k2_enumset1(A_9, B_10, C_11, D_12))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.34/1.32  tff(c_382, plain, (![C_84, A_85, B_86, C_87]: (k3_enumset1(C_84, C_84, A_85, B_86, C_87)=k2_enumset1(C_84, B_86, A_85, C_87))), inference(superposition, [status(thm), theory('equality')], [c_202, c_4])).
% 2.34/1.32  tff(c_401, plain, (![C_84, B_86, A_85, C_87]: (k2_enumset1(C_84, B_86, A_85, C_87)=k2_enumset1(C_84, A_85, B_86, C_87))), inference(superposition, [status(thm), theory('equality')], [c_382, c_4])).
% 2.34/1.32  tff(c_12, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_3', '#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.34/1.32  tff(c_438, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_401, c_12])).
% 2.34/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.34/1.32  
% 2.34/1.32  Inference rules
% 2.34/1.32  ----------------------
% 2.34/1.32  #Ref     : 0
% 2.34/1.32  #Sup     : 106
% 2.34/1.32  #Fact    : 0
% 2.34/1.32  #Define  : 0
% 2.34/1.32  #Split   : 0
% 2.34/1.32  #Chain   : 0
% 2.34/1.32  #Close   : 0
% 2.34/1.32  
% 2.34/1.32  Ordering : KBO
% 2.34/1.32  
% 2.34/1.32  Simplification rules
% 2.34/1.32  ----------------------
% 2.34/1.32  #Subsume      : 5
% 2.34/1.32  #Demod        : 29
% 2.34/1.32  #Tautology    : 70
% 2.34/1.32  #SimpNegUnit  : 0
% 2.34/1.32  #BackRed      : 1
% 2.34/1.32  
% 2.34/1.32  #Partial instantiations: 0
% 2.34/1.32  #Strategies tried      : 1
% 2.34/1.32  
% 2.34/1.32  Timing (in seconds)
% 2.34/1.32  ----------------------
% 2.34/1.32  Preprocessing        : 0.29
% 2.34/1.32  Parsing              : 0.16
% 2.34/1.32  CNF conversion       : 0.02
% 2.34/1.32  Main loop            : 0.25
% 2.34/1.32  Inferencing          : 0.11
% 2.34/1.32  Reduction            : 0.09
% 2.34/1.32  Demodulation         : 0.07
% 2.34/1.32  BG Simplification    : 0.01
% 2.34/1.32  Subsumption          : 0.03
% 2.34/1.32  Abstraction          : 0.02
% 2.34/1.32  MUC search           : 0.00
% 2.34/1.32  Cooper               : 0.00
% 2.34/1.32  Total                : 0.56
% 2.34/1.32  Index Insertion      : 0.00
% 2.34/1.32  Index Deletion       : 0.00
% 2.34/1.32  Index Matching       : 0.00
% 2.34/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
