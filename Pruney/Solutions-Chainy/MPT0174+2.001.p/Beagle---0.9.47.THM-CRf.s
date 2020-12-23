%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:32 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   34 (  38 expanded)
%              Number of leaves         :   18 (  21 expanded)
%              Depth                    :    7
%              Number of atoms          :   22 (  26 expanded)
%              Number of equality atoms :   21 (  25 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k4_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_33,axiom,(
    ! [A,B,C,D] : k4_enumset1(A,A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C] : k4_enumset1(A,A,A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k2_enumset1(A,B,C,D),k2_enumset1(E,F,G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l75_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_enumset1(A,B,C),k1_enumset1(D,E,F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_enumset1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,k2_xboole_0(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_1)).

tff(f_38,negated_conjecture,(
    ~ ! [A,B,C,D] : k6_enumset1(A,A,A,A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_enumset1)).

tff(c_39,plain,(
    ! [A_29,B_30,C_31,D_32] : k4_enumset1(A_29,A_29,A_29,B_30,C_31,D_32) = k2_enumset1(A_29,B_30,C_31,D_32) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_21,B_22,C_23] : k4_enumset1(A_21,A_21,A_21,A_21,B_22,C_23) = k1_enumset1(A_21,B_22,C_23) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_46,plain,(
    ! [B_30,C_31,D_32] : k2_enumset1(B_30,B_30,C_31,D_32) = k1_enumset1(B_30,C_31,D_32) ),
    inference(superposition,[status(thm),theory(equality)],[c_39,c_10])).

tff(c_121,plain,(
    ! [C_57,E_52,F_54,D_53,G_51,B_58,A_55,H_56] : k2_xboole_0(k2_enumset1(A_55,B_58,C_57,D_53),k2_enumset1(E_52,F_54,G_51,H_56)) = k6_enumset1(A_55,B_58,C_57,D_53,E_52,F_54,G_51,H_56) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_199,plain,(
    ! [G_78,F_81,H_77,B_80,E_79,D_76,C_82] : k6_enumset1(B_80,B_80,C_82,D_76,E_79,F_81,G_78,H_77) = k2_xboole_0(k1_enumset1(B_80,C_82,D_76),k2_enumset1(E_79,F_81,G_78,H_77)) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_121])).

tff(c_8,plain,(
    ! [A_17,B_18,C_19,D_20] : k4_enumset1(A_17,A_17,A_17,B_18,C_19,D_20) = k2_enumset1(A_17,B_18,C_19,D_20) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [F_16,D_14,E_15,B_12,A_11,C_13] : k2_xboole_0(k1_enumset1(A_11,B_12,C_13),k1_enumset1(D_14,E_15,F_16)) = k4_enumset1(A_11,B_12,C_13,D_14,E_15,F_16) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_65,plain,(
    ! [B_39,D_40,C_37,F_36,E_41,A_38] : k2_xboole_0(k1_enumset1(A_38,B_39,C_37),k1_enumset1(D_40,E_41,F_36)) = k4_enumset1(A_38,B_39,C_37,D_40,E_41,F_36) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2,plain,(
    ! [A_1,B_2] : k2_xboole_0(A_1,k2_xboole_0(A_1,B_2)) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_71,plain,(
    ! [B_39,D_40,C_37,F_36,E_41,A_38] : k2_xboole_0(k1_enumset1(A_38,B_39,C_37),k4_enumset1(A_38,B_39,C_37,D_40,E_41,F_36)) = k2_xboole_0(k1_enumset1(A_38,B_39,C_37),k1_enumset1(D_40,E_41,F_36)) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_2])).

tff(c_78,plain,(
    ! [F_46,A_42,C_47,D_43,E_45,B_44] : k2_xboole_0(k1_enumset1(A_42,B_44,C_47),k4_enumset1(A_42,B_44,C_47,D_43,E_45,F_46)) = k4_enumset1(A_42,B_44,C_47,D_43,E_45,F_46) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_71])).

tff(c_90,plain,(
    ! [A_17,B_18,C_19,D_20] : k2_xboole_0(k1_enumset1(A_17,A_17,A_17),k2_enumset1(A_17,B_18,C_19,D_20)) = k4_enumset1(A_17,A_17,A_17,B_18,C_19,D_20) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_78])).

tff(c_97,plain,(
    ! [A_17,B_18,C_19,D_20] : k2_xboole_0(k1_enumset1(A_17,A_17,A_17),k2_enumset1(A_17,B_18,C_19,D_20)) = k2_enumset1(A_17,B_18,C_19,D_20) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_90])).

tff(c_217,plain,(
    ! [E_79,F_81,G_78,H_77] : k6_enumset1(E_79,E_79,E_79,E_79,E_79,F_81,G_78,H_77) = k2_enumset1(E_79,F_81,G_78,H_77) ),
    inference(superposition,[status(thm),theory(equality)],[c_199,c_97])).

tff(c_12,plain,(
    k6_enumset1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_251,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_217,c_12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:21:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.93/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.21  
% 1.93/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.21  %$ k6_enumset1 > k4_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.93/1.21  
% 1.93/1.21  %Foreground sorts:
% 1.93/1.21  
% 1.93/1.21  
% 1.93/1.21  %Background operators:
% 1.93/1.21  
% 1.93/1.21  
% 1.93/1.21  %Foreground operators:
% 1.93/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.93/1.21  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.93/1.21  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.93/1.21  tff('#skF_2', type, '#skF_2': $i).
% 1.93/1.21  tff('#skF_3', type, '#skF_3': $i).
% 1.93/1.21  tff('#skF_1', type, '#skF_1': $i).
% 1.93/1.21  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.93/1.21  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.93/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.93/1.21  tff('#skF_4', type, '#skF_4': $i).
% 1.93/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.93/1.21  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.93/1.21  
% 1.93/1.22  tff(f_33, axiom, (![A, B, C, D]: (k4_enumset1(A, A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_enumset1)).
% 1.93/1.22  tff(f_35, axiom, (![A, B, C]: (k4_enumset1(A, A, A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_enumset1)).
% 1.93/1.22  tff(f_29, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k2_enumset1(A, B, C, D), k2_enumset1(E, F, G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l75_enumset1)).
% 1.93/1.22  tff(f_31, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_enumset1(A, B, C), k1_enumset1(D, E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_enumset1)).
% 1.93/1.22  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, k2_xboole_0(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_xboole_1)).
% 1.93/1.22  tff(f_38, negated_conjecture, ~(![A, B, C, D]: (k6_enumset1(A, A, A, A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_enumset1)).
% 1.93/1.22  tff(c_39, plain, (![A_29, B_30, C_31, D_32]: (k4_enumset1(A_29, A_29, A_29, B_30, C_31, D_32)=k2_enumset1(A_29, B_30, C_31, D_32))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.93/1.22  tff(c_10, plain, (![A_21, B_22, C_23]: (k4_enumset1(A_21, A_21, A_21, A_21, B_22, C_23)=k1_enumset1(A_21, B_22, C_23))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.93/1.22  tff(c_46, plain, (![B_30, C_31, D_32]: (k2_enumset1(B_30, B_30, C_31, D_32)=k1_enumset1(B_30, C_31, D_32))), inference(superposition, [status(thm), theory('equality')], [c_39, c_10])).
% 1.93/1.22  tff(c_121, plain, (![C_57, E_52, F_54, D_53, G_51, B_58, A_55, H_56]: (k2_xboole_0(k2_enumset1(A_55, B_58, C_57, D_53), k2_enumset1(E_52, F_54, G_51, H_56))=k6_enumset1(A_55, B_58, C_57, D_53, E_52, F_54, G_51, H_56))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.93/1.22  tff(c_199, plain, (![G_78, F_81, H_77, B_80, E_79, D_76, C_82]: (k6_enumset1(B_80, B_80, C_82, D_76, E_79, F_81, G_78, H_77)=k2_xboole_0(k1_enumset1(B_80, C_82, D_76), k2_enumset1(E_79, F_81, G_78, H_77)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_121])).
% 1.93/1.22  tff(c_8, plain, (![A_17, B_18, C_19, D_20]: (k4_enumset1(A_17, A_17, A_17, B_18, C_19, D_20)=k2_enumset1(A_17, B_18, C_19, D_20))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.93/1.22  tff(c_6, plain, (![F_16, D_14, E_15, B_12, A_11, C_13]: (k2_xboole_0(k1_enumset1(A_11, B_12, C_13), k1_enumset1(D_14, E_15, F_16))=k4_enumset1(A_11, B_12, C_13, D_14, E_15, F_16))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.93/1.22  tff(c_65, plain, (![B_39, D_40, C_37, F_36, E_41, A_38]: (k2_xboole_0(k1_enumset1(A_38, B_39, C_37), k1_enumset1(D_40, E_41, F_36))=k4_enumset1(A_38, B_39, C_37, D_40, E_41, F_36))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.93/1.22  tff(c_2, plain, (![A_1, B_2]: (k2_xboole_0(A_1, k2_xboole_0(A_1, B_2))=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.93/1.22  tff(c_71, plain, (![B_39, D_40, C_37, F_36, E_41, A_38]: (k2_xboole_0(k1_enumset1(A_38, B_39, C_37), k4_enumset1(A_38, B_39, C_37, D_40, E_41, F_36))=k2_xboole_0(k1_enumset1(A_38, B_39, C_37), k1_enumset1(D_40, E_41, F_36)))), inference(superposition, [status(thm), theory('equality')], [c_65, c_2])).
% 1.93/1.22  tff(c_78, plain, (![F_46, A_42, C_47, D_43, E_45, B_44]: (k2_xboole_0(k1_enumset1(A_42, B_44, C_47), k4_enumset1(A_42, B_44, C_47, D_43, E_45, F_46))=k4_enumset1(A_42, B_44, C_47, D_43, E_45, F_46))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_71])).
% 1.93/1.22  tff(c_90, plain, (![A_17, B_18, C_19, D_20]: (k2_xboole_0(k1_enumset1(A_17, A_17, A_17), k2_enumset1(A_17, B_18, C_19, D_20))=k4_enumset1(A_17, A_17, A_17, B_18, C_19, D_20))), inference(superposition, [status(thm), theory('equality')], [c_8, c_78])).
% 1.93/1.22  tff(c_97, plain, (![A_17, B_18, C_19, D_20]: (k2_xboole_0(k1_enumset1(A_17, A_17, A_17), k2_enumset1(A_17, B_18, C_19, D_20))=k2_enumset1(A_17, B_18, C_19, D_20))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_90])).
% 1.93/1.22  tff(c_217, plain, (![E_79, F_81, G_78, H_77]: (k6_enumset1(E_79, E_79, E_79, E_79, E_79, F_81, G_78, H_77)=k2_enumset1(E_79, F_81, G_78, H_77))), inference(superposition, [status(thm), theory('equality')], [c_199, c_97])).
% 1.93/1.22  tff(c_12, plain, (k6_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.93/1.22  tff(c_251, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_217, c_12])).
% 1.93/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.22  
% 1.93/1.22  Inference rules
% 1.93/1.22  ----------------------
% 1.93/1.22  #Ref     : 0
% 1.93/1.22  #Sup     : 56
% 1.93/1.22  #Fact    : 0
% 1.93/1.22  #Define  : 0
% 1.93/1.22  #Split   : 0
% 1.93/1.22  #Chain   : 0
% 1.93/1.22  #Close   : 0
% 1.93/1.22  
% 1.93/1.22  Ordering : KBO
% 1.93/1.22  
% 1.93/1.22  Simplification rules
% 1.93/1.22  ----------------------
% 1.93/1.22  #Subsume      : 0
% 1.93/1.22  #Demod        : 37
% 1.93/1.22  #Tautology    : 44
% 1.93/1.22  #SimpNegUnit  : 0
% 1.93/1.22  #BackRed      : 1
% 1.93/1.22  
% 1.93/1.22  #Partial instantiations: 0
% 1.93/1.22  #Strategies tried      : 1
% 1.93/1.22  
% 1.93/1.22  Timing (in seconds)
% 1.93/1.22  ----------------------
% 1.93/1.22  Preprocessing        : 0.27
% 1.93/1.22  Parsing              : 0.15
% 1.93/1.22  CNF conversion       : 0.02
% 1.93/1.22  Main loop            : 0.18
% 1.93/1.22  Inferencing          : 0.09
% 1.93/1.23  Reduction            : 0.06
% 1.93/1.23  Demodulation         : 0.05
% 1.93/1.23  BG Simplification    : 0.01
% 1.93/1.23  Subsumption          : 0.02
% 1.93/1.23  Abstraction          : 0.01
% 1.93/1.23  MUC search           : 0.00
% 1.93/1.23  Cooper               : 0.00
% 1.93/1.23  Total                : 0.48
% 1.93/1.23  Index Insertion      : 0.00
% 1.93/1.23  Index Deletion       : 0.00
% 1.93/1.23  Index Matching       : 0.00
% 1.93/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
