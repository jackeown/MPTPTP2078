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
% DateTime   : Thu Dec  3 09:46:35 EST 2020

% Result     : Theorem 1.65s
% Output     : CNFRefutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :   29 (  36 expanded)
%              Number of leaves         :   18 (  21 expanded)
%              Depth                    :    7
%              Number of atoms          :   16 (  23 expanded)
%              Number of equality atoms :   15 (  22 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k4_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_35,axiom,(
    ! [A,B,C] : k4_enumset1(A,A,A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_enumset1(A,B,C),k1_enumset1(D,E,F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l62_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D] : k4_enumset1(A,A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k2_enumset1(A,B,C,D),k2_enumset1(E,F,G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_enumset1)).

tff(f_38,negated_conjecture,(
    ~ ! [A,B,C] : k6_enumset1(A,A,A,A,A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_enumset1)).

tff(c_10,plain,(
    ! [A_21,B_22,C_23] : k4_enumset1(A_21,A_21,A_21,A_21,B_22,C_23) = k1_enumset1(A_21,B_22,C_23) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4,plain,(
    ! [A_3,F_8,D_6,C_5,E_7,B_4] : k2_xboole_0(k1_enumset1(A_3,B_4,C_5),k1_enumset1(D_6,E_7,F_8)) = k4_enumset1(A_3,B_4,C_5,D_6,E_7,F_8) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_31,plain,(
    ! [A_29,B_30,C_31,D_32] : k4_enumset1(A_29,A_29,A_29,B_30,C_31,D_32) = k2_enumset1(A_29,B_30,C_31,D_32) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_38,plain,(
    ! [B_30,C_31,D_32] : k2_enumset1(B_30,B_30,C_31,D_32) = k1_enumset1(B_30,C_31,D_32) ),
    inference(superposition,[status(thm),theory(equality)],[c_31,c_10])).

tff(c_66,plain,(
    ! [H_47,B_43,D_45,F_42,G_48,E_46,C_44,A_49] : k2_xboole_0(k2_enumset1(A_49,B_43,C_44,D_45),k2_enumset1(E_46,F_42,G_48,H_47)) = k6_enumset1(A_49,B_43,C_44,D_45,E_46,F_42,G_48,H_47) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_81,plain,(
    ! [E_50,G_53,C_56,F_52,D_51,H_55,B_54] : k6_enumset1(B_54,B_54,C_56,D_51,E_50,F_52,G_53,H_55) = k2_xboole_0(k1_enumset1(B_54,C_56,D_51),k2_enumset1(E_50,F_52,G_53,H_55)) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_66])).

tff(c_96,plain,(
    ! [C_56,D_51,D_32,C_31,B_54,B_30] : k6_enumset1(B_54,B_54,C_56,D_51,B_30,B_30,C_31,D_32) = k2_xboole_0(k1_enumset1(B_54,C_56,D_51),k1_enumset1(B_30,C_31,D_32)) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_81])).

tff(c_101,plain,(
    ! [C_56,D_51,D_32,C_31,B_54,B_30] : k6_enumset1(B_54,B_54,C_56,D_51,B_30,B_30,C_31,D_32) = k4_enumset1(B_54,C_56,D_51,B_30,C_31,D_32) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_96])).

tff(c_12,plain,(
    k6_enumset1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_133,plain,(
    k4_enumset1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_12])).

tff(c_136,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_133])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:10:44 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.65/1.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.65/1.14  
% 1.65/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.65/1.14  %$ k6_enumset1 > k4_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.65/1.14  
% 1.65/1.14  %Foreground sorts:
% 1.65/1.14  
% 1.65/1.14  
% 1.65/1.14  %Background operators:
% 1.65/1.14  
% 1.65/1.14  
% 1.65/1.14  %Foreground operators:
% 1.65/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.65/1.14  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.65/1.14  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.65/1.14  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.65/1.14  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.65/1.14  tff('#skF_2', type, '#skF_2': $i).
% 1.65/1.14  tff('#skF_3', type, '#skF_3': $i).
% 1.65/1.14  tff('#skF_1', type, '#skF_1': $i).
% 1.65/1.14  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.65/1.14  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.65/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.65/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.65/1.14  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.65/1.14  
% 1.87/1.15  tff(f_35, axiom, (![A, B, C]: (k4_enumset1(A, A, A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_enumset1)).
% 1.87/1.15  tff(f_29, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_enumset1(A, B, C), k1_enumset1(D, E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l62_enumset1)).
% 1.87/1.15  tff(f_33, axiom, (![A, B, C, D]: (k4_enumset1(A, A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_enumset1)).
% 1.87/1.15  tff(f_31, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k2_enumset1(A, B, C, D), k2_enumset1(E, F, G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_enumset1)).
% 1.87/1.15  tff(f_38, negated_conjecture, ~(![A, B, C]: (k6_enumset1(A, A, A, A, A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t93_enumset1)).
% 1.87/1.15  tff(c_10, plain, (![A_21, B_22, C_23]: (k4_enumset1(A_21, A_21, A_21, A_21, B_22, C_23)=k1_enumset1(A_21, B_22, C_23))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.87/1.15  tff(c_4, plain, (![A_3, F_8, D_6, C_5, E_7, B_4]: (k2_xboole_0(k1_enumset1(A_3, B_4, C_5), k1_enumset1(D_6, E_7, F_8))=k4_enumset1(A_3, B_4, C_5, D_6, E_7, F_8))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.87/1.15  tff(c_31, plain, (![A_29, B_30, C_31, D_32]: (k4_enumset1(A_29, A_29, A_29, B_30, C_31, D_32)=k2_enumset1(A_29, B_30, C_31, D_32))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.87/1.15  tff(c_38, plain, (![B_30, C_31, D_32]: (k2_enumset1(B_30, B_30, C_31, D_32)=k1_enumset1(B_30, C_31, D_32))), inference(superposition, [status(thm), theory('equality')], [c_31, c_10])).
% 1.87/1.15  tff(c_66, plain, (![H_47, B_43, D_45, F_42, G_48, E_46, C_44, A_49]: (k2_xboole_0(k2_enumset1(A_49, B_43, C_44, D_45), k2_enumset1(E_46, F_42, G_48, H_47))=k6_enumset1(A_49, B_43, C_44, D_45, E_46, F_42, G_48, H_47))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.87/1.15  tff(c_81, plain, (![E_50, G_53, C_56, F_52, D_51, H_55, B_54]: (k6_enumset1(B_54, B_54, C_56, D_51, E_50, F_52, G_53, H_55)=k2_xboole_0(k1_enumset1(B_54, C_56, D_51), k2_enumset1(E_50, F_52, G_53, H_55)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_66])).
% 1.87/1.15  tff(c_96, plain, (![C_56, D_51, D_32, C_31, B_54, B_30]: (k6_enumset1(B_54, B_54, C_56, D_51, B_30, B_30, C_31, D_32)=k2_xboole_0(k1_enumset1(B_54, C_56, D_51), k1_enumset1(B_30, C_31, D_32)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_81])).
% 1.87/1.15  tff(c_101, plain, (![C_56, D_51, D_32, C_31, B_54, B_30]: (k6_enumset1(B_54, B_54, C_56, D_51, B_30, B_30, C_31, D_32)=k4_enumset1(B_54, C_56, D_51, B_30, C_31, D_32))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_96])).
% 1.87/1.15  tff(c_12, plain, (k6_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.87/1.15  tff(c_133, plain, (k4_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_101, c_12])).
% 1.87/1.15  tff(c_136, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_133])).
% 1.87/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.15  
% 1.87/1.15  Inference rules
% 1.87/1.15  ----------------------
% 1.87/1.15  #Ref     : 0
% 1.87/1.15  #Sup     : 28
% 1.87/1.15  #Fact    : 0
% 1.87/1.15  #Define  : 0
% 1.87/1.15  #Split   : 0
% 1.87/1.15  #Chain   : 0
% 1.87/1.15  #Close   : 0
% 1.87/1.15  
% 1.87/1.15  Ordering : KBO
% 1.87/1.15  
% 1.87/1.15  Simplification rules
% 1.87/1.15  ----------------------
% 1.87/1.15  #Subsume      : 0
% 1.87/1.15  #Demod        : 9
% 1.87/1.15  #Tautology    : 23
% 1.87/1.15  #SimpNegUnit  : 0
% 1.87/1.15  #BackRed      : 1
% 1.87/1.15  
% 1.87/1.15  #Partial instantiations: 0
% 1.87/1.15  #Strategies tried      : 1
% 1.87/1.15  
% 1.87/1.15  Timing (in seconds)
% 1.87/1.15  ----------------------
% 1.87/1.16  Preprocessing        : 0.27
% 1.87/1.16  Parsing              : 0.14
% 1.87/1.16  CNF conversion       : 0.02
% 1.87/1.16  Main loop            : 0.13
% 1.87/1.16  Inferencing          : 0.06
% 1.87/1.16  Reduction            : 0.04
% 1.87/1.16  Demodulation         : 0.03
% 1.87/1.16  BG Simplification    : 0.01
% 1.87/1.16  Subsumption          : 0.01
% 1.87/1.16  Abstraction          : 0.01
% 1.87/1.16  MUC search           : 0.00
% 1.87/1.16  Cooper               : 0.00
% 1.87/1.16  Total                : 0.42
% 1.87/1.16  Index Insertion      : 0.00
% 1.87/1.16  Index Deletion       : 0.00
% 1.87/1.16  Index Matching       : 0.00
% 1.87/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
