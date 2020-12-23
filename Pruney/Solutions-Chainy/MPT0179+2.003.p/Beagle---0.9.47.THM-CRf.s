%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:38 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   38 (  58 expanded)
%              Number of leaves         :   21 (  29 expanded)
%              Depth                    :    9
%              Number of atoms          :   24 (  44 expanded)
%              Number of equality atoms :   23 (  43 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_enumset1(A,B,C),k2_tarski(D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E,F] : k6_enumset1(A,A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C] : k5_enumset1(A,A,A,A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k4_enumset1(A,B,C,D,E,F),k2_tarski(G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_enumset1)).

tff(f_37,axiom,(
    ! [A,B] : k3_enumset1(A,A,A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_enumset1)).

tff(f_42,negated_conjecture,(
    ~ ! [A,B] : k6_enumset1(A,A,A,A,A,A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_enumset1)).

tff(c_4,plain,(
    ! [A_3,D_6,C_5,E_7,B_4] : k2_xboole_0(k1_enumset1(A_3,B_4,C_5),k2_tarski(D_6,E_7)) = k3_enumset1(A_3,B_4,C_5,D_6,E_7) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_69,plain,(
    ! [E_55,G_53,F_52,A_56,C_58,D_57,B_54] : k6_enumset1(A_56,A_56,B_54,C_58,D_57,E_55,F_52,G_53) = k5_enumset1(A_56,B_54,C_58,D_57,E_55,F_52,G_53) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_23,B_24,F_28,D_26,C_25,E_27] : k6_enumset1(A_23,A_23,A_23,B_24,C_25,D_26,E_27,F_28) = k4_enumset1(A_23,B_24,C_25,D_26,E_27,F_28) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_85,plain,(
    ! [D_63,E_62,B_64,G_59,C_61,F_60] : k5_enumset1(B_64,B_64,C_61,D_63,E_62,F_60,G_59) = k4_enumset1(B_64,C_61,D_63,E_62,F_60,G_59) ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_10])).

tff(c_14,plain,(
    ! [A_31,B_32,C_33] : k5_enumset1(A_31,A_31,A_31,A_31,A_31,B_32,C_33) = k1_enumset1(A_31,B_32,C_33) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_92,plain,(
    ! [E_62,F_60,G_59] : k4_enumset1(E_62,E_62,E_62,E_62,F_60,G_59) = k1_enumset1(E_62,F_60,G_59) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_14])).

tff(c_141,plain,(
    ! [E_72,F_70,B_73,D_77,G_75,C_74,A_71,H_76] : k2_xboole_0(k4_enumset1(A_71,B_73,C_74,D_77,E_72,F_70),k2_tarski(G_75,H_76)) = k6_enumset1(A_71,B_73,C_74,D_77,E_72,F_70,G_75,H_76) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_153,plain,(
    ! [G_75,E_62,G_59,F_60,H_76] : k6_enumset1(E_62,E_62,E_62,E_62,F_60,G_59,G_75,H_76) = k2_xboole_0(k1_enumset1(E_62,F_60,G_59),k2_tarski(G_75,H_76)) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_141])).

tff(c_213,plain,(
    ! [F_84,G_83,G_80,H_81,E_82] : k6_enumset1(E_82,E_82,E_82,E_82,F_84,G_80,G_83,H_81) = k3_enumset1(E_82,F_84,G_80,G_83,H_81) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_153])).

tff(c_236,plain,(
    ! [F_86,G_85,G_88,H_87,E_89] : k4_enumset1(E_89,E_89,F_86,G_85,G_88,H_87) = k3_enumset1(E_89,F_86,G_85,G_88,H_87) ),
    inference(superposition,[status(thm),theory(equality)],[c_213,c_10])).

tff(c_256,plain,(
    ! [G_90,G_91,H_92] : k3_enumset1(G_90,G_90,G_90,G_91,H_92) = k1_enumset1(G_90,G_91,H_92) ),
    inference(superposition,[status(thm),theory(equality)],[c_236,c_92])).

tff(c_12,plain,(
    ! [A_29,B_30] : k3_enumset1(A_29,A_29,A_29,A_29,B_30) = k2_tarski(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_263,plain,(
    ! [G_91,H_92] : k1_enumset1(G_91,G_91,H_92) = k2_tarski(G_91,H_92) ),
    inference(superposition,[status(thm),theory(equality)],[c_256,c_12])).

tff(c_16,plain,(
    k6_enumset1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_2') != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_17,plain,(
    k4_enumset1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_2') != k2_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_16])).

tff(c_101,plain,(
    k1_enumset1('#skF_1','#skF_1','#skF_2') != k2_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_17])).

tff(c_274,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_263,c_101])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:26:54 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.93/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.22  
% 1.93/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.22  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > #skF_2 > #skF_1
% 1.93/1.22  
% 1.93/1.22  %Foreground sorts:
% 1.93/1.22  
% 1.93/1.22  
% 1.93/1.22  %Background operators:
% 1.93/1.22  
% 1.93/1.22  
% 1.93/1.22  %Foreground operators:
% 1.93/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.93/1.22  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.93/1.22  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.93/1.22  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.93/1.22  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.93/1.22  tff('#skF_2', type, '#skF_2': $i).
% 1.93/1.22  tff('#skF_1', type, '#skF_1': $i).
% 1.93/1.22  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.93/1.22  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.93/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.93/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.93/1.22  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.93/1.22  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.93/1.22  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.93/1.22  
% 1.93/1.23  tff(f_29, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_enumset1(A, B, C), k2_tarski(D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_enumset1)).
% 1.93/1.23  tff(f_33, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 1.93/1.23  tff(f_35, axiom, (![A, B, C, D, E, F]: (k6_enumset1(A, A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_enumset1)).
% 1.93/1.23  tff(f_39, axiom, (![A, B, C]: (k5_enumset1(A, A, A, A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t89_enumset1)).
% 1.93/1.23  tff(f_31, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k4_enumset1(A, B, C, D, E, F), k2_tarski(G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_enumset1)).
% 1.93/1.23  tff(f_37, axiom, (![A, B]: (k3_enumset1(A, A, A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_enumset1)).
% 1.93/1.23  tff(f_42, negated_conjecture, ~(![A, B]: (k6_enumset1(A, A, A, A, A, A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_enumset1)).
% 1.93/1.23  tff(c_4, plain, (![A_3, D_6, C_5, E_7, B_4]: (k2_xboole_0(k1_enumset1(A_3, B_4, C_5), k2_tarski(D_6, E_7))=k3_enumset1(A_3, B_4, C_5, D_6, E_7))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.93/1.23  tff(c_69, plain, (![E_55, G_53, F_52, A_56, C_58, D_57, B_54]: (k6_enumset1(A_56, A_56, B_54, C_58, D_57, E_55, F_52, G_53)=k5_enumset1(A_56, B_54, C_58, D_57, E_55, F_52, G_53))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.93/1.23  tff(c_10, plain, (![A_23, B_24, F_28, D_26, C_25, E_27]: (k6_enumset1(A_23, A_23, A_23, B_24, C_25, D_26, E_27, F_28)=k4_enumset1(A_23, B_24, C_25, D_26, E_27, F_28))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.93/1.23  tff(c_85, plain, (![D_63, E_62, B_64, G_59, C_61, F_60]: (k5_enumset1(B_64, B_64, C_61, D_63, E_62, F_60, G_59)=k4_enumset1(B_64, C_61, D_63, E_62, F_60, G_59))), inference(superposition, [status(thm), theory('equality')], [c_69, c_10])).
% 1.93/1.23  tff(c_14, plain, (![A_31, B_32, C_33]: (k5_enumset1(A_31, A_31, A_31, A_31, A_31, B_32, C_33)=k1_enumset1(A_31, B_32, C_33))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.93/1.23  tff(c_92, plain, (![E_62, F_60, G_59]: (k4_enumset1(E_62, E_62, E_62, E_62, F_60, G_59)=k1_enumset1(E_62, F_60, G_59))), inference(superposition, [status(thm), theory('equality')], [c_85, c_14])).
% 1.93/1.23  tff(c_141, plain, (![E_72, F_70, B_73, D_77, G_75, C_74, A_71, H_76]: (k2_xboole_0(k4_enumset1(A_71, B_73, C_74, D_77, E_72, F_70), k2_tarski(G_75, H_76))=k6_enumset1(A_71, B_73, C_74, D_77, E_72, F_70, G_75, H_76))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.93/1.23  tff(c_153, plain, (![G_75, E_62, G_59, F_60, H_76]: (k6_enumset1(E_62, E_62, E_62, E_62, F_60, G_59, G_75, H_76)=k2_xboole_0(k1_enumset1(E_62, F_60, G_59), k2_tarski(G_75, H_76)))), inference(superposition, [status(thm), theory('equality')], [c_92, c_141])).
% 1.93/1.23  tff(c_213, plain, (![F_84, G_83, G_80, H_81, E_82]: (k6_enumset1(E_82, E_82, E_82, E_82, F_84, G_80, G_83, H_81)=k3_enumset1(E_82, F_84, G_80, G_83, H_81))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_153])).
% 1.93/1.23  tff(c_236, plain, (![F_86, G_85, G_88, H_87, E_89]: (k4_enumset1(E_89, E_89, F_86, G_85, G_88, H_87)=k3_enumset1(E_89, F_86, G_85, G_88, H_87))), inference(superposition, [status(thm), theory('equality')], [c_213, c_10])).
% 1.93/1.23  tff(c_256, plain, (![G_90, G_91, H_92]: (k3_enumset1(G_90, G_90, G_90, G_91, H_92)=k1_enumset1(G_90, G_91, H_92))), inference(superposition, [status(thm), theory('equality')], [c_236, c_92])).
% 1.93/1.23  tff(c_12, plain, (![A_29, B_30]: (k3_enumset1(A_29, A_29, A_29, A_29, B_30)=k2_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.93/1.23  tff(c_263, plain, (![G_91, H_92]: (k1_enumset1(G_91, G_91, H_92)=k2_tarski(G_91, H_92))), inference(superposition, [status(thm), theory('equality')], [c_256, c_12])).
% 1.93/1.23  tff(c_16, plain, (k6_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2')!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.93/1.23  tff(c_17, plain, (k4_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2')!=k2_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_16])).
% 1.93/1.23  tff(c_101, plain, (k1_enumset1('#skF_1', '#skF_1', '#skF_2')!=k2_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_17])).
% 1.93/1.23  tff(c_274, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_263, c_101])).
% 1.93/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.23  
% 1.93/1.23  Inference rules
% 1.93/1.23  ----------------------
% 1.93/1.23  #Ref     : 0
% 1.93/1.23  #Sup     : 62
% 1.93/1.23  #Fact    : 0
% 1.93/1.23  #Define  : 0
% 1.93/1.23  #Split   : 0
% 1.93/1.23  #Chain   : 0
% 1.93/1.23  #Close   : 0
% 1.93/1.23  
% 1.93/1.23  Ordering : KBO
% 1.93/1.23  
% 1.93/1.23  Simplification rules
% 1.93/1.23  ----------------------
% 1.93/1.23  #Subsume      : 0
% 1.93/1.23  #Demod        : 30
% 1.93/1.23  #Tautology    : 31
% 1.93/1.23  #SimpNegUnit  : 0
% 1.93/1.23  #BackRed      : 2
% 1.93/1.23  
% 1.93/1.23  #Partial instantiations: 0
% 1.93/1.23  #Strategies tried      : 1
% 1.93/1.23  
% 1.93/1.23  Timing (in seconds)
% 1.93/1.23  ----------------------
% 2.24/1.23  Preprocessing        : 0.28
% 2.24/1.23  Parsing              : 0.15
% 2.24/1.23  CNF conversion       : 0.02
% 2.24/1.23  Main loop            : 0.20
% 2.24/1.23  Inferencing          : 0.08
% 2.24/1.23  Reduction            : 0.08
% 2.24/1.23  Demodulation         : 0.06
% 2.24/1.23  BG Simplification    : 0.02
% 2.24/1.23  Subsumption          : 0.02
% 2.24/1.23  Abstraction          : 0.02
% 2.24/1.23  MUC search           : 0.00
% 2.24/1.23  Cooper               : 0.00
% 2.24/1.23  Total                : 0.50
% 2.24/1.23  Index Insertion      : 0.00
% 2.24/1.23  Index Deletion       : 0.00
% 2.24/1.23  Index Matching       : 0.00
% 2.24/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
