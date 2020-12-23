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
% DateTime   : Thu Dec  3 09:48:11 EST 2020

% Result     : Theorem 2.78s
% Output     : CNFRefutation 2.78s
% Verified   : 
% Statistics : Number of formulae       :   38 (  42 expanded)
%              Number of leaves         :   23 (  25 expanded)
%              Depth                    :    9
%              Number of atoms          :   22 (  26 expanded)
%              Number of equality atoms :   21 (  25 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1

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

tff(f_43,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_41,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k2_enumset1(A,B,C,D),k2_tarski(E,F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_enumset1)).

tff(f_52,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_zfmisc_1)).

tff(c_18,plain,(
    ! [A_33,B_34] : k1_enumset1(A_33,A_33,B_34) = k2_tarski(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_20,plain,(
    ! [A_35,B_36,C_37] : k2_enumset1(A_35,A_35,B_36,C_37) = k1_enumset1(A_35,B_36,C_37) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_16,plain,(
    ! [A_32] : k2_tarski(A_32,A_32) = k1_tarski(A_32) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_22,plain,(
    ! [A_38,B_39,C_40,D_41] : k3_enumset1(A_38,A_38,B_39,C_40,D_41) = k2_enumset1(A_38,B_39,C_40,D_41) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_24,plain,(
    ! [B_43,A_42,D_45,E_46,C_44] : k4_enumset1(A_42,A_42,B_43,C_44,D_45,E_46) = k3_enumset1(A_42,B_43,C_44,D_45,E_46) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_327,plain,(
    ! [F_85,C_86,B_81,D_84,A_83,E_82] : k2_xboole_0(k2_enumset1(A_83,B_81,C_86,D_84),k2_tarski(E_82,F_85)) = k4_enumset1(A_83,B_81,C_86,D_84,E_82,F_85) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_336,plain,(
    ! [A_35,F_85,B_36,C_37,E_82] : k4_enumset1(A_35,A_35,B_36,C_37,E_82,F_85) = k2_xboole_0(k1_enumset1(A_35,B_36,C_37),k2_tarski(E_82,F_85)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_327])).

tff(c_693,plain,(
    ! [E_108,B_107,F_105,A_104,C_106] : k2_xboole_0(k1_enumset1(A_104,B_107,C_106),k2_tarski(E_108,F_105)) = k3_enumset1(A_104,B_107,C_106,E_108,F_105) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_336])).

tff(c_702,plain,(
    ! [A_33,B_34,E_108,F_105] : k3_enumset1(A_33,A_33,B_34,E_108,F_105) = k2_xboole_0(k2_tarski(A_33,B_34),k2_tarski(E_108,F_105)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_693])).

tff(c_709,plain,(
    ! [A_109,B_110,E_111,F_112] : k2_xboole_0(k2_tarski(A_109,B_110),k2_tarski(E_111,F_112)) = k2_enumset1(A_109,B_110,E_111,F_112) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_702])).

tff(c_718,plain,(
    ! [A_32,E_111,F_112] : k2_xboole_0(k1_tarski(A_32),k2_tarski(E_111,F_112)) = k2_enumset1(A_32,A_32,E_111,F_112) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_709])).

tff(c_724,plain,(
    ! [A_32,E_111,F_112] : k2_xboole_0(k1_tarski(A_32),k2_tarski(E_111,F_112)) = k1_enumset1(A_32,E_111,F_112) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_718])).

tff(c_26,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k2_tarski('#skF_1','#skF_2')) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_725,plain,(
    k1_enumset1('#skF_1','#skF_1','#skF_2') != k2_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_724,c_26])).

tff(c_728,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_725])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 18:32:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.78/1.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.78/1.39  
% 2.78/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.78/1.39  %$ k6_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1
% 2.78/1.39  
% 2.78/1.39  %Foreground sorts:
% 2.78/1.39  
% 2.78/1.39  
% 2.78/1.39  %Background operators:
% 2.78/1.39  
% 2.78/1.39  
% 2.78/1.39  %Foreground operators:
% 2.78/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.78/1.39  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.78/1.39  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.78/1.39  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.78/1.39  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.78/1.39  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.78/1.39  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.78/1.39  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.78/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.78/1.39  tff('#skF_1', type, '#skF_1': $i).
% 2.78/1.39  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.78/1.39  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.78/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.78/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.78/1.39  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.78/1.39  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.78/1.39  
% 2.78/1.40  tff(f_43, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.78/1.40  tff(f_45, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.78/1.40  tff(f_41, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.78/1.40  tff(f_47, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 2.78/1.40  tff(f_49, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 2.78/1.40  tff(f_35, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k2_enumset1(A, B, C, D), k2_tarski(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_enumset1)).
% 2.78/1.40  tff(f_52, negated_conjecture, ~(![A, B]: (k2_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_zfmisc_1)).
% 2.78/1.40  tff(c_18, plain, (![A_33, B_34]: (k1_enumset1(A_33, A_33, B_34)=k2_tarski(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.78/1.40  tff(c_20, plain, (![A_35, B_36, C_37]: (k2_enumset1(A_35, A_35, B_36, C_37)=k1_enumset1(A_35, B_36, C_37))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.78/1.40  tff(c_16, plain, (![A_32]: (k2_tarski(A_32, A_32)=k1_tarski(A_32))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.78/1.40  tff(c_22, plain, (![A_38, B_39, C_40, D_41]: (k3_enumset1(A_38, A_38, B_39, C_40, D_41)=k2_enumset1(A_38, B_39, C_40, D_41))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.78/1.40  tff(c_24, plain, (![B_43, A_42, D_45, E_46, C_44]: (k4_enumset1(A_42, A_42, B_43, C_44, D_45, E_46)=k3_enumset1(A_42, B_43, C_44, D_45, E_46))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.78/1.40  tff(c_327, plain, (![F_85, C_86, B_81, D_84, A_83, E_82]: (k2_xboole_0(k2_enumset1(A_83, B_81, C_86, D_84), k2_tarski(E_82, F_85))=k4_enumset1(A_83, B_81, C_86, D_84, E_82, F_85))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.78/1.40  tff(c_336, plain, (![A_35, F_85, B_36, C_37, E_82]: (k4_enumset1(A_35, A_35, B_36, C_37, E_82, F_85)=k2_xboole_0(k1_enumset1(A_35, B_36, C_37), k2_tarski(E_82, F_85)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_327])).
% 2.78/1.40  tff(c_693, plain, (![E_108, B_107, F_105, A_104, C_106]: (k2_xboole_0(k1_enumset1(A_104, B_107, C_106), k2_tarski(E_108, F_105))=k3_enumset1(A_104, B_107, C_106, E_108, F_105))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_336])).
% 2.78/1.40  tff(c_702, plain, (![A_33, B_34, E_108, F_105]: (k3_enumset1(A_33, A_33, B_34, E_108, F_105)=k2_xboole_0(k2_tarski(A_33, B_34), k2_tarski(E_108, F_105)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_693])).
% 2.78/1.40  tff(c_709, plain, (![A_109, B_110, E_111, F_112]: (k2_xboole_0(k2_tarski(A_109, B_110), k2_tarski(E_111, F_112))=k2_enumset1(A_109, B_110, E_111, F_112))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_702])).
% 2.78/1.40  tff(c_718, plain, (![A_32, E_111, F_112]: (k2_xboole_0(k1_tarski(A_32), k2_tarski(E_111, F_112))=k2_enumset1(A_32, A_32, E_111, F_112))), inference(superposition, [status(thm), theory('equality')], [c_16, c_709])).
% 2.78/1.40  tff(c_724, plain, (![A_32, E_111, F_112]: (k2_xboole_0(k1_tarski(A_32), k2_tarski(E_111, F_112))=k1_enumset1(A_32, E_111, F_112))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_718])).
% 2.78/1.40  tff(c_26, plain, (k2_xboole_0(k1_tarski('#skF_1'), k2_tarski('#skF_1', '#skF_2'))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.78/1.40  tff(c_725, plain, (k1_enumset1('#skF_1', '#skF_1', '#skF_2')!=k2_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_724, c_26])).
% 2.78/1.40  tff(c_728, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_725])).
% 2.78/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.78/1.40  
% 2.78/1.40  Inference rules
% 2.78/1.40  ----------------------
% 2.78/1.40  #Ref     : 0
% 2.78/1.40  #Sup     : 172
% 2.78/1.40  #Fact    : 0
% 2.78/1.40  #Define  : 0
% 2.78/1.40  #Split   : 0
% 2.78/1.40  #Chain   : 0
% 2.78/1.40  #Close   : 0
% 2.78/1.40  
% 2.78/1.40  Ordering : KBO
% 2.78/1.40  
% 2.78/1.40  Simplification rules
% 2.78/1.40  ----------------------
% 2.78/1.40  #Subsume      : 0
% 2.78/1.40  #Demod        : 135
% 2.78/1.40  #Tautology    : 63
% 2.78/1.40  #SimpNegUnit  : 0
% 2.78/1.40  #BackRed      : 1
% 2.78/1.40  
% 2.78/1.40  #Partial instantiations: 0
% 2.78/1.40  #Strategies tried      : 1
% 2.78/1.40  
% 2.78/1.40  Timing (in seconds)
% 2.78/1.40  ----------------------
% 2.78/1.40  Preprocessing        : 0.31
% 2.78/1.40  Parsing              : 0.17
% 2.78/1.40  CNF conversion       : 0.02
% 2.78/1.40  Main loop            : 0.32
% 2.78/1.40  Inferencing          : 0.12
% 2.78/1.40  Reduction            : 0.12
% 2.78/1.40  Demodulation         : 0.10
% 2.78/1.40  BG Simplification    : 0.02
% 2.78/1.40  Subsumption          : 0.04
% 2.78/1.40  Abstraction          : 0.03
% 2.78/1.40  MUC search           : 0.00
% 2.78/1.40  Cooper               : 0.00
% 2.78/1.40  Total                : 0.66
% 2.78/1.40  Index Insertion      : 0.00
% 2.78/1.40  Index Deletion       : 0.00
% 2.78/1.40  Index Matching       : 0.00
% 2.78/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
