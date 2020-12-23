%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:49 EST 2020

% Result     : Theorem 2.09s
% Output     : CNFRefutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :   29 (  32 expanded)
%              Number of leaves         :   19 (  21 expanded)
%              Depth                    :    6
%              Number of atoms          :   14 (  17 expanded)
%              Number of equality atoms :   13 (  16 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(f_41,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(B,A,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_tarski(A,B),k1_enumset1(C,D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_44,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,C,B,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_enumset1)).

tff(c_16,plain,(
    ! [B_34,A_33,C_35] : k1_enumset1(B_34,A_33,C_35) = k1_enumset1(A_33,B_34,C_35) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_88,plain,(
    ! [A_57,C_56,D_54,B_55,E_53] : k2_xboole_0(k2_tarski(A_57,B_55),k1_enumset1(C_56,D_54,E_53)) = k3_enumset1(A_57,B_55,C_56,D_54,E_53) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_166,plain,(
    ! [B_73,B_74,C_72,A_71,A_75] : k2_xboole_0(k2_tarski(A_75,B_73),k1_enumset1(B_74,A_71,C_72)) = k3_enumset1(A_75,B_73,A_71,B_74,C_72) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_88])).

tff(c_2,plain,(
    ! [B_2,C_3,A_1,E_5,D_4] : k2_xboole_0(k2_tarski(A_1,B_2),k1_enumset1(C_3,D_4,E_5)) = k3_enumset1(A_1,B_2,C_3,D_4,E_5) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_192,plain,(
    ! [C_78,A_77,B_80,A_79,B_76] : k3_enumset1(A_77,B_76,B_80,A_79,C_78) = k3_enumset1(A_77,B_76,A_79,B_80,C_78) ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_2])).

tff(c_8,plain,(
    ! [A_11,B_12,C_13,D_14] : k3_enumset1(A_11,A_11,B_12,C_13,D_14) = k2_enumset1(A_11,B_12,C_13,D_14) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_239,plain,(
    ! [B_81,B_82,A_83,C_84] : k3_enumset1(B_81,B_81,B_82,A_83,C_84) = k2_enumset1(B_81,A_83,B_82,C_84) ),
    inference(superposition,[status(thm),theory(equality)],[c_192,c_8])).

tff(c_255,plain,(
    ! [B_81,B_82,A_83,C_84] : k2_enumset1(B_81,B_82,A_83,C_84) = k2_enumset1(B_81,A_83,B_82,C_84) ),
    inference(superposition,[status(thm),theory(equality)],[c_239,c_8])).

tff(c_18,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_3','#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_282,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_255,c_18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:26:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.09/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.28  
% 2.09/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.28  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.09/1.28  
% 2.09/1.28  %Foreground sorts:
% 2.09/1.28  
% 2.09/1.28  
% 2.09/1.28  %Background operators:
% 2.09/1.28  
% 2.09/1.28  
% 2.09/1.28  %Foreground operators:
% 2.09/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.09/1.28  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.09/1.28  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.09/1.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.09/1.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.09/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.09/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.09/1.28  tff('#skF_1', type, '#skF_1': $i).
% 2.09/1.28  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.09/1.28  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.09/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.09/1.28  tff('#skF_4', type, '#skF_4': $i).
% 2.09/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.09/1.28  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.09/1.28  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.09/1.28  
% 2.09/1.29  tff(f_41, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(B, A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_enumset1)).
% 2.09/1.29  tff(f_27, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_tarski(A, B), k1_enumset1(C, D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_enumset1)).
% 2.09/1.29  tff(f_33, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 2.09/1.29  tff(f_44, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, C, B, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t104_enumset1)).
% 2.09/1.29  tff(c_16, plain, (![B_34, A_33, C_35]: (k1_enumset1(B_34, A_33, C_35)=k1_enumset1(A_33, B_34, C_35))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.09/1.29  tff(c_88, plain, (![A_57, C_56, D_54, B_55, E_53]: (k2_xboole_0(k2_tarski(A_57, B_55), k1_enumset1(C_56, D_54, E_53))=k3_enumset1(A_57, B_55, C_56, D_54, E_53))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.09/1.29  tff(c_166, plain, (![B_73, B_74, C_72, A_71, A_75]: (k2_xboole_0(k2_tarski(A_75, B_73), k1_enumset1(B_74, A_71, C_72))=k3_enumset1(A_75, B_73, A_71, B_74, C_72))), inference(superposition, [status(thm), theory('equality')], [c_16, c_88])).
% 2.09/1.29  tff(c_2, plain, (![B_2, C_3, A_1, E_5, D_4]: (k2_xboole_0(k2_tarski(A_1, B_2), k1_enumset1(C_3, D_4, E_5))=k3_enumset1(A_1, B_2, C_3, D_4, E_5))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.09/1.29  tff(c_192, plain, (![C_78, A_77, B_80, A_79, B_76]: (k3_enumset1(A_77, B_76, B_80, A_79, C_78)=k3_enumset1(A_77, B_76, A_79, B_80, C_78))), inference(superposition, [status(thm), theory('equality')], [c_166, c_2])).
% 2.09/1.29  tff(c_8, plain, (![A_11, B_12, C_13, D_14]: (k3_enumset1(A_11, A_11, B_12, C_13, D_14)=k2_enumset1(A_11, B_12, C_13, D_14))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.09/1.29  tff(c_239, plain, (![B_81, B_82, A_83, C_84]: (k3_enumset1(B_81, B_81, B_82, A_83, C_84)=k2_enumset1(B_81, A_83, B_82, C_84))), inference(superposition, [status(thm), theory('equality')], [c_192, c_8])).
% 2.09/1.29  tff(c_255, plain, (![B_81, B_82, A_83, C_84]: (k2_enumset1(B_81, B_82, A_83, C_84)=k2_enumset1(B_81, A_83, B_82, C_84))), inference(superposition, [status(thm), theory('equality')], [c_239, c_8])).
% 2.09/1.29  tff(c_18, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_3', '#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.09/1.29  tff(c_282, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_255, c_18])).
% 2.09/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.29  
% 2.09/1.29  Inference rules
% 2.09/1.29  ----------------------
% 2.09/1.29  #Ref     : 0
% 2.09/1.29  #Sup     : 64
% 2.09/1.29  #Fact    : 0
% 2.09/1.29  #Define  : 0
% 2.09/1.29  #Split   : 0
% 2.09/1.29  #Chain   : 0
% 2.09/1.29  #Close   : 0
% 2.09/1.29  
% 2.09/1.29  Ordering : KBO
% 2.09/1.29  
% 2.09/1.29  Simplification rules
% 2.09/1.29  ----------------------
% 2.09/1.29  #Subsume      : 4
% 2.09/1.29  #Demod        : 9
% 2.09/1.29  #Tautology    : 48
% 2.09/1.29  #SimpNegUnit  : 0
% 2.09/1.29  #BackRed      : 1
% 2.09/1.29  
% 2.09/1.29  #Partial instantiations: 0
% 2.09/1.29  #Strategies tried      : 1
% 2.09/1.29  
% 2.09/1.29  Timing (in seconds)
% 2.09/1.29  ----------------------
% 2.09/1.30  Preprocessing        : 0.31
% 2.09/1.30  Parsing              : 0.17
% 2.09/1.30  CNF conversion       : 0.02
% 2.09/1.30  Main loop            : 0.19
% 2.09/1.30  Inferencing          : 0.08
% 2.09/1.30  Reduction            : 0.07
% 2.09/1.30  Demodulation         : 0.05
% 2.09/1.30  BG Simplification    : 0.01
% 2.09/1.30  Subsumption          : 0.02
% 2.09/1.30  Abstraction          : 0.01
% 2.09/1.30  MUC search           : 0.00
% 2.09/1.30  Cooper               : 0.00
% 2.09/1.30  Total                : 0.52
% 2.09/1.30  Index Insertion      : 0.00
% 2.09/1.30  Index Deletion       : 0.00
% 2.09/1.30  Index Matching       : 0.00
% 2.09/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
