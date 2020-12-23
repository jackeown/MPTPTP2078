%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:43 EST 2020

% Result     : Theorem 2.00s
% Output     : CNFRefutation 2.00s
% Verified   : 
% Statistics : Number of formulae       :   42 (  65 expanded)
%              Number of leaves         :   25 (  34 expanded)
%              Depth                    :   10
%              Number of atoms          :   24 (  47 expanded)
%              Number of equality atoms :   23 (  46 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_43,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_41,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k1_tarski(F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_enumset1)).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(B,A,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_enumset1)).

tff(c_6,plain,(
    ! [B_6,A_5] : k2_tarski(B_6,A_5) = k2_tarski(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_18,plain,(
    ! [A_30,B_31,C_32] : k2_enumset1(A_30,A_30,B_31,C_32) = k1_enumset1(A_30,B_31,C_32) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_16,plain,(
    ! [A_28,B_29] : k1_enumset1(A_28,A_28,B_29) = k2_tarski(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_20,plain,(
    ! [A_33,B_34,C_35,D_36] : k3_enumset1(A_33,A_33,B_34,C_35,D_36) = k2_enumset1(A_33,B_34,C_35,D_36) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_22,plain,(
    ! [C_39,B_38,A_37,D_40,E_41] : k4_enumset1(A_37,A_37,B_38,C_39,D_40,E_41) = k3_enumset1(A_37,B_38,C_39,D_40,E_41) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_134,plain,(
    ! [A_85,B_83,F_86,C_84,E_87,D_82] : k2_xboole_0(k3_enumset1(A_85,B_83,C_84,D_82,E_87),k1_tarski(F_86)) = k4_enumset1(A_85,B_83,C_84,D_82,E_87,F_86) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_143,plain,(
    ! [D_36,F_86,A_33,B_34,C_35] : k4_enumset1(A_33,A_33,B_34,C_35,D_36,F_86) = k2_xboole_0(k2_enumset1(A_33,B_34,C_35,D_36),k1_tarski(F_86)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_134])).

tff(c_147,plain,(
    ! [C_89,F_91,A_88,B_92,D_90] : k2_xboole_0(k2_enumset1(A_88,B_92,C_89,D_90),k1_tarski(F_91)) = k3_enumset1(A_88,B_92,C_89,D_90,F_91) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_143])).

tff(c_156,plain,(
    ! [A_30,B_31,C_32,F_91] : k3_enumset1(A_30,A_30,B_31,C_32,F_91) = k2_xboole_0(k1_enumset1(A_30,B_31,C_32),k1_tarski(F_91)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_147])).

tff(c_160,plain,(
    ! [A_93,B_94,C_95,F_96] : k2_xboole_0(k1_enumset1(A_93,B_94,C_95),k1_tarski(F_96)) = k2_enumset1(A_93,B_94,C_95,F_96) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_156])).

tff(c_169,plain,(
    ! [A_28,B_29,F_96] : k2_xboole_0(k2_tarski(A_28,B_29),k1_tarski(F_96)) = k2_enumset1(A_28,A_28,B_29,F_96) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_160])).

tff(c_173,plain,(
    ! [A_97,B_98,F_99] : k2_xboole_0(k2_tarski(A_97,B_98),k1_tarski(F_99)) = k1_enumset1(A_97,B_98,F_99) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_169])).

tff(c_210,plain,(
    ! [A_109,B_110,F_111] : k2_xboole_0(k2_tarski(A_109,B_110),k1_tarski(F_111)) = k1_enumset1(B_110,A_109,F_111) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_173])).

tff(c_172,plain,(
    ! [A_28,B_29,F_96] : k2_xboole_0(k2_tarski(A_28,B_29),k1_tarski(F_96)) = k1_enumset1(A_28,B_29,F_96) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_169])).

tff(c_216,plain,(
    ! [B_110,A_109,F_111] : k1_enumset1(B_110,A_109,F_111) = k1_enumset1(A_109,B_110,F_111) ),
    inference(superposition,[status(thm),theory(equality)],[c_210,c_172])).

tff(c_28,plain,(
    k1_enumset1('#skF_2','#skF_1','#skF_3') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_239,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_216,c_28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:17:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.00/1.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.20  
% 2.00/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.20  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 2.00/1.20  
% 2.00/1.20  %Foreground sorts:
% 2.00/1.20  
% 2.00/1.20  
% 2.00/1.20  %Background operators:
% 2.00/1.20  
% 2.00/1.20  
% 2.00/1.20  %Foreground operators:
% 2.00/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.00/1.20  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.00/1.20  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.00/1.20  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.00/1.20  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.00/1.20  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.00/1.20  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.00/1.20  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.00/1.20  tff('#skF_2', type, '#skF_2': $i).
% 2.00/1.20  tff('#skF_3', type, '#skF_3': $i).
% 2.00/1.20  tff('#skF_1', type, '#skF_1': $i).
% 2.00/1.20  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.00/1.20  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.00/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.00/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.00/1.20  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.00/1.20  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.00/1.20  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.00/1.20  
% 2.00/1.21  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.00/1.21  tff(f_43, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.00/1.21  tff(f_41, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.00/1.21  tff(f_45, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 2.00/1.21  tff(f_47, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 2.00/1.21  tff(f_33, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k1_tarski(F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_enumset1)).
% 2.00/1.21  tff(f_54, negated_conjecture, ~(![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(B, A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_enumset1)).
% 2.00/1.21  tff(c_6, plain, (![B_6, A_5]: (k2_tarski(B_6, A_5)=k2_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.00/1.21  tff(c_18, plain, (![A_30, B_31, C_32]: (k2_enumset1(A_30, A_30, B_31, C_32)=k1_enumset1(A_30, B_31, C_32))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.00/1.21  tff(c_16, plain, (![A_28, B_29]: (k1_enumset1(A_28, A_28, B_29)=k2_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.00/1.21  tff(c_20, plain, (![A_33, B_34, C_35, D_36]: (k3_enumset1(A_33, A_33, B_34, C_35, D_36)=k2_enumset1(A_33, B_34, C_35, D_36))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.00/1.21  tff(c_22, plain, (![C_39, B_38, A_37, D_40, E_41]: (k4_enumset1(A_37, A_37, B_38, C_39, D_40, E_41)=k3_enumset1(A_37, B_38, C_39, D_40, E_41))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.00/1.21  tff(c_134, plain, (![A_85, B_83, F_86, C_84, E_87, D_82]: (k2_xboole_0(k3_enumset1(A_85, B_83, C_84, D_82, E_87), k1_tarski(F_86))=k4_enumset1(A_85, B_83, C_84, D_82, E_87, F_86))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.00/1.21  tff(c_143, plain, (![D_36, F_86, A_33, B_34, C_35]: (k4_enumset1(A_33, A_33, B_34, C_35, D_36, F_86)=k2_xboole_0(k2_enumset1(A_33, B_34, C_35, D_36), k1_tarski(F_86)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_134])).
% 2.00/1.21  tff(c_147, plain, (![C_89, F_91, A_88, B_92, D_90]: (k2_xboole_0(k2_enumset1(A_88, B_92, C_89, D_90), k1_tarski(F_91))=k3_enumset1(A_88, B_92, C_89, D_90, F_91))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_143])).
% 2.00/1.21  tff(c_156, plain, (![A_30, B_31, C_32, F_91]: (k3_enumset1(A_30, A_30, B_31, C_32, F_91)=k2_xboole_0(k1_enumset1(A_30, B_31, C_32), k1_tarski(F_91)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_147])).
% 2.00/1.21  tff(c_160, plain, (![A_93, B_94, C_95, F_96]: (k2_xboole_0(k1_enumset1(A_93, B_94, C_95), k1_tarski(F_96))=k2_enumset1(A_93, B_94, C_95, F_96))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_156])).
% 2.00/1.21  tff(c_169, plain, (![A_28, B_29, F_96]: (k2_xboole_0(k2_tarski(A_28, B_29), k1_tarski(F_96))=k2_enumset1(A_28, A_28, B_29, F_96))), inference(superposition, [status(thm), theory('equality')], [c_16, c_160])).
% 2.00/1.21  tff(c_173, plain, (![A_97, B_98, F_99]: (k2_xboole_0(k2_tarski(A_97, B_98), k1_tarski(F_99))=k1_enumset1(A_97, B_98, F_99))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_169])).
% 2.00/1.21  tff(c_210, plain, (![A_109, B_110, F_111]: (k2_xboole_0(k2_tarski(A_109, B_110), k1_tarski(F_111))=k1_enumset1(B_110, A_109, F_111))), inference(superposition, [status(thm), theory('equality')], [c_6, c_173])).
% 2.00/1.21  tff(c_172, plain, (![A_28, B_29, F_96]: (k2_xboole_0(k2_tarski(A_28, B_29), k1_tarski(F_96))=k1_enumset1(A_28, B_29, F_96))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_169])).
% 2.00/1.21  tff(c_216, plain, (![B_110, A_109, F_111]: (k1_enumset1(B_110, A_109, F_111)=k1_enumset1(A_109, B_110, F_111))), inference(superposition, [status(thm), theory('equality')], [c_210, c_172])).
% 2.00/1.21  tff(c_28, plain, (k1_enumset1('#skF_2', '#skF_1', '#skF_3')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.00/1.21  tff(c_239, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_216, c_28])).
% 2.00/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.21  
% 2.00/1.21  Inference rules
% 2.00/1.21  ----------------------
% 2.00/1.21  #Ref     : 0
% 2.00/1.21  #Sup     : 49
% 2.00/1.21  #Fact    : 0
% 2.00/1.21  #Define  : 0
% 2.00/1.21  #Split   : 0
% 2.00/1.21  #Chain   : 0
% 2.00/1.22  #Close   : 0
% 2.00/1.22  
% 2.00/1.22  Ordering : KBO
% 2.00/1.22  
% 2.00/1.22  Simplification rules
% 2.00/1.22  ----------------------
% 2.00/1.22  #Subsume      : 0
% 2.00/1.22  #Demod        : 9
% 2.00/1.22  #Tautology    : 41
% 2.00/1.22  #SimpNegUnit  : 0
% 2.00/1.22  #BackRed      : 1
% 2.00/1.22  
% 2.00/1.22  #Partial instantiations: 0
% 2.00/1.22  #Strategies tried      : 1
% 2.00/1.22  
% 2.00/1.22  Timing (in seconds)
% 2.00/1.22  ----------------------
% 2.00/1.22  Preprocessing        : 0.31
% 2.00/1.22  Parsing              : 0.16
% 2.00/1.22  CNF conversion       : 0.02
% 2.00/1.22  Main loop            : 0.15
% 2.00/1.22  Inferencing          : 0.06
% 2.00/1.22  Reduction            : 0.05
% 2.00/1.22  Demodulation         : 0.04
% 2.00/1.22  BG Simplification    : 0.02
% 2.00/1.22  Subsumption          : 0.02
% 2.00/1.22  Abstraction          : 0.01
% 2.00/1.22  MUC search           : 0.00
% 2.00/1.22  Cooper               : 0.00
% 2.00/1.22  Total                : 0.48
% 2.00/1.22  Index Insertion      : 0.00
% 2.00/1.22  Index Deletion       : 0.00
% 2.00/1.22  Index Matching       : 0.00
% 2.00/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
