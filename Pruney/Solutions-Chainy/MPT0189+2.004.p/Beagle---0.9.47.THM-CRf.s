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
% DateTime   : Thu Dec  3 09:46:51 EST 2020

% Result     : Theorem 2.13s
% Output     : CNFRefutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :   42 (  72 expanded)
%              Number of leaves         :   25 (  37 expanded)
%              Depth                    :   10
%              Number of atoms          :   23 (  53 expanded)
%              Number of equality atoms :   22 (  52 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_4',type,(
    '#skF_4': $i )).

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

tff(f_45,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_43,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_tarski(E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,A,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_enumset1)).

tff(c_6,plain,(
    ! [B_6,A_5] : k2_tarski(B_6,A_5) = k2_tarski(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_20,plain,(
    ! [A_37,B_38,C_39] : k2_enumset1(A_37,A_37,B_38,C_39) = k1_enumset1(A_37,B_38,C_39) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_18,plain,(
    ! [A_35,B_36] : k1_enumset1(A_35,A_35,B_36) = k2_tarski(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_22,plain,(
    ! [A_40,B_41,C_42,D_43] : k3_enumset1(A_40,A_40,B_41,C_42,D_43) = k2_enumset1(A_40,B_41,C_42,D_43) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_127,plain,(
    ! [C_85,E_87,B_84,D_83,A_86] : k2_xboole_0(k2_enumset1(A_86,B_84,C_85,D_83),k1_tarski(E_87)) = k3_enumset1(A_86,B_84,C_85,D_83,E_87) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_136,plain,(
    ! [A_37,B_38,C_39,E_87] : k3_enumset1(A_37,A_37,B_38,C_39,E_87) = k2_xboole_0(k1_enumset1(A_37,B_38,C_39),k1_tarski(E_87)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_127])).

tff(c_140,plain,(
    ! [A_88,B_89,C_90,E_91] : k2_xboole_0(k1_enumset1(A_88,B_89,C_90),k1_tarski(E_91)) = k2_enumset1(A_88,B_89,C_90,E_91) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_136])).

tff(c_149,plain,(
    ! [A_35,B_36,E_91] : k2_xboole_0(k2_tarski(A_35,B_36),k1_tarski(E_91)) = k2_enumset1(A_35,A_35,B_36,E_91) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_140])).

tff(c_153,plain,(
    ! [A_92,B_93,E_94] : k2_xboole_0(k2_tarski(A_92,B_93),k1_tarski(E_94)) = k1_enumset1(A_92,B_93,E_94) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_149])).

tff(c_181,plain,(
    ! [B_97,A_98,E_99] : k2_xboole_0(k2_tarski(B_97,A_98),k1_tarski(E_99)) = k1_enumset1(A_98,B_97,E_99) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_153])).

tff(c_152,plain,(
    ! [A_35,B_36,E_91] : k2_xboole_0(k2_tarski(A_35,B_36),k1_tarski(E_91)) = k1_enumset1(A_35,B_36,E_91) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_149])).

tff(c_208,plain,(
    ! [B_100,A_101,E_102] : k1_enumset1(B_100,A_101,E_102) = k1_enumset1(A_101,B_100,E_102) ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_152])).

tff(c_139,plain,(
    ! [A_37,B_38,C_39,E_87] : k2_xboole_0(k1_enumset1(A_37,B_38,C_39),k1_tarski(E_87)) = k2_enumset1(A_37,B_38,C_39,E_87) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_136])).

tff(c_257,plain,(
    ! [B_109,A_110,E_111,E_112] : k2_xboole_0(k1_enumset1(B_109,A_110,E_111),k1_tarski(E_112)) = k2_enumset1(A_110,B_109,E_111,E_112) ),
    inference(superposition,[status(thm),theory(equality)],[c_208,c_139])).

tff(c_263,plain,(
    ! [B_109,A_110,E_111,E_112] : k2_enumset1(B_109,A_110,E_111,E_112) = k2_enumset1(A_110,B_109,E_111,E_112) ),
    inference(superposition,[status(thm),theory(equality)],[c_257,c_139])).

tff(c_30,plain,(
    k2_enumset1('#skF_2','#skF_1','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_308,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_263,c_30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:08:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.13/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.29  
% 2.13/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.29  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.13/1.29  
% 2.13/1.29  %Foreground sorts:
% 2.13/1.29  
% 2.13/1.29  
% 2.13/1.29  %Background operators:
% 2.13/1.29  
% 2.13/1.29  
% 2.13/1.29  %Foreground operators:
% 2.13/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.13/1.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.13/1.29  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.13/1.29  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.13/1.29  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.13/1.29  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.13/1.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.13/1.29  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.13/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.13/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.13/1.29  tff('#skF_1', type, '#skF_1': $i).
% 2.13/1.29  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.13/1.29  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.13/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.13/1.29  tff('#skF_4', type, '#skF_4': $i).
% 2.13/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.13/1.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.13/1.29  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.13/1.29  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.13/1.29  
% 2.13/1.30  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.13/1.30  tff(f_45, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.13/1.30  tff(f_43, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.13/1.30  tff(f_47, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 2.13/1.30  tff(f_33, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_tarski(E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_enumset1)).
% 2.13/1.30  tff(f_56, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, A, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t108_enumset1)).
% 2.13/1.30  tff(c_6, plain, (![B_6, A_5]: (k2_tarski(B_6, A_5)=k2_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.13/1.30  tff(c_20, plain, (![A_37, B_38, C_39]: (k2_enumset1(A_37, A_37, B_38, C_39)=k1_enumset1(A_37, B_38, C_39))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.13/1.30  tff(c_18, plain, (![A_35, B_36]: (k1_enumset1(A_35, A_35, B_36)=k2_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.13/1.30  tff(c_22, plain, (![A_40, B_41, C_42, D_43]: (k3_enumset1(A_40, A_40, B_41, C_42, D_43)=k2_enumset1(A_40, B_41, C_42, D_43))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.13/1.30  tff(c_127, plain, (![C_85, E_87, B_84, D_83, A_86]: (k2_xboole_0(k2_enumset1(A_86, B_84, C_85, D_83), k1_tarski(E_87))=k3_enumset1(A_86, B_84, C_85, D_83, E_87))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.13/1.30  tff(c_136, plain, (![A_37, B_38, C_39, E_87]: (k3_enumset1(A_37, A_37, B_38, C_39, E_87)=k2_xboole_0(k1_enumset1(A_37, B_38, C_39), k1_tarski(E_87)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_127])).
% 2.13/1.30  tff(c_140, plain, (![A_88, B_89, C_90, E_91]: (k2_xboole_0(k1_enumset1(A_88, B_89, C_90), k1_tarski(E_91))=k2_enumset1(A_88, B_89, C_90, E_91))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_136])).
% 2.13/1.30  tff(c_149, plain, (![A_35, B_36, E_91]: (k2_xboole_0(k2_tarski(A_35, B_36), k1_tarski(E_91))=k2_enumset1(A_35, A_35, B_36, E_91))), inference(superposition, [status(thm), theory('equality')], [c_18, c_140])).
% 2.13/1.30  tff(c_153, plain, (![A_92, B_93, E_94]: (k2_xboole_0(k2_tarski(A_92, B_93), k1_tarski(E_94))=k1_enumset1(A_92, B_93, E_94))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_149])).
% 2.13/1.30  tff(c_181, plain, (![B_97, A_98, E_99]: (k2_xboole_0(k2_tarski(B_97, A_98), k1_tarski(E_99))=k1_enumset1(A_98, B_97, E_99))), inference(superposition, [status(thm), theory('equality')], [c_6, c_153])).
% 2.13/1.30  tff(c_152, plain, (![A_35, B_36, E_91]: (k2_xboole_0(k2_tarski(A_35, B_36), k1_tarski(E_91))=k1_enumset1(A_35, B_36, E_91))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_149])).
% 2.13/1.30  tff(c_208, plain, (![B_100, A_101, E_102]: (k1_enumset1(B_100, A_101, E_102)=k1_enumset1(A_101, B_100, E_102))), inference(superposition, [status(thm), theory('equality')], [c_181, c_152])).
% 2.13/1.30  tff(c_139, plain, (![A_37, B_38, C_39, E_87]: (k2_xboole_0(k1_enumset1(A_37, B_38, C_39), k1_tarski(E_87))=k2_enumset1(A_37, B_38, C_39, E_87))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_136])).
% 2.13/1.30  tff(c_257, plain, (![B_109, A_110, E_111, E_112]: (k2_xboole_0(k1_enumset1(B_109, A_110, E_111), k1_tarski(E_112))=k2_enumset1(A_110, B_109, E_111, E_112))), inference(superposition, [status(thm), theory('equality')], [c_208, c_139])).
% 2.13/1.30  tff(c_263, plain, (![B_109, A_110, E_111, E_112]: (k2_enumset1(B_109, A_110, E_111, E_112)=k2_enumset1(A_110, B_109, E_111, E_112))), inference(superposition, [status(thm), theory('equality')], [c_257, c_139])).
% 2.13/1.30  tff(c_30, plain, (k2_enumset1('#skF_2', '#skF_1', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.13/1.30  tff(c_308, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_263, c_30])).
% 2.13/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.30  
% 2.13/1.30  Inference rules
% 2.13/1.30  ----------------------
% 2.13/1.30  #Ref     : 0
% 2.13/1.30  #Sup     : 67
% 2.13/1.30  #Fact    : 0
% 2.13/1.30  #Define  : 0
% 2.13/1.30  #Split   : 0
% 2.13/1.30  #Chain   : 0
% 2.13/1.30  #Close   : 0
% 2.13/1.30  
% 2.13/1.30  Ordering : KBO
% 2.13/1.30  
% 2.13/1.30  Simplification rules
% 2.13/1.30  ----------------------
% 2.13/1.30  #Subsume      : 1
% 2.13/1.30  #Demod        : 14
% 2.13/1.30  #Tautology    : 53
% 2.13/1.30  #SimpNegUnit  : 0
% 2.13/1.30  #BackRed      : 1
% 2.13/1.30  
% 2.13/1.30  #Partial instantiations: 0
% 2.13/1.30  #Strategies tried      : 1
% 2.13/1.30  
% 2.13/1.30  Timing (in seconds)
% 2.13/1.30  ----------------------
% 2.13/1.30  Preprocessing        : 0.32
% 2.13/1.30  Parsing              : 0.17
% 2.13/1.30  CNF conversion       : 0.02
% 2.13/1.30  Main loop            : 0.18
% 2.13/1.30  Inferencing          : 0.07
% 2.13/1.30  Reduction            : 0.07
% 2.13/1.30  Demodulation         : 0.05
% 2.13/1.30  BG Simplification    : 0.02
% 2.13/1.30  Subsumption          : 0.02
% 2.13/1.30  Abstraction          : 0.01
% 2.13/1.30  MUC search           : 0.00
% 2.13/1.30  Cooper               : 0.00
% 2.13/1.30  Total                : 0.53
% 2.13/1.30  Index Insertion      : 0.00
% 2.13/1.30  Index Deletion       : 0.00
% 2.13/1.30  Index Matching       : 0.00
% 2.13/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
