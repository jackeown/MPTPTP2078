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
% DateTime   : Thu Dec  3 09:46:34 EST 2020

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :   31 (  31 expanded)
%              Number of leaves         :   20 (  20 expanded)
%              Depth                    :    5
%              Number of atoms          :   17 (  17 expanded)
%              Number of equality atoms :   16 (  16 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_45,axiom,(
    ! [A,B] : k3_enumset1(A,A,A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_enumset1)).

tff(f_43,axiom,(
    ! [A] : k2_enumset1(A,A,A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_tarski(E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_enumset1)).

tff(f_47,axiom,(
    ! [A] : k4_enumset1(A,A,A,A,A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k4_enumset1(A,B,C,D,E,F),k1_tarski(G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_enumset1)).

tff(f_50,negated_conjecture,(
    ~ ! [A,B] : k5_enumset1(A,A,A,A,A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_enumset1)).

tff(c_20,plain,(
    ! [A_53,B_54] : k3_enumset1(A_53,A_53,A_53,A_53,B_54) = k2_tarski(A_53,B_54) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_18,plain,(
    ! [A_52] : k2_enumset1(A_52,A_52,A_52,A_52) = k1_tarski(A_52) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_110,plain,(
    ! [B_70,A_74,E_73,D_72,C_71] : k2_xboole_0(k2_enumset1(A_74,B_70,C_71,D_72),k1_tarski(E_73)) = k3_enumset1(A_74,B_70,C_71,D_72,E_73) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_122,plain,(
    ! [A_52,E_73] : k3_enumset1(A_52,A_52,A_52,A_52,E_73) = k2_xboole_0(k1_tarski(A_52),k1_tarski(E_73)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_110])).

tff(c_125,plain,(
    ! [A_52,E_73] : k2_xboole_0(k1_tarski(A_52),k1_tarski(E_73)) = k2_tarski(A_52,E_73) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_122])).

tff(c_22,plain,(
    ! [A_55] : k4_enumset1(A_55,A_55,A_55,A_55,A_55,A_55) = k1_tarski(A_55) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_185,plain,(
    ! [C_85,B_87,E_88,F_86,G_82,D_84,A_83] : k2_xboole_0(k4_enumset1(A_83,B_87,C_85,D_84,E_88,F_86),k1_tarski(G_82)) = k5_enumset1(A_83,B_87,C_85,D_84,E_88,F_86,G_82) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_197,plain,(
    ! [A_55,G_82] : k5_enumset1(A_55,A_55,A_55,A_55,A_55,A_55,G_82) = k2_xboole_0(k1_tarski(A_55),k1_tarski(G_82)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_185])).

tff(c_200,plain,(
    ! [A_55,G_82] : k5_enumset1(A_55,A_55,A_55,A_55,A_55,A_55,G_82) = k2_tarski(A_55,G_82) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_197])).

tff(c_24,plain,(
    k5_enumset1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_2') != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_203,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:01:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.18/1.57  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.58  
% 2.18/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.58  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1
% 2.18/1.58  
% 2.18/1.58  %Foreground sorts:
% 2.18/1.58  
% 2.18/1.58  
% 2.18/1.58  %Background operators:
% 2.18/1.58  
% 2.18/1.58  
% 2.18/1.58  %Foreground operators:
% 2.18/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.18/1.58  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.18/1.58  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.18/1.58  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.18/1.58  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.18/1.58  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.18/1.58  tff('#skF_2', type, '#skF_2': $i).
% 2.18/1.58  tff('#skF_1', type, '#skF_1': $i).
% 2.18/1.58  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.18/1.58  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.18/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.18/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.18/1.58  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.18/1.58  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.18/1.58  
% 2.18/1.59  tff(f_45, axiom, (![A, B]: (k3_enumset1(A, A, A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_enumset1)).
% 2.18/1.59  tff(f_43, axiom, (![A]: (k2_enumset1(A, A, A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t82_enumset1)).
% 2.18/1.59  tff(f_29, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_tarski(E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_enumset1)).
% 2.18/1.59  tff(f_47, axiom, (![A]: (k4_enumset1(A, A, A, A, A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_enumset1)).
% 2.18/1.59  tff(f_33, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k4_enumset1(A, B, C, D, E, F), k1_tarski(G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_enumset1)).
% 2.18/1.59  tff(f_50, negated_conjecture, ~(![A, B]: (k5_enumset1(A, A, A, A, A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_enumset1)).
% 2.18/1.59  tff(c_20, plain, (![A_53, B_54]: (k3_enumset1(A_53, A_53, A_53, A_53, B_54)=k2_tarski(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.18/1.59  tff(c_18, plain, (![A_52]: (k2_enumset1(A_52, A_52, A_52, A_52)=k1_tarski(A_52))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.18/1.59  tff(c_110, plain, (![B_70, A_74, E_73, D_72, C_71]: (k2_xboole_0(k2_enumset1(A_74, B_70, C_71, D_72), k1_tarski(E_73))=k3_enumset1(A_74, B_70, C_71, D_72, E_73))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.18/1.59  tff(c_122, plain, (![A_52, E_73]: (k3_enumset1(A_52, A_52, A_52, A_52, E_73)=k2_xboole_0(k1_tarski(A_52), k1_tarski(E_73)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_110])).
% 2.18/1.59  tff(c_125, plain, (![A_52, E_73]: (k2_xboole_0(k1_tarski(A_52), k1_tarski(E_73))=k2_tarski(A_52, E_73))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_122])).
% 2.18/1.59  tff(c_22, plain, (![A_55]: (k4_enumset1(A_55, A_55, A_55, A_55, A_55, A_55)=k1_tarski(A_55))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.18/1.59  tff(c_185, plain, (![C_85, B_87, E_88, F_86, G_82, D_84, A_83]: (k2_xboole_0(k4_enumset1(A_83, B_87, C_85, D_84, E_88, F_86), k1_tarski(G_82))=k5_enumset1(A_83, B_87, C_85, D_84, E_88, F_86, G_82))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.18/1.59  tff(c_197, plain, (![A_55, G_82]: (k5_enumset1(A_55, A_55, A_55, A_55, A_55, A_55, G_82)=k2_xboole_0(k1_tarski(A_55), k1_tarski(G_82)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_185])).
% 2.18/1.59  tff(c_200, plain, (![A_55, G_82]: (k5_enumset1(A_55, A_55, A_55, A_55, A_55, A_55, G_82)=k2_tarski(A_55, G_82))), inference(demodulation, [status(thm), theory('equality')], [c_125, c_197])).
% 2.18/1.59  tff(c_24, plain, (k5_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2')!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.18/1.59  tff(c_203, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_200, c_24])).
% 2.18/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.59  
% 2.18/1.59  Inference rules
% 2.18/1.59  ----------------------
% 2.18/1.59  #Ref     : 0
% 2.18/1.59  #Sup     : 41
% 2.18/1.59  #Fact    : 0
% 2.18/1.59  #Define  : 0
% 2.18/1.59  #Split   : 0
% 2.18/1.59  #Chain   : 0
% 2.18/1.59  #Close   : 0
% 2.18/1.59  
% 2.18/1.59  Ordering : KBO
% 2.18/1.59  
% 2.18/1.59  Simplification rules
% 2.18/1.59  ----------------------
% 2.18/1.59  #Subsume      : 0
% 2.18/1.59  #Demod        : 18
% 2.18/1.59  #Tautology    : 34
% 2.18/1.59  #SimpNegUnit  : 0
% 2.18/1.59  #BackRed      : 1
% 2.18/1.59  
% 2.18/1.59  #Partial instantiations: 0
% 2.18/1.59  #Strategies tried      : 1
% 2.18/1.59  
% 2.18/1.59  Timing (in seconds)
% 2.18/1.59  ----------------------
% 2.18/1.59  Preprocessing        : 0.53
% 2.18/1.59  Parsing              : 0.28
% 2.18/1.59  CNF conversion       : 0.03
% 2.18/1.59  Main loop            : 0.14
% 2.18/1.59  Inferencing          : 0.05
% 2.18/1.59  Reduction            : 0.05
% 2.18/1.59  Demodulation         : 0.04
% 2.18/1.59  BG Simplification    : 0.02
% 2.18/1.59  Subsumption          : 0.02
% 2.18/1.59  Abstraction          : 0.01
% 2.18/1.59  MUC search           : 0.00
% 2.18/1.59  Cooper               : 0.00
% 2.18/1.59  Total                : 0.70
% 2.18/1.59  Index Insertion      : 0.00
% 2.18/1.59  Index Deletion       : 0.00
% 2.18/1.59  Index Matching       : 0.00
% 2.18/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
