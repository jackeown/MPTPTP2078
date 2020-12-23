%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:22 EST 2020

% Result     : Theorem 1.85s
% Output     : CNFRefutation 1.85s
% Verified   : 
% Statistics : Number of formulae       :   30 (  30 expanded)
%              Number of leaves         :   23 (  23 expanded)
%              Depth                    :    4
%              Number of atoms          :   11 (  11 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(f_29,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_enumset1(E,F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l68_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k1_enumset1(F,G,H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_enumset1)).

tff(f_42,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

tff(c_4,plain,(
    ! [A_3,F_8,D_6,C_5,G_9,E_7,B_4] : k2_xboole_0(k2_enumset1(A_3,B_4,C_5,D_6),k1_enumset1(E_7,F_8,G_9)) = k5_enumset1(A_3,B_4,C_5,D_6,E_7,F_8,G_9) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_10,plain,(
    ! [A_21,B_22,C_23,D_24] : k3_enumset1(A_21,A_21,B_22,C_23,D_24) = k2_enumset1(A_21,B_22,C_23,D_24) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_84,plain,(
    ! [E_72,D_74,B_70,F_75,H_71,C_76,G_69,A_73] : k2_xboole_0(k3_enumset1(A_73,B_70,C_76,D_74,E_72),k1_enumset1(F_75,G_69,H_71)) = k6_enumset1(A_73,B_70,C_76,D_74,E_72,F_75,G_69,H_71) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_93,plain,(
    ! [A_21,B_22,D_24,C_23,F_75,H_71,G_69] : k6_enumset1(A_21,A_21,B_22,C_23,D_24,F_75,G_69,H_71) = k2_xboole_0(k2_enumset1(A_21,B_22,C_23,D_24),k1_enumset1(F_75,G_69,H_71)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_84])).

tff(c_96,plain,(
    ! [A_21,B_22,D_24,C_23,F_75,H_71,G_69] : k6_enumset1(A_21,A_21,B_22,C_23,D_24,F_75,G_69,H_71) = k5_enumset1(A_21,B_22,C_23,D_24,F_75,G_69,H_71) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_93])).

tff(c_16,plain,(
    k6_enumset1('#skF_1','#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7') != k5_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_99,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:45:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.85/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.85/1.24  
% 1.85/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.85/1.24  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.85/1.24  
% 1.85/1.24  %Foreground sorts:
% 1.85/1.24  
% 1.85/1.24  
% 1.85/1.24  %Background operators:
% 1.85/1.24  
% 1.85/1.24  
% 1.85/1.24  %Foreground operators:
% 1.85/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.85/1.24  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.85/1.24  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.85/1.24  tff('#skF_7', type, '#skF_7': $i).
% 1.85/1.24  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.85/1.24  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.85/1.24  tff('#skF_5', type, '#skF_5': $i).
% 1.85/1.24  tff('#skF_6', type, '#skF_6': $i).
% 1.85/1.24  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.85/1.24  tff('#skF_2', type, '#skF_2': $i).
% 1.85/1.24  tff('#skF_3', type, '#skF_3': $i).
% 1.85/1.24  tff('#skF_1', type, '#skF_1': $i).
% 1.85/1.24  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.85/1.24  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.85/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.85/1.24  tff('#skF_4', type, '#skF_4': $i).
% 1.85/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.85/1.24  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.85/1.24  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.85/1.24  
% 1.85/1.25  tff(f_29, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_enumset1(E, F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l68_enumset1)).
% 1.85/1.25  tff(f_35, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 1.85/1.25  tff(f_31, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k1_enumset1(F, G, H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_enumset1)).
% 1.85/1.25  tff(f_42, negated_conjecture, ~(![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 1.85/1.25  tff(c_4, plain, (![A_3, F_8, D_6, C_5, G_9, E_7, B_4]: (k2_xboole_0(k2_enumset1(A_3, B_4, C_5, D_6), k1_enumset1(E_7, F_8, G_9))=k5_enumset1(A_3, B_4, C_5, D_6, E_7, F_8, G_9))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.85/1.25  tff(c_10, plain, (![A_21, B_22, C_23, D_24]: (k3_enumset1(A_21, A_21, B_22, C_23, D_24)=k2_enumset1(A_21, B_22, C_23, D_24))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.85/1.25  tff(c_84, plain, (![E_72, D_74, B_70, F_75, H_71, C_76, G_69, A_73]: (k2_xboole_0(k3_enumset1(A_73, B_70, C_76, D_74, E_72), k1_enumset1(F_75, G_69, H_71))=k6_enumset1(A_73, B_70, C_76, D_74, E_72, F_75, G_69, H_71))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.85/1.25  tff(c_93, plain, (![A_21, B_22, D_24, C_23, F_75, H_71, G_69]: (k6_enumset1(A_21, A_21, B_22, C_23, D_24, F_75, G_69, H_71)=k2_xboole_0(k2_enumset1(A_21, B_22, C_23, D_24), k1_enumset1(F_75, G_69, H_71)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_84])).
% 1.85/1.25  tff(c_96, plain, (![A_21, B_22, D_24, C_23, F_75, H_71, G_69]: (k6_enumset1(A_21, A_21, B_22, C_23, D_24, F_75, G_69, H_71)=k5_enumset1(A_21, B_22, C_23, D_24, F_75, G_69, H_71))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_93])).
% 1.85/1.25  tff(c_16, plain, (k6_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')!=k5_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.85/1.25  tff(c_99, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_96, c_16])).
% 1.85/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.85/1.25  
% 1.85/1.25  Inference rules
% 1.85/1.25  ----------------------
% 1.85/1.25  #Ref     : 0
% 1.85/1.25  #Sup     : 18
% 1.85/1.25  #Fact    : 0
% 1.85/1.25  #Define  : 0
% 1.85/1.25  #Split   : 0
% 1.85/1.25  #Chain   : 0
% 1.85/1.25  #Close   : 0
% 1.85/1.25  
% 1.85/1.25  Ordering : KBO
% 1.85/1.25  
% 1.85/1.25  Simplification rules
% 1.85/1.25  ----------------------
% 1.85/1.25  #Subsume      : 0
% 1.85/1.25  #Demod        : 3
% 1.85/1.25  #Tautology    : 16
% 1.85/1.25  #SimpNegUnit  : 0
% 1.85/1.25  #BackRed      : 1
% 1.85/1.25  
% 1.85/1.25  #Partial instantiations: 0
% 1.85/1.25  #Strategies tried      : 1
% 1.85/1.25  
% 1.85/1.25  Timing (in seconds)
% 1.85/1.25  ----------------------
% 1.85/1.25  Preprocessing        : 0.32
% 1.85/1.25  Parsing              : 0.17
% 1.85/1.25  CNF conversion       : 0.02
% 1.85/1.25  Main loop            : 0.10
% 1.85/1.26  Inferencing          : 0.05
% 1.85/1.26  Reduction            : 0.03
% 1.85/1.26  Demodulation         : 0.02
% 1.85/1.26  BG Simplification    : 0.01
% 1.85/1.26  Subsumption          : 0.01
% 1.85/1.26  Abstraction          : 0.01
% 1.85/1.26  MUC search           : 0.00
% 1.85/1.26  Cooper               : 0.00
% 1.85/1.26  Total                : 0.44
% 1.85/1.26  Index Insertion      : 0.00
% 1.85/1.26  Index Deletion       : 0.00
% 1.85/1.26  Index Matching       : 0.00
% 1.85/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
