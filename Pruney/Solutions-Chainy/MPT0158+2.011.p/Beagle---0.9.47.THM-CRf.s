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
% DateTime   : Thu Dec  3 09:46:20 EST 2020

% Result     : Theorem 3.37s
% Output     : CNFRefutation 3.37s
% Verified   : 
% Statistics : Number of formulae       :   34 (  35 expanded)
%              Number of leaves         :   23 (  24 expanded)
%              Depth                    :    6
%              Number of atoms          :   18 (  19 expanded)
%              Number of equality atoms :   13 (  14 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(f_35,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k1_tarski(A),k4_enumset1(B,C,D,E,F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_tarski(A),k3_enumset1(B,C,D,E,F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_enumset1)).

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_48,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

tff(c_8,plain,(
    ! [G_17,F_16,D_14,E_15,B_12,A_11,C_13] : k2_xboole_0(k1_tarski(A_11),k4_enumset1(B_12,C_13,D_14,E_15,F_16,G_17)) = k5_enumset1(A_11,B_12,C_13,D_14,E_15,F_16,G_17) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6,plain,(
    ! [B_6,C_7,E_9,D_8,A_5,F_10] : k2_xboole_0(k1_tarski(A_5),k3_enumset1(B_6,C_7,D_8,E_9,F_10)) = k4_enumset1(A_5,B_6,C_7,D_8,E_9,F_10) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_93,plain,(
    ! [A_58,B_56,E_59,C_57,F_55,D_54] : k2_xboole_0(k1_tarski(A_58),k3_enumset1(B_56,C_57,D_54,E_59,F_55)) = k4_enumset1(A_58,B_56,C_57,D_54,E_59,F_55) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(A_3,k2_xboole_0(A_3,B_4)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_31,plain,(
    ! [A_36,B_37] :
      ( k2_xboole_0(A_36,B_37) = B_37
      | ~ r1_tarski(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_35,plain,(
    ! [A_3,B_4] : k2_xboole_0(A_3,k2_xboole_0(A_3,B_4)) = k2_xboole_0(A_3,B_4) ),
    inference(resolution,[status(thm)],[c_4,c_31])).

tff(c_99,plain,(
    ! [A_58,B_56,E_59,C_57,F_55,D_54] : k2_xboole_0(k1_tarski(A_58),k4_enumset1(A_58,B_56,C_57,D_54,E_59,F_55)) = k2_xboole_0(k1_tarski(A_58),k3_enumset1(B_56,C_57,D_54,E_59,F_55)) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_35])).

tff(c_726,plain,(
    ! [C_143,D_141,E_144,F_142,B_139,A_140] : k2_xboole_0(k1_tarski(A_140),k4_enumset1(A_140,B_139,C_143,D_141,E_144,F_142)) = k4_enumset1(A_140,B_139,C_143,D_141,E_144,F_142) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_99])).

tff(c_763,plain,(
    ! [G_17,F_16,D_14,E_15,B_12,C_13] : k5_enumset1(B_12,B_12,C_13,D_14,E_15,F_16,G_17) = k4_enumset1(B_12,C_13,D_14,E_15,F_16,G_17) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_726])).

tff(c_20,plain,(
    k5_enumset1('#skF_1','#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6') != k4_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1574,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_763,c_20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:16:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.37/1.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.37/1.55  
% 3.37/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.37/1.55  %$ r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.37/1.55  
% 3.37/1.55  %Foreground sorts:
% 3.37/1.55  
% 3.37/1.55  
% 3.37/1.55  %Background operators:
% 3.37/1.55  
% 3.37/1.55  
% 3.37/1.55  %Foreground operators:
% 3.37/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.37/1.55  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.37/1.55  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.37/1.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.37/1.55  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.37/1.55  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.37/1.55  tff('#skF_5', type, '#skF_5': $i).
% 3.37/1.55  tff('#skF_6', type, '#skF_6': $i).
% 3.37/1.55  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.37/1.55  tff('#skF_2', type, '#skF_2': $i).
% 3.37/1.55  tff('#skF_3', type, '#skF_3': $i).
% 3.37/1.55  tff('#skF_1', type, '#skF_1': $i).
% 3.37/1.55  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.37/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.37/1.55  tff('#skF_4', type, '#skF_4': $i).
% 3.37/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.37/1.55  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.37/1.55  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.37/1.55  
% 3.37/1.56  tff(f_35, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k1_tarski(A), k4_enumset1(B, C, D, E, F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_enumset1)).
% 3.37/1.56  tff(f_33, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_tarski(A), k3_enumset1(B, C, D, E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_enumset1)).
% 3.37/1.56  tff(f_31, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.37/1.56  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.37/1.56  tff(f_48, negated_conjecture, ~(![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 3.37/1.56  tff(c_8, plain, (![G_17, F_16, D_14, E_15, B_12, A_11, C_13]: (k2_xboole_0(k1_tarski(A_11), k4_enumset1(B_12, C_13, D_14, E_15, F_16, G_17))=k5_enumset1(A_11, B_12, C_13, D_14, E_15, F_16, G_17))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.37/1.56  tff(c_6, plain, (![B_6, C_7, E_9, D_8, A_5, F_10]: (k2_xboole_0(k1_tarski(A_5), k3_enumset1(B_6, C_7, D_8, E_9, F_10))=k4_enumset1(A_5, B_6, C_7, D_8, E_9, F_10))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.37/1.56  tff(c_93, plain, (![A_58, B_56, E_59, C_57, F_55, D_54]: (k2_xboole_0(k1_tarski(A_58), k3_enumset1(B_56, C_57, D_54, E_59, F_55))=k4_enumset1(A_58, B_56, C_57, D_54, E_59, F_55))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.37/1.56  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(A_3, k2_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.37/1.56  tff(c_31, plain, (![A_36, B_37]: (k2_xboole_0(A_36, B_37)=B_37 | ~r1_tarski(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.37/1.56  tff(c_35, plain, (![A_3, B_4]: (k2_xboole_0(A_3, k2_xboole_0(A_3, B_4))=k2_xboole_0(A_3, B_4))), inference(resolution, [status(thm)], [c_4, c_31])).
% 3.37/1.56  tff(c_99, plain, (![A_58, B_56, E_59, C_57, F_55, D_54]: (k2_xboole_0(k1_tarski(A_58), k4_enumset1(A_58, B_56, C_57, D_54, E_59, F_55))=k2_xboole_0(k1_tarski(A_58), k3_enumset1(B_56, C_57, D_54, E_59, F_55)))), inference(superposition, [status(thm), theory('equality')], [c_93, c_35])).
% 3.37/1.56  tff(c_726, plain, (![C_143, D_141, E_144, F_142, B_139, A_140]: (k2_xboole_0(k1_tarski(A_140), k4_enumset1(A_140, B_139, C_143, D_141, E_144, F_142))=k4_enumset1(A_140, B_139, C_143, D_141, E_144, F_142))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_99])).
% 3.37/1.56  tff(c_763, plain, (![G_17, F_16, D_14, E_15, B_12, C_13]: (k5_enumset1(B_12, B_12, C_13, D_14, E_15, F_16, G_17)=k4_enumset1(B_12, C_13, D_14, E_15, F_16, G_17))), inference(superposition, [status(thm), theory('equality')], [c_8, c_726])).
% 3.37/1.56  tff(c_20, plain, (k5_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')!=k4_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.37/1.56  tff(c_1574, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_763, c_20])).
% 3.37/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.37/1.56  
% 3.37/1.56  Inference rules
% 3.37/1.56  ----------------------
% 3.37/1.56  #Ref     : 0
% 3.37/1.56  #Sup     : 368
% 3.37/1.56  #Fact    : 0
% 3.37/1.56  #Define  : 0
% 3.37/1.56  #Split   : 0
% 3.37/1.56  #Chain   : 0
% 3.37/1.56  #Close   : 0
% 3.37/1.56  
% 3.37/1.56  Ordering : KBO
% 3.37/1.56  
% 3.37/1.56  Simplification rules
% 3.37/1.56  ----------------------
% 3.37/1.56  #Subsume      : 14
% 3.37/1.56  #Demod        : 338
% 3.37/1.56  #Tautology    : 288
% 3.37/1.56  #SimpNegUnit  : 0
% 3.37/1.56  #BackRed      : 1
% 3.37/1.56  
% 3.37/1.56  #Partial instantiations: 0
% 3.37/1.56  #Strategies tried      : 1
% 3.37/1.56  
% 3.37/1.56  Timing (in seconds)
% 3.37/1.56  ----------------------
% 3.37/1.57  Preprocessing        : 0.30
% 3.37/1.57  Parsing              : 0.16
% 3.37/1.57  CNF conversion       : 0.02
% 3.37/1.57  Main loop            : 0.50
% 3.37/1.57  Inferencing          : 0.22
% 3.37/1.57  Reduction            : 0.19
% 3.37/1.57  Demodulation         : 0.15
% 3.37/1.57  BG Simplification    : 0.02
% 3.37/1.57  Subsumption          : 0.05
% 3.37/1.57  Abstraction          : 0.04
% 3.37/1.57  MUC search           : 0.00
% 3.37/1.57  Cooper               : 0.00
% 3.37/1.57  Total                : 0.83
% 3.37/1.57  Index Insertion      : 0.00
% 3.37/1.57  Index Deletion       : 0.00
% 3.37/1.57  Index Matching       : 0.00
% 3.37/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
