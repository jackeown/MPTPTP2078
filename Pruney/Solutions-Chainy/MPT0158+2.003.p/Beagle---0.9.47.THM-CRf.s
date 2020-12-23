%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:18 EST 2020

% Result     : Theorem 1.71s
% Output     : CNFRefutation 1.71s
% Verified   : 
% Statistics : Number of formulae       :   29 (  29 expanded)
%              Number of leaves         :   22 (  22 expanded)
%              Depth                    :    4
%              Number of atoms          :   11 (  11 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_enumset1(A,B,C),k1_enumset1(D,E,F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l62_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_enumset1(E,F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l68_enumset1)).

tff(f_42,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

tff(c_6,plain,(
    ! [B_6,C_7,E_9,D_8,A_5,F_10] : k2_xboole_0(k1_enumset1(A_5,B_6,C_7),k1_enumset1(D_8,E_9,F_10)) = k4_enumset1(A_5,B_6,C_7,D_8,E_9,F_10) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_18,B_19,C_20] : k2_enumset1(A_18,A_18,B_19,C_20) = k1_enumset1(A_18,B_19,C_20) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_71,plain,(
    ! [F_52,B_56,G_54,E_58,A_55,C_53,D_57] : k2_xboole_0(k2_enumset1(A_55,B_56,C_53,D_57),k1_enumset1(E_58,F_52,G_54)) = k5_enumset1(A_55,B_56,C_53,D_57,E_58,F_52,G_54) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_80,plain,(
    ! [F_52,G_54,E_58,A_18,C_20,B_19] : k5_enumset1(A_18,A_18,B_19,C_20,E_58,F_52,G_54) = k2_xboole_0(k1_enumset1(A_18,B_19,C_20),k1_enumset1(E_58,F_52,G_54)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_71])).

tff(c_83,plain,(
    ! [F_52,G_54,E_58,A_18,C_20,B_19] : k5_enumset1(A_18,A_18,B_19,C_20,E_58,F_52,G_54) = k4_enumset1(A_18,B_19,C_20,E_58,F_52,G_54) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_80])).

tff(c_16,plain,(
    k5_enumset1('#skF_1','#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6') != k4_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_86,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:46:57 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.71/1.09  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.71/1.10  
% 1.71/1.10  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.71/1.10  %$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.71/1.10  
% 1.71/1.10  %Foreground sorts:
% 1.71/1.10  
% 1.71/1.10  
% 1.71/1.10  %Background operators:
% 1.71/1.10  
% 1.71/1.10  
% 1.71/1.10  %Foreground operators:
% 1.71/1.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.71/1.10  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.71/1.10  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.71/1.10  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.71/1.10  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.71/1.10  tff('#skF_5', type, '#skF_5': $i).
% 1.71/1.10  tff('#skF_6', type, '#skF_6': $i).
% 1.71/1.10  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.71/1.10  tff('#skF_2', type, '#skF_2': $i).
% 1.71/1.10  tff('#skF_3', type, '#skF_3': $i).
% 1.71/1.10  tff('#skF_1', type, '#skF_1': $i).
% 1.71/1.10  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.71/1.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.71/1.10  tff('#skF_4', type, '#skF_4': $i).
% 1.71/1.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.71/1.10  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.71/1.10  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.71/1.10  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.71/1.10  
% 1.71/1.11  tff(f_31, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_enumset1(A, B, C), k1_enumset1(D, E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l62_enumset1)).
% 1.71/1.11  tff(f_35, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 1.71/1.11  tff(f_33, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_enumset1(E, F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l68_enumset1)).
% 1.71/1.11  tff(f_42, negated_conjecture, ~(![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 1.71/1.11  tff(c_6, plain, (![B_6, C_7, E_9, D_8, A_5, F_10]: (k2_xboole_0(k1_enumset1(A_5, B_6, C_7), k1_enumset1(D_8, E_9, F_10))=k4_enumset1(A_5, B_6, C_7, D_8, E_9, F_10))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.71/1.11  tff(c_10, plain, (![A_18, B_19, C_20]: (k2_enumset1(A_18, A_18, B_19, C_20)=k1_enumset1(A_18, B_19, C_20))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.71/1.11  tff(c_71, plain, (![F_52, B_56, G_54, E_58, A_55, C_53, D_57]: (k2_xboole_0(k2_enumset1(A_55, B_56, C_53, D_57), k1_enumset1(E_58, F_52, G_54))=k5_enumset1(A_55, B_56, C_53, D_57, E_58, F_52, G_54))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.71/1.11  tff(c_80, plain, (![F_52, G_54, E_58, A_18, C_20, B_19]: (k5_enumset1(A_18, A_18, B_19, C_20, E_58, F_52, G_54)=k2_xboole_0(k1_enumset1(A_18, B_19, C_20), k1_enumset1(E_58, F_52, G_54)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_71])).
% 1.71/1.11  tff(c_83, plain, (![F_52, G_54, E_58, A_18, C_20, B_19]: (k5_enumset1(A_18, A_18, B_19, C_20, E_58, F_52, G_54)=k4_enumset1(A_18, B_19, C_20, E_58, F_52, G_54))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_80])).
% 1.71/1.11  tff(c_16, plain, (k5_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')!=k4_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.71/1.11  tff(c_86, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_83, c_16])).
% 1.71/1.11  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.71/1.11  
% 1.71/1.11  Inference rules
% 1.71/1.11  ----------------------
% 1.71/1.11  #Ref     : 0
% 1.71/1.11  #Sup     : 15
% 1.71/1.11  #Fact    : 0
% 1.71/1.11  #Define  : 0
% 1.71/1.11  #Split   : 0
% 1.71/1.11  #Chain   : 0
% 1.71/1.11  #Close   : 0
% 1.71/1.11  
% 1.71/1.11  Ordering : KBO
% 1.71/1.11  
% 1.71/1.11  Simplification rules
% 1.71/1.11  ----------------------
% 1.71/1.11  #Subsume      : 0
% 1.71/1.11  #Demod        : 2
% 1.71/1.11  #Tautology    : 14
% 1.71/1.11  #SimpNegUnit  : 0
% 1.71/1.11  #BackRed      : 1
% 1.71/1.11  
% 1.71/1.11  #Partial instantiations: 0
% 1.71/1.11  #Strategies tried      : 1
% 1.71/1.11  
% 1.71/1.11  Timing (in seconds)
% 1.71/1.11  ----------------------
% 1.71/1.11  Preprocessing        : 0.28
% 1.71/1.11  Parsing              : 0.15
% 1.71/1.11  CNF conversion       : 0.02
% 1.71/1.11  Main loop            : 0.09
% 1.71/1.11  Inferencing          : 0.04
% 1.71/1.11  Reduction            : 0.03
% 1.71/1.11  Demodulation         : 0.02
% 1.71/1.11  BG Simplification    : 0.01
% 1.71/1.11  Subsumption          : 0.01
% 1.71/1.11  Abstraction          : 0.01
% 1.71/1.11  MUC search           : 0.00
% 1.71/1.11  Cooper               : 0.00
% 1.71/1.11  Total                : 0.39
% 1.71/1.11  Index Insertion      : 0.00
% 1.71/1.11  Index Deletion       : 0.00
% 1.71/1.11  Index Matching       : 0.00
% 1.71/1.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
