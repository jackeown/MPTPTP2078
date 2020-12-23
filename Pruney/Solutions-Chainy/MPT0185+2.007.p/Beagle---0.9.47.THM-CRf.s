%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:47 EST 2020

% Result     : Theorem 2.08s
% Output     : CNFRefutation 2.35s
% Verified   : 
% Statistics : Number of formulae       :   26 (  29 expanded)
%              Number of leaves         :   16 (  18 expanded)
%              Depth                    :    6
%              Number of atoms          :   14 (  17 expanded)
%              Number of equality atoms :   13 (  16 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_35,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(A,C,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_tarski(A,B),k1_enumset1(C,D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_38,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,B,D,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_enumset1)).

tff(c_10,plain,(
    ! [A_15,C_17,B_16] : k1_enumset1(A_15,C_17,B_16) = k1_enumset1(A_15,B_16,C_17) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_127,plain,(
    ! [A_36,E_32,D_33,B_34,C_35] : k2_xboole_0(k2_tarski(A_36,B_34),k1_enumset1(C_35,D_33,E_32)) = k3_enumset1(A_36,B_34,C_35,D_33,E_32) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_278,plain,(
    ! [C_51,B_53,A_52,A_55,B_54] : k2_xboole_0(k2_tarski(A_52,B_54),k1_enumset1(A_55,C_51,B_53)) = k3_enumset1(A_52,B_54,A_55,B_53,C_51) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_127])).

tff(c_2,plain,(
    ! [B_2,C_3,A_1,E_5,D_4] : k2_xboole_0(k2_tarski(A_1,B_2),k1_enumset1(C_3,D_4,E_5)) = k3_enumset1(A_1,B_2,C_3,D_4,E_5) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_418,plain,(
    ! [B_67,A_66,C_63,A_64,B_65] : k3_enumset1(A_64,B_67,A_66,C_63,B_65) = k3_enumset1(A_64,B_67,A_66,B_65,C_63) ),
    inference(superposition,[status(thm),theory(equality)],[c_278,c_2])).

tff(c_8,plain,(
    ! [A_11,B_12,C_13,D_14] : k3_enumset1(A_11,A_11,B_12,C_13,D_14) = k2_enumset1(A_11,B_12,C_13,D_14) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_512,plain,(
    ! [B_68,A_69,C_70,B_71] : k3_enumset1(B_68,B_68,A_69,C_70,B_71) = k2_enumset1(B_68,A_69,B_71,C_70) ),
    inference(superposition,[status(thm),theory(equality)],[c_418,c_8])).

tff(c_532,plain,(
    ! [B_68,A_69,C_70,B_71] : k2_enumset1(B_68,A_69,C_70,B_71) = k2_enumset1(B_68,A_69,B_71,C_70) ),
    inference(superposition,[status(thm),theory(equality)],[c_512,c_8])).

tff(c_12,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_2','#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_563,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_532,c_12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.15/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.16/0.36  % Computer   : n024.cluster.edu
% 0.16/0.36  % Model      : x86_64 x86_64
% 0.16/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.36  % Memory     : 8042.1875MB
% 0.16/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.36  % CPULimit   : 60
% 0.16/0.36  % DateTime   : Tue Dec  1 13:44:21 EST 2020
% 0.22/0.36  % CPUTime    : 
% 0.22/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.08/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.30  
% 2.08/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.31  %$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.08/1.31  
% 2.08/1.31  %Foreground sorts:
% 2.08/1.31  
% 2.08/1.31  
% 2.08/1.31  %Background operators:
% 2.08/1.31  
% 2.08/1.31  
% 2.08/1.31  %Foreground operators:
% 2.08/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.08/1.31  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.08/1.31  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.08/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.08/1.31  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.08/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.08/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.08/1.31  tff('#skF_1', type, '#skF_1': $i).
% 2.08/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.08/1.31  tff('#skF_4', type, '#skF_4': $i).
% 2.08/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.08/1.31  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.08/1.31  
% 2.35/1.31  tff(f_35, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(A, C, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_enumset1)).
% 2.35/1.31  tff(f_27, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_tarski(A, B), k1_enumset1(C, D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_enumset1)).
% 2.35/1.31  tff(f_33, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 2.35/1.31  tff(f_38, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, B, D, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_enumset1)).
% 2.35/1.31  tff(c_10, plain, (![A_15, C_17, B_16]: (k1_enumset1(A_15, C_17, B_16)=k1_enumset1(A_15, B_16, C_17))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.35/1.31  tff(c_127, plain, (![A_36, E_32, D_33, B_34, C_35]: (k2_xboole_0(k2_tarski(A_36, B_34), k1_enumset1(C_35, D_33, E_32))=k3_enumset1(A_36, B_34, C_35, D_33, E_32))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.35/1.31  tff(c_278, plain, (![C_51, B_53, A_52, A_55, B_54]: (k2_xboole_0(k2_tarski(A_52, B_54), k1_enumset1(A_55, C_51, B_53))=k3_enumset1(A_52, B_54, A_55, B_53, C_51))), inference(superposition, [status(thm), theory('equality')], [c_10, c_127])).
% 2.35/1.31  tff(c_2, plain, (![B_2, C_3, A_1, E_5, D_4]: (k2_xboole_0(k2_tarski(A_1, B_2), k1_enumset1(C_3, D_4, E_5))=k3_enumset1(A_1, B_2, C_3, D_4, E_5))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.35/1.31  tff(c_418, plain, (![B_67, A_66, C_63, A_64, B_65]: (k3_enumset1(A_64, B_67, A_66, C_63, B_65)=k3_enumset1(A_64, B_67, A_66, B_65, C_63))), inference(superposition, [status(thm), theory('equality')], [c_278, c_2])).
% 2.35/1.31  tff(c_8, plain, (![A_11, B_12, C_13, D_14]: (k3_enumset1(A_11, A_11, B_12, C_13, D_14)=k2_enumset1(A_11, B_12, C_13, D_14))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.35/1.31  tff(c_512, plain, (![B_68, A_69, C_70, B_71]: (k3_enumset1(B_68, B_68, A_69, C_70, B_71)=k2_enumset1(B_68, A_69, B_71, C_70))), inference(superposition, [status(thm), theory('equality')], [c_418, c_8])).
% 2.35/1.31  tff(c_532, plain, (![B_68, A_69, C_70, B_71]: (k2_enumset1(B_68, A_69, C_70, B_71)=k2_enumset1(B_68, A_69, B_71, C_70))), inference(superposition, [status(thm), theory('equality')], [c_512, c_8])).
% 2.35/1.31  tff(c_12, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_2', '#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.35/1.31  tff(c_563, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_532, c_12])).
% 2.35/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.35/1.31  
% 2.35/1.31  Inference rules
% 2.35/1.31  ----------------------
% 2.35/1.31  #Ref     : 0
% 2.35/1.31  #Sup     : 132
% 2.35/1.31  #Fact    : 0
% 2.35/1.31  #Define  : 0
% 2.35/1.31  #Split   : 0
% 2.35/1.31  #Chain   : 0
% 2.35/1.31  #Close   : 0
% 2.35/1.31  
% 2.35/1.31  Ordering : KBO
% 2.35/1.31  
% 2.35/1.31  Simplification rules
% 2.35/1.31  ----------------------
% 2.35/1.31  #Subsume      : 19
% 2.35/1.31  #Demod        : 37
% 2.35/1.31  #Tautology    : 90
% 2.35/1.31  #SimpNegUnit  : 0
% 2.35/1.31  #BackRed      : 1
% 2.35/1.31  
% 2.35/1.31  #Partial instantiations: 0
% 2.35/1.31  #Strategies tried      : 1
% 2.35/1.31  
% 2.35/1.31  Timing (in seconds)
% 2.35/1.31  ----------------------
% 2.35/1.32  Preprocessing        : 0.27
% 2.35/1.32  Parsing              : 0.14
% 2.35/1.32  CNF conversion       : 0.02
% 2.35/1.32  Main loop            : 0.27
% 2.35/1.32  Inferencing          : 0.11
% 2.35/1.32  Reduction            : 0.10
% 2.35/1.32  Demodulation         : 0.08
% 2.35/1.32  BG Simplification    : 0.01
% 2.35/1.32  Subsumption          : 0.03
% 2.35/1.32  Abstraction          : 0.02
% 2.35/1.32  MUC search           : 0.00
% 2.35/1.32  Cooper               : 0.00
% 2.35/1.32  Total                : 0.56
% 2.35/1.32  Index Insertion      : 0.00
% 2.35/1.32  Index Deletion       : 0.00
% 2.35/1.32  Index Matching       : 0.00
% 2.35/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
