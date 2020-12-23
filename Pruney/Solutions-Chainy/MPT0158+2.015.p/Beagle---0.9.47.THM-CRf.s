%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:20 EST 2020

% Result     : Theorem 1.98s
% Output     : CNFRefutation 1.98s
% Verified   : 
% Statistics : Number of formulae       :   30 (  30 expanded)
%              Number of leaves         :   23 (  23 expanded)
%              Depth                    :    4
%              Number of atoms          :   11 (  11 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_29,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_tarski(A),k3_enumset1(B,C,D,E,F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_enumset1)).

tff(f_33,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k2_tarski(A,B),k3_enumset1(C,D,E,F,G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_enumset1)).

tff(f_44,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(c_4,plain,(
    ! [A_3,F_8,D_6,C_5,E_7,B_4] : k2_xboole_0(k1_tarski(A_3),k3_enumset1(B_4,C_5,D_6,E_7,F_8)) = k4_enumset1(A_3,B_4,C_5,D_6,E_7,F_8) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_8,plain,(
    ! [A_16] : k2_tarski(A_16,A_16) = k1_tarski(A_16) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_115,plain,(
    ! [G_64,A_65,D_62,C_61,F_59,E_63,B_60] : k2_xboole_0(k2_tarski(A_65,B_60),k3_enumset1(C_61,D_62,E_63,F_59,G_64)) = k5_enumset1(A_65,B_60,C_61,D_62,E_63,F_59,G_64) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_127,plain,(
    ! [G_64,A_16,D_62,C_61,F_59,E_63] : k5_enumset1(A_16,A_16,C_61,D_62,E_63,F_59,G_64) = k2_xboole_0(k1_tarski(A_16),k3_enumset1(C_61,D_62,E_63,F_59,G_64)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_115])).

tff(c_130,plain,(
    ! [G_64,A_16,D_62,C_61,F_59,E_63] : k5_enumset1(A_16,A_16,C_61,D_62,E_63,F_59,G_64) = k4_enumset1(A_16,C_61,D_62,E_63,F_59,G_64) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_127])).

tff(c_18,plain,(
    k5_enumset1('#skF_1','#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6') != k4_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_215,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:36:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.98/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.25  
% 1.98/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.25  %$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.98/1.25  
% 1.98/1.25  %Foreground sorts:
% 1.98/1.25  
% 1.98/1.25  
% 1.98/1.25  %Background operators:
% 1.98/1.25  
% 1.98/1.25  
% 1.98/1.25  %Foreground operators:
% 1.98/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.98/1.25  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.98/1.25  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.98/1.25  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.98/1.25  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.98/1.25  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.98/1.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.98/1.25  tff('#skF_5', type, '#skF_5': $i).
% 1.98/1.25  tff('#skF_6', type, '#skF_6': $i).
% 1.98/1.25  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.98/1.25  tff('#skF_2', type, '#skF_2': $i).
% 1.98/1.25  tff('#skF_3', type, '#skF_3': $i).
% 1.98/1.25  tff('#skF_1', type, '#skF_1': $i).
% 1.98/1.25  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.98/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.98/1.25  tff('#skF_4', type, '#skF_4': $i).
% 1.98/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.98/1.25  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.98/1.25  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.98/1.25  
% 1.98/1.26  tff(f_29, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_tarski(A), k3_enumset1(B, C, D, E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_enumset1)).
% 1.98/1.26  tff(f_33, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.98/1.26  tff(f_31, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k2_tarski(A, B), k3_enumset1(C, D, E, F, G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_enumset1)).
% 1.98/1.26  tff(f_44, negated_conjecture, ~(![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 1.98/1.26  tff(c_4, plain, (![A_3, F_8, D_6, C_5, E_7, B_4]: (k2_xboole_0(k1_tarski(A_3), k3_enumset1(B_4, C_5, D_6, E_7, F_8))=k4_enumset1(A_3, B_4, C_5, D_6, E_7, F_8))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.98/1.26  tff(c_8, plain, (![A_16]: (k2_tarski(A_16, A_16)=k1_tarski(A_16))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.98/1.26  tff(c_115, plain, (![G_64, A_65, D_62, C_61, F_59, E_63, B_60]: (k2_xboole_0(k2_tarski(A_65, B_60), k3_enumset1(C_61, D_62, E_63, F_59, G_64))=k5_enumset1(A_65, B_60, C_61, D_62, E_63, F_59, G_64))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.98/1.26  tff(c_127, plain, (![G_64, A_16, D_62, C_61, F_59, E_63]: (k5_enumset1(A_16, A_16, C_61, D_62, E_63, F_59, G_64)=k2_xboole_0(k1_tarski(A_16), k3_enumset1(C_61, D_62, E_63, F_59, G_64)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_115])).
% 1.98/1.26  tff(c_130, plain, (![G_64, A_16, D_62, C_61, F_59, E_63]: (k5_enumset1(A_16, A_16, C_61, D_62, E_63, F_59, G_64)=k4_enumset1(A_16, C_61, D_62, E_63, F_59, G_64))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_127])).
% 1.98/1.26  tff(c_18, plain, (k5_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')!=k4_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.98/1.26  tff(c_215, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_130, c_18])).
% 1.98/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.26  
% 1.98/1.26  Inference rules
% 1.98/1.26  ----------------------
% 1.98/1.26  #Ref     : 0
% 1.98/1.26  #Sup     : 45
% 1.98/1.26  #Fact    : 0
% 1.98/1.26  #Define  : 0
% 1.98/1.26  #Split   : 0
% 1.98/1.26  #Chain   : 0
% 1.98/1.26  #Close   : 0
% 1.98/1.26  
% 1.98/1.26  Ordering : KBO
% 1.98/1.26  
% 1.98/1.26  Simplification rules
% 1.98/1.26  ----------------------
% 1.98/1.26  #Subsume      : 0
% 1.98/1.26  #Demod        : 11
% 1.98/1.26  #Tautology    : 34
% 1.98/1.26  #SimpNegUnit  : 0
% 1.98/1.26  #BackRed      : 1
% 1.98/1.26  
% 1.98/1.26  #Partial instantiations: 0
% 1.98/1.26  #Strategies tried      : 1
% 1.98/1.26  
% 1.98/1.26  Timing (in seconds)
% 1.98/1.26  ----------------------
% 1.98/1.26  Preprocessing        : 0.30
% 1.98/1.26  Parsing              : 0.16
% 1.98/1.26  CNF conversion       : 0.02
% 1.98/1.26  Main loop            : 0.15
% 1.98/1.26  Inferencing          : 0.07
% 1.98/1.26  Reduction            : 0.05
% 1.98/1.26  Demodulation         : 0.04
% 1.98/1.26  BG Simplification    : 0.01
% 1.98/1.26  Subsumption          : 0.01
% 1.98/1.26  Abstraction          : 0.01
% 1.98/1.26  MUC search           : 0.00
% 1.98/1.26  Cooper               : 0.00
% 1.98/1.26  Total                : 0.47
% 1.98/1.26  Index Insertion      : 0.00
% 1.98/1.26  Index Deletion       : 0.00
% 1.98/1.26  Index Matching       : 0.00
% 1.98/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
