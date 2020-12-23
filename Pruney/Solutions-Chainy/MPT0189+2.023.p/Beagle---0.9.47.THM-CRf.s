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
% DateTime   : Thu Dec  3 09:46:53 EST 2020

% Result     : Theorem 2.34s
% Output     : CNFRefutation 2.34s
% Verified   : 
% Statistics : Number of formulae       :   38 (  65 expanded)
%              Number of leaves         :   25 (  35 expanded)
%              Depth                    :    6
%              Number of atoms          :   19 (  46 expanded)
%              Number of equality atoms :   18 (  45 expanded)
%              Maximal formula depth    :   10 (   5 average)
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

tff(f_33,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(B,C,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_enumset1)).

tff(f_53,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_51,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_tarski(E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,C,B,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_enumset1)).

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,A,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_enumset1)).

tff(c_8,plain,(
    ! [B_14,C_15,A_13] : k1_enumset1(B_14,C_15,A_13) = k1_enumset1(A_13,B_14,C_15) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_28,plain,(
    ! [A_59,B_60,C_61,D_62] : k3_enumset1(A_59,A_59,B_60,C_61,D_62) = k2_enumset1(A_59,B_60,C_61,D_62) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_26,plain,(
    ! [A_56,B_57,C_58] : k2_enumset1(A_56,A_56,B_57,C_58) = k1_enumset1(A_56,B_57,C_58) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_315,plain,(
    ! [D_109,A_111,B_108,E_110,C_107] : k2_xboole_0(k2_enumset1(A_111,B_108,C_107,D_109),k1_tarski(E_110)) = k3_enumset1(A_111,B_108,C_107,D_109,E_110) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_333,plain,(
    ! [A_56,B_57,C_58,E_110] : k3_enumset1(A_56,A_56,B_57,C_58,E_110) = k2_xboole_0(k1_enumset1(A_56,B_57,C_58),k1_tarski(E_110)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_315])).

tff(c_337,plain,(
    ! [A_112,B_113,C_114,E_115] : k2_xboole_0(k1_enumset1(A_112,B_113,C_114),k1_tarski(E_115)) = k2_enumset1(A_112,B_113,C_114,E_115) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_333])).

tff(c_448,plain,(
    ! [A_134,B_135,C_136,E_137] : k2_xboole_0(k1_enumset1(A_134,B_135,C_136),k1_tarski(E_137)) = k2_enumset1(B_135,C_136,A_134,E_137) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_337])).

tff(c_336,plain,(
    ! [A_56,B_57,C_58,E_110] : k2_xboole_0(k1_enumset1(A_56,B_57,C_58),k1_tarski(E_110)) = k2_enumset1(A_56,B_57,C_58,E_110) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_333])).

tff(c_454,plain,(
    ! [B_135,C_136,A_134,E_137] : k2_enumset1(B_135,C_136,A_134,E_137) = k2_enumset1(A_134,B_135,C_136,E_137) ),
    inference(superposition,[status(thm),theory(equality)],[c_448,c_336])).

tff(c_10,plain,(
    ! [A_16,C_18,B_17,D_19] : k2_enumset1(A_16,C_18,B_17,D_19) = k2_enumset1(A_16,B_17,C_18,D_19) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_34,plain,(
    k2_enumset1('#skF_2','#skF_1','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_35,plain,(
    k2_enumset1('#skF_2','#skF_1','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_3','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_34])).

tff(c_512,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_454,c_454,c_35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:53:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.34/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.34/1.32  
% 2.34/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.34/1.32  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.34/1.32  
% 2.34/1.32  %Foreground sorts:
% 2.34/1.32  
% 2.34/1.32  
% 2.34/1.32  %Background operators:
% 2.34/1.32  
% 2.34/1.32  
% 2.34/1.32  %Foreground operators:
% 2.34/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.34/1.32  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.34/1.32  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.34/1.32  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.34/1.32  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.34/1.32  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.34/1.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.34/1.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.34/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.34/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.34/1.32  tff('#skF_1', type, '#skF_1': $i).
% 2.34/1.32  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.34/1.32  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.34/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.34/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.34/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.34/1.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.34/1.32  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.34/1.32  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.34/1.32  
% 2.34/1.33  tff(f_33, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(B, C, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_enumset1)).
% 2.34/1.33  tff(f_53, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 2.34/1.33  tff(f_51, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.34/1.33  tff(f_37, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_tarski(E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_enumset1)).
% 2.34/1.33  tff(f_35, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, C, B, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t104_enumset1)).
% 2.34/1.33  tff(f_60, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, A, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t108_enumset1)).
% 2.34/1.33  tff(c_8, plain, (![B_14, C_15, A_13]: (k1_enumset1(B_14, C_15, A_13)=k1_enumset1(A_13, B_14, C_15))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.34/1.33  tff(c_28, plain, (![A_59, B_60, C_61, D_62]: (k3_enumset1(A_59, A_59, B_60, C_61, D_62)=k2_enumset1(A_59, B_60, C_61, D_62))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.34/1.33  tff(c_26, plain, (![A_56, B_57, C_58]: (k2_enumset1(A_56, A_56, B_57, C_58)=k1_enumset1(A_56, B_57, C_58))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.34/1.33  tff(c_315, plain, (![D_109, A_111, B_108, E_110, C_107]: (k2_xboole_0(k2_enumset1(A_111, B_108, C_107, D_109), k1_tarski(E_110))=k3_enumset1(A_111, B_108, C_107, D_109, E_110))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.34/1.33  tff(c_333, plain, (![A_56, B_57, C_58, E_110]: (k3_enumset1(A_56, A_56, B_57, C_58, E_110)=k2_xboole_0(k1_enumset1(A_56, B_57, C_58), k1_tarski(E_110)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_315])).
% 2.34/1.33  tff(c_337, plain, (![A_112, B_113, C_114, E_115]: (k2_xboole_0(k1_enumset1(A_112, B_113, C_114), k1_tarski(E_115))=k2_enumset1(A_112, B_113, C_114, E_115))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_333])).
% 2.34/1.33  tff(c_448, plain, (![A_134, B_135, C_136, E_137]: (k2_xboole_0(k1_enumset1(A_134, B_135, C_136), k1_tarski(E_137))=k2_enumset1(B_135, C_136, A_134, E_137))), inference(superposition, [status(thm), theory('equality')], [c_8, c_337])).
% 2.34/1.33  tff(c_336, plain, (![A_56, B_57, C_58, E_110]: (k2_xboole_0(k1_enumset1(A_56, B_57, C_58), k1_tarski(E_110))=k2_enumset1(A_56, B_57, C_58, E_110))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_333])).
% 2.34/1.33  tff(c_454, plain, (![B_135, C_136, A_134, E_137]: (k2_enumset1(B_135, C_136, A_134, E_137)=k2_enumset1(A_134, B_135, C_136, E_137))), inference(superposition, [status(thm), theory('equality')], [c_448, c_336])).
% 2.34/1.33  tff(c_10, plain, (![A_16, C_18, B_17, D_19]: (k2_enumset1(A_16, C_18, B_17, D_19)=k2_enumset1(A_16, B_17, C_18, D_19))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.34/1.33  tff(c_34, plain, (k2_enumset1('#skF_2', '#skF_1', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.34/1.33  tff(c_35, plain, (k2_enumset1('#skF_2', '#skF_1', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_3', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_34])).
% 2.34/1.33  tff(c_512, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_454, c_454, c_35])).
% 2.34/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.34/1.33  
% 2.34/1.33  Inference rules
% 2.34/1.33  ----------------------
% 2.34/1.33  #Ref     : 0
% 2.34/1.33  #Sup     : 112
% 2.34/1.33  #Fact    : 0
% 2.34/1.33  #Define  : 0
% 2.34/1.33  #Split   : 0
% 2.34/1.33  #Chain   : 0
% 2.34/1.33  #Close   : 0
% 2.34/1.33  
% 2.34/1.33  Ordering : KBO
% 2.34/1.33  
% 2.34/1.33  Simplification rules
% 2.34/1.33  ----------------------
% 2.34/1.33  #Subsume      : 4
% 2.34/1.33  #Demod        : 63
% 2.34/1.33  #Tautology    : 86
% 2.34/1.33  #SimpNegUnit  : 0
% 2.34/1.33  #BackRed      : 1
% 2.34/1.33  
% 2.34/1.33  #Partial instantiations: 0
% 2.34/1.33  #Strategies tried      : 1
% 2.34/1.33  
% 2.34/1.33  Timing (in seconds)
% 2.34/1.33  ----------------------
% 2.34/1.34  Preprocessing        : 0.33
% 2.34/1.34  Parsing              : 0.17
% 2.34/1.34  CNF conversion       : 0.02
% 2.34/1.34  Main loop            : 0.24
% 2.34/1.34  Inferencing          : 0.09
% 2.34/1.34  Reduction            : 0.10
% 2.34/1.34  Demodulation         : 0.08
% 2.34/1.34  BG Simplification    : 0.02
% 2.34/1.34  Subsumption          : 0.03
% 2.34/1.34  Abstraction          : 0.02
% 2.34/1.34  MUC search           : 0.00
% 2.34/1.34  Cooper               : 0.00
% 2.34/1.34  Total                : 0.59
% 2.34/1.34  Index Insertion      : 0.00
% 2.34/1.34  Index Deletion       : 0.00
% 2.34/1.34  Index Matching       : 0.00
% 2.34/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
