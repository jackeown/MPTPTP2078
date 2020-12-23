%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:17 EST 2020

% Result     : Theorem 4.48s
% Output     : CNFRefutation 4.66s
% Verified   : 
% Statistics : Number of formulae       :   35 (  36 expanded)
%              Number of leaves         :   22 (  23 expanded)
%              Depth                    :    7
%              Number of atoms          :   23 (  24 expanded)
%              Number of equality atoms :   17 (  18 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_39,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_tarski(A),k2_enumset1(B,C,D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_tarski(A),k3_enumset1(B,C,D,E,F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_enumset1)).

tff(f_52,negated_conjecture,(
    ~ ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(c_12,plain,(
    ! [E_12,D_11,A_8,C_10,B_9] : k2_xboole_0(k1_tarski(A_8),k2_enumset1(B_9,C_10,D_11,E_12)) = k3_enumset1(A_8,B_9,C_10,D_11,E_12) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_218,plain,(
    ! [D_56,A_52,C_55,B_54,E_53] : k2_xboole_0(k1_tarski(A_52),k2_enumset1(B_54,C_55,D_56,E_53)) = k3_enumset1(A_52,B_54,C_55,D_56,E_53) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_36,plain,(
    ! [A_31,B_32] :
      ( k2_xboole_0(A_31,B_32) = B_32
      | ~ r1_tarski(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_40,plain,(
    ! [B_2] : k2_xboole_0(B_2,B_2) = B_2 ),
    inference(resolution,[status(thm)],[c_6,c_36])).

tff(c_75,plain,(
    ! [A_41,B_42,C_43] : k2_xboole_0(k2_xboole_0(A_41,B_42),C_43) = k2_xboole_0(A_41,k2_xboole_0(B_42,C_43)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_94,plain,(
    ! [B_2,C_43] : k2_xboole_0(B_2,k2_xboole_0(B_2,C_43)) = k2_xboole_0(B_2,C_43) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_75])).

tff(c_227,plain,(
    ! [D_56,A_52,C_55,B_54,E_53] : k2_xboole_0(k1_tarski(A_52),k3_enumset1(A_52,B_54,C_55,D_56,E_53)) = k2_xboole_0(k1_tarski(A_52),k2_enumset1(B_54,C_55,D_56,E_53)) ),
    inference(superposition,[status(thm),theory(equality)],[c_218,c_94])).

tff(c_3041,plain,(
    ! [C_163,D_166,A_165,B_167,E_164] : k2_xboole_0(k1_tarski(A_165),k3_enumset1(A_165,B_167,C_163,D_166,E_164)) = k3_enumset1(A_165,B_167,C_163,D_166,E_164) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_227])).

tff(c_14,plain,(
    ! [E_17,F_18,A_13,B_14,C_15,D_16] : k2_xboole_0(k1_tarski(A_13),k3_enumset1(B_14,C_15,D_16,E_17,F_18)) = k4_enumset1(A_13,B_14,C_15,D_16,E_17,F_18) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_3060,plain,(
    ! [C_163,D_166,A_165,B_167,E_164] : k4_enumset1(A_165,A_165,B_167,C_163,D_166,E_164) = k3_enumset1(A_165,B_167,C_163,D_166,E_164) ),
    inference(superposition,[status(thm),theory(equality)],[c_3041,c_14])).

tff(c_24,plain,(
    k4_enumset1('#skF_1','#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != k3_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_3115,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3060,c_24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:42:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.48/1.81  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.48/1.81  
% 4.48/1.81  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.48/1.82  %$ r1_tarski > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.48/1.82  
% 4.48/1.82  %Foreground sorts:
% 4.48/1.82  
% 4.48/1.82  
% 4.48/1.82  %Background operators:
% 4.48/1.82  
% 4.48/1.82  
% 4.48/1.82  %Foreground operators:
% 4.48/1.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.48/1.82  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.48/1.82  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.48/1.82  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.48/1.82  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.48/1.82  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.48/1.82  tff('#skF_5', type, '#skF_5': $i).
% 4.48/1.82  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.48/1.82  tff('#skF_2', type, '#skF_2': $i).
% 4.48/1.82  tff('#skF_3', type, '#skF_3': $i).
% 4.48/1.82  tff('#skF_1', type, '#skF_1': $i).
% 4.48/1.82  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.48/1.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.48/1.82  tff('#skF_4', type, '#skF_4': $i).
% 4.48/1.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.48/1.82  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.48/1.82  
% 4.66/1.83  tff(f_39, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_tarski(A), k2_enumset1(B, C, D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_enumset1)).
% 4.66/1.83  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.66/1.83  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 4.66/1.83  tff(f_37, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 4.66/1.83  tff(f_41, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_tarski(A), k3_enumset1(B, C, D, E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_enumset1)).
% 4.66/1.83  tff(f_52, negated_conjecture, ~(![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 4.66/1.83  tff(c_12, plain, (![E_12, D_11, A_8, C_10, B_9]: (k2_xboole_0(k1_tarski(A_8), k2_enumset1(B_9, C_10, D_11, E_12))=k3_enumset1(A_8, B_9, C_10, D_11, E_12))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.66/1.83  tff(c_218, plain, (![D_56, A_52, C_55, B_54, E_53]: (k2_xboole_0(k1_tarski(A_52), k2_enumset1(B_54, C_55, D_56, E_53))=k3_enumset1(A_52, B_54, C_55, D_56, E_53))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.66/1.83  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.66/1.83  tff(c_36, plain, (![A_31, B_32]: (k2_xboole_0(A_31, B_32)=B_32 | ~r1_tarski(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.66/1.83  tff(c_40, plain, (![B_2]: (k2_xboole_0(B_2, B_2)=B_2)), inference(resolution, [status(thm)], [c_6, c_36])).
% 4.66/1.83  tff(c_75, plain, (![A_41, B_42, C_43]: (k2_xboole_0(k2_xboole_0(A_41, B_42), C_43)=k2_xboole_0(A_41, k2_xboole_0(B_42, C_43)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.66/1.83  tff(c_94, plain, (![B_2, C_43]: (k2_xboole_0(B_2, k2_xboole_0(B_2, C_43))=k2_xboole_0(B_2, C_43))), inference(superposition, [status(thm), theory('equality')], [c_40, c_75])).
% 4.66/1.83  tff(c_227, plain, (![D_56, A_52, C_55, B_54, E_53]: (k2_xboole_0(k1_tarski(A_52), k3_enumset1(A_52, B_54, C_55, D_56, E_53))=k2_xboole_0(k1_tarski(A_52), k2_enumset1(B_54, C_55, D_56, E_53)))), inference(superposition, [status(thm), theory('equality')], [c_218, c_94])).
% 4.66/1.83  tff(c_3041, plain, (![C_163, D_166, A_165, B_167, E_164]: (k2_xboole_0(k1_tarski(A_165), k3_enumset1(A_165, B_167, C_163, D_166, E_164))=k3_enumset1(A_165, B_167, C_163, D_166, E_164))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_227])).
% 4.66/1.83  tff(c_14, plain, (![E_17, F_18, A_13, B_14, C_15, D_16]: (k2_xboole_0(k1_tarski(A_13), k3_enumset1(B_14, C_15, D_16, E_17, F_18))=k4_enumset1(A_13, B_14, C_15, D_16, E_17, F_18))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.66/1.83  tff(c_3060, plain, (![C_163, D_166, A_165, B_167, E_164]: (k4_enumset1(A_165, A_165, B_167, C_163, D_166, E_164)=k3_enumset1(A_165, B_167, C_163, D_166, E_164))), inference(superposition, [status(thm), theory('equality')], [c_3041, c_14])).
% 4.66/1.83  tff(c_24, plain, (k4_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!=k3_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.66/1.83  tff(c_3115, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3060, c_24])).
% 4.66/1.83  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.66/1.83  
% 4.66/1.83  Inference rules
% 4.66/1.83  ----------------------
% 4.66/1.83  #Ref     : 0
% 4.66/1.83  #Sup     : 729
% 4.66/1.83  #Fact    : 0
% 4.66/1.83  #Define  : 0
% 4.66/1.83  #Split   : 0
% 4.66/1.83  #Chain   : 0
% 4.66/1.83  #Close   : 0
% 4.66/1.83  
% 4.66/1.83  Ordering : KBO
% 4.66/1.83  
% 4.66/1.83  Simplification rules
% 4.66/1.83  ----------------------
% 4.66/1.83  #Subsume      : 43
% 4.66/1.83  #Demod        : 959
% 4.66/1.83  #Tautology    : 468
% 4.66/1.83  #SimpNegUnit  : 0
% 4.66/1.83  #BackRed      : 1
% 4.66/1.83  
% 4.66/1.83  #Partial instantiations: 0
% 4.66/1.83  #Strategies tried      : 1
% 4.66/1.83  
% 4.66/1.83  Timing (in seconds)
% 4.66/1.83  ----------------------
% 4.66/1.83  Preprocessing        : 0.29
% 4.66/1.83  Parsing              : 0.15
% 4.66/1.83  CNF conversion       : 0.02
% 4.66/1.83  Main loop            : 0.79
% 4.66/1.83  Inferencing          : 0.29
% 4.66/1.83  Reduction            : 0.34
% 4.66/1.83  Demodulation         : 0.29
% 4.66/1.83  BG Simplification    : 0.05
% 4.66/1.83  Subsumption          : 0.07
% 4.66/1.83  Abstraction          : 0.06
% 4.66/1.83  MUC search           : 0.00
% 4.66/1.83  Cooper               : 0.00
% 4.66/1.83  Total                : 1.10
% 4.66/1.83  Index Insertion      : 0.00
% 4.66/1.83  Index Deletion       : 0.00
% 4.66/1.83  Index Matching       : 0.00
% 4.66/1.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------
