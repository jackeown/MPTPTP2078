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
% DateTime   : Thu Dec  3 09:46:23 EST 2020

% Result     : Theorem 2.91s
% Output     : CNFRefutation 2.91s
% Verified   : 
% Statistics : Number of formulae       :   28 (  28 expanded)
%              Number of leaves         :   21 (  21 expanded)
%              Depth                    :    4
%              Number of atoms          :   11 (  11 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(f_27,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k2_tarski(F,G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k4_enumset1(A,B,C,D,E,F),k2_tarski(G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_enumset1)).

tff(f_40,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

tff(c_2,plain,(
    ! [B_2,C_3,A_1,E_5,D_4,G_7,F_6] : k2_xboole_0(k3_enumset1(A_1,B_2,C_3,D_4,E_5),k2_tarski(F_6,G_7)) = k5_enumset1(A_1,B_2,C_3,D_4,E_5,F_6,G_7) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [B_33,C_34,E_36,A_32,D_35] : k4_enumset1(A_32,A_32,B_33,C_34,D_35,E_36) = k3_enumset1(A_32,B_33,C_34,D_35,E_36) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_166,plain,(
    ! [A_82,D_77,F_80,G_78,C_75,B_79,E_81,H_76] : k2_xboole_0(k4_enumset1(A_82,B_79,C_75,D_77,E_81,F_80),k2_tarski(G_78,H_76)) = k6_enumset1(A_82,B_79,C_75,D_77,E_81,F_80,G_78,H_76) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_175,plain,(
    ! [B_33,C_34,G_78,E_36,H_76,A_32,D_35] : k6_enumset1(A_32,A_32,B_33,C_34,D_35,E_36,G_78,H_76) = k2_xboole_0(k3_enumset1(A_32,B_33,C_34,D_35,E_36),k2_tarski(G_78,H_76)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_166])).

tff(c_181,plain,(
    ! [B_33,C_34,G_78,E_36,H_76,A_32,D_35] : k6_enumset1(A_32,A_32,B_33,C_34,D_35,E_36,G_78,H_76) = k5_enumset1(A_32,B_33,C_34,D_35,E_36,G_78,H_76) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_175])).

tff(c_14,plain,(
    k6_enumset1('#skF_1','#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7') != k5_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_590,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.08  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.07/0.26  % Computer   : n002.cluster.edu
% 0.07/0.26  % Model      : x86_64 x86_64
% 0.07/0.26  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.07/0.26  % Memory     : 8042.1875MB
% 0.07/0.26  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.07/0.26  % CPULimit   : 60
% 0.07/0.26  % DateTime   : Tue Dec  1 14:14:06 EST 2020
% 0.07/0.26  % CPUTime    : 
% 0.07/0.27  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.91/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.91/1.44  
% 2.91/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.91/1.44  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.91/1.44  
% 2.91/1.44  %Foreground sorts:
% 2.91/1.44  
% 2.91/1.44  
% 2.91/1.44  %Background operators:
% 2.91/1.44  
% 2.91/1.44  
% 2.91/1.44  %Foreground operators:
% 2.91/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.91/1.44  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.91/1.44  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.91/1.44  tff('#skF_7', type, '#skF_7': $i).
% 2.91/1.44  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.91/1.44  tff('#skF_5', type, '#skF_5': $i).
% 2.91/1.44  tff('#skF_6', type, '#skF_6': $i).
% 2.91/1.44  tff('#skF_2', type, '#skF_2': $i).
% 2.91/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.91/1.44  tff('#skF_1', type, '#skF_1': $i).
% 2.91/1.44  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.91/1.44  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.91/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.91/1.44  tff('#skF_4', type, '#skF_4': $i).
% 2.91/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.91/1.44  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.91/1.44  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.91/1.44  
% 2.91/1.45  tff(f_27, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k2_tarski(F, G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_enumset1)).
% 2.91/1.45  tff(f_37, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 2.91/1.45  tff(f_31, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k4_enumset1(A, B, C, D, E, F), k2_tarski(G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_enumset1)).
% 2.91/1.45  tff(f_40, negated_conjecture, ~(![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 2.91/1.45  tff(c_2, plain, (![B_2, C_3, A_1, E_5, D_4, G_7, F_6]: (k2_xboole_0(k3_enumset1(A_1, B_2, C_3, D_4, E_5), k2_tarski(F_6, G_7))=k5_enumset1(A_1, B_2, C_3, D_4, E_5, F_6, G_7))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.91/1.45  tff(c_12, plain, (![B_33, C_34, E_36, A_32, D_35]: (k4_enumset1(A_32, A_32, B_33, C_34, D_35, E_36)=k3_enumset1(A_32, B_33, C_34, D_35, E_36))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.91/1.45  tff(c_166, plain, (![A_82, D_77, F_80, G_78, C_75, B_79, E_81, H_76]: (k2_xboole_0(k4_enumset1(A_82, B_79, C_75, D_77, E_81, F_80), k2_tarski(G_78, H_76))=k6_enumset1(A_82, B_79, C_75, D_77, E_81, F_80, G_78, H_76))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.91/1.45  tff(c_175, plain, (![B_33, C_34, G_78, E_36, H_76, A_32, D_35]: (k6_enumset1(A_32, A_32, B_33, C_34, D_35, E_36, G_78, H_76)=k2_xboole_0(k3_enumset1(A_32, B_33, C_34, D_35, E_36), k2_tarski(G_78, H_76)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_166])).
% 2.91/1.45  tff(c_181, plain, (![B_33, C_34, G_78, E_36, H_76, A_32, D_35]: (k6_enumset1(A_32, A_32, B_33, C_34, D_35, E_36, G_78, H_76)=k5_enumset1(A_32, B_33, C_34, D_35, E_36, G_78, H_76))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_175])).
% 2.91/1.45  tff(c_14, plain, (k6_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')!=k5_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.91/1.45  tff(c_590, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_181, c_14])).
% 2.91/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.91/1.45  
% 2.91/1.46  Inference rules
% 2.91/1.46  ----------------------
% 2.91/1.46  #Ref     : 0
% 2.91/1.46  #Sup     : 150
% 2.91/1.46  #Fact    : 0
% 2.91/1.46  #Define  : 0
% 2.91/1.46  #Split   : 0
% 2.91/1.46  #Chain   : 0
% 2.91/1.46  #Close   : 0
% 2.91/1.46  
% 2.91/1.46  Ordering : KBO
% 2.91/1.46  
% 2.91/1.46  Simplification rules
% 2.91/1.46  ----------------------
% 2.91/1.46  #Subsume      : 39
% 2.91/1.46  #Demod        : 9
% 2.91/1.46  #Tautology    : 41
% 2.91/1.46  #SimpNegUnit  : 0
% 2.91/1.46  #BackRed      : 2
% 2.91/1.46  
% 2.91/1.46  #Partial instantiations: 0
% 2.91/1.46  #Strategies tried      : 1
% 2.91/1.46  
% 2.91/1.46  Timing (in seconds)
% 2.91/1.46  ----------------------
% 2.91/1.46  Preprocessing        : 0.38
% 2.91/1.46  Parsing              : 0.19
% 2.91/1.46  CNF conversion       : 0.02
% 2.91/1.46  Main loop            : 0.43
% 2.91/1.46  Inferencing          : 0.18
% 2.91/1.46  Reduction            : 0.16
% 2.91/1.46  Demodulation         : 0.14
% 2.91/1.46  BG Simplification    : 0.03
% 2.91/1.46  Subsumption          : 0.05
% 2.91/1.46  Abstraction          : 0.03
% 2.91/1.46  MUC search           : 0.00
% 2.91/1.46  Cooper               : 0.00
% 2.91/1.46  Total                : 0.85
% 2.91/1.46  Index Insertion      : 0.00
% 2.91/1.46  Index Deletion       : 0.00
% 2.91/1.46  Index Matching       : 0.00
% 2.91/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
