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
% DateTime   : Thu Dec  3 09:46:00 EST 2020

% Result     : Theorem 2.76s
% Output     : CNFRefutation 2.76s
% Verified   : 
% Statistics : Number of formulae       :   42 (  45 expanded)
%              Number of leaves         :   28 (  30 expanded)
%              Depth                    :    7
%              Number of atoms          :   20 (  23 expanded)
%              Number of equality atoms :   19 (  22 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k6_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_48,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k1_enumset1(F,G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_enumset1)).

tff(f_40,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k2_tarski(A,B),k1_tarski(C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).

tff(f_38,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_46,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k1_tarski(F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_enumset1)).

tff(f_51,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k4_enumset1(A,B,C,D,E,F),k2_tarski(G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_enumset1)).

tff(c_28,plain,(
    ! [D_36,G_39,F_38,E_37,A_33,B_34,H_40,C_35] : k2_xboole_0(k3_enumset1(A_33,B_34,C_35,D_36,E_37),k1_enumset1(F_38,G_39,H_40)) = k6_enumset1(A_33,B_34,C_35,D_36,E_37,F_38,G_39,H_40) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_20,plain,(
    ! [A_15,B_16,C_17] : k2_xboole_0(k2_tarski(A_15,B_16),k1_tarski(C_17)) = k1_enumset1(A_15,B_16,C_17) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_18,plain,(
    ! [A_13,B_14] : k2_xboole_0(k1_tarski(A_13),k1_tarski(B_14)) = k2_tarski(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_57,plain,(
    ! [A_49,B_50,C_51] : k2_xboole_0(k2_xboole_0(A_49,B_50),C_51) = k2_xboole_0(A_49,k2_xboole_0(B_50,C_51)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_100,plain,(
    ! [A_62,B_63,C_64] : k2_xboole_0(k1_tarski(A_62),k2_xboole_0(k1_tarski(B_63),C_64)) = k2_xboole_0(k2_tarski(A_62,B_63),C_64) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_57])).

tff(c_118,plain,(
    ! [A_62,A_13,B_14] : k2_xboole_0(k2_tarski(A_62,A_13),k1_tarski(B_14)) = k2_xboole_0(k1_tarski(A_62),k2_tarski(A_13,B_14)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_100])).

tff(c_122,plain,(
    ! [A_62,A_13,B_14] : k2_xboole_0(k1_tarski(A_62),k2_tarski(A_13,B_14)) = k1_enumset1(A_62,A_13,B_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_118])).

tff(c_179,plain,(
    ! [C_78,A_82,E_80,B_81,D_79,F_77] : k2_xboole_0(k3_enumset1(A_82,B_81,C_78,D_79,E_80),k1_tarski(F_77)) = k4_enumset1(A_82,B_81,C_78,D_79,E_80,F_77) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_4,plain,(
    ! [A_5,B_6,C_7] : k2_xboole_0(k2_xboole_0(A_5,B_6),C_7) = k2_xboole_0(A_5,k2_xboole_0(B_6,C_7)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_506,plain,(
    ! [C_160,C_161,F_159,B_157,E_158,A_162,D_163] : k2_xboole_0(k3_enumset1(A_162,B_157,C_161,D_163,E_158),k2_xboole_0(k1_tarski(F_159),C_160)) = k2_xboole_0(k4_enumset1(A_162,B_157,C_161,D_163,E_158,F_159),C_160) ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_4])).

tff(c_530,plain,(
    ! [C_161,A_13,B_14,B_157,E_158,A_62,A_162,D_163] : k2_xboole_0(k4_enumset1(A_162,B_157,C_161,D_163,E_158,A_62),k2_tarski(A_13,B_14)) = k2_xboole_0(k3_enumset1(A_162,B_157,C_161,D_163,E_158),k1_enumset1(A_62,A_13,B_14)) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_506])).

tff(c_540,plain,(
    ! [C_161,A_13,B_14,B_157,E_158,A_62,A_162,D_163] : k2_xboole_0(k4_enumset1(A_162,B_157,C_161,D_163,E_158,A_62),k2_tarski(A_13,B_14)) = k6_enumset1(A_162,B_157,C_161,D_163,E_158,A_62,A_13,B_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_530])).

tff(c_30,plain,(
    k2_xboole_0(k4_enumset1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),k2_tarski('#skF_9','#skF_10')) != k6_enumset1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8','#skF_9','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_803,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_540,c_30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:21:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.76/1.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.76/1.44  
% 2.76/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.76/1.45  %$ r2_hidden > k6_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_2 > #skF_1
% 2.76/1.45  
% 2.76/1.45  %Foreground sorts:
% 2.76/1.45  
% 2.76/1.45  
% 2.76/1.45  %Background operators:
% 2.76/1.45  
% 2.76/1.45  
% 2.76/1.45  %Foreground operators:
% 2.76/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.76/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.76/1.45  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.76/1.45  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.76/1.45  tff('#skF_7', type, '#skF_7': $i).
% 2.76/1.45  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.76/1.45  tff('#skF_10', type, '#skF_10': $i).
% 2.76/1.45  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.76/1.45  tff('#skF_5', type, '#skF_5': $i).
% 2.76/1.45  tff('#skF_6', type, '#skF_6': $i).
% 2.76/1.45  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.76/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.76/1.45  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.76/1.45  tff('#skF_9', type, '#skF_9': $i).
% 2.76/1.45  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.76/1.45  tff('#skF_8', type, '#skF_8': $i).
% 2.76/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.76/1.45  tff('#skF_4', type, '#skF_4': $i).
% 2.76/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.76/1.45  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.76/1.45  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.76/1.45  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.76/1.45  
% 2.76/1.46  tff(f_48, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k1_enumset1(F, G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_enumset1)).
% 2.76/1.46  tff(f_40, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k2_tarski(A, B), k1_tarski(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_enumset1)).
% 2.76/1.46  tff(f_38, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 2.76/1.46  tff(f_29, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 2.76/1.46  tff(f_46, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k1_tarski(F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_enumset1)).
% 2.76/1.46  tff(f_51, negated_conjecture, ~(![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k4_enumset1(A, B, C, D, E, F), k2_tarski(G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_enumset1)).
% 2.76/1.46  tff(c_28, plain, (![D_36, G_39, F_38, E_37, A_33, B_34, H_40, C_35]: (k2_xboole_0(k3_enumset1(A_33, B_34, C_35, D_36, E_37), k1_enumset1(F_38, G_39, H_40))=k6_enumset1(A_33, B_34, C_35, D_36, E_37, F_38, G_39, H_40))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.76/1.46  tff(c_20, plain, (![A_15, B_16, C_17]: (k2_xboole_0(k2_tarski(A_15, B_16), k1_tarski(C_17))=k1_enumset1(A_15, B_16, C_17))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.76/1.46  tff(c_18, plain, (![A_13, B_14]: (k2_xboole_0(k1_tarski(A_13), k1_tarski(B_14))=k2_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.76/1.46  tff(c_57, plain, (![A_49, B_50, C_51]: (k2_xboole_0(k2_xboole_0(A_49, B_50), C_51)=k2_xboole_0(A_49, k2_xboole_0(B_50, C_51)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.76/1.46  tff(c_100, plain, (![A_62, B_63, C_64]: (k2_xboole_0(k1_tarski(A_62), k2_xboole_0(k1_tarski(B_63), C_64))=k2_xboole_0(k2_tarski(A_62, B_63), C_64))), inference(superposition, [status(thm), theory('equality')], [c_18, c_57])).
% 2.76/1.46  tff(c_118, plain, (![A_62, A_13, B_14]: (k2_xboole_0(k2_tarski(A_62, A_13), k1_tarski(B_14))=k2_xboole_0(k1_tarski(A_62), k2_tarski(A_13, B_14)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_100])).
% 2.76/1.46  tff(c_122, plain, (![A_62, A_13, B_14]: (k2_xboole_0(k1_tarski(A_62), k2_tarski(A_13, B_14))=k1_enumset1(A_62, A_13, B_14))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_118])).
% 2.76/1.46  tff(c_179, plain, (![C_78, A_82, E_80, B_81, D_79, F_77]: (k2_xboole_0(k3_enumset1(A_82, B_81, C_78, D_79, E_80), k1_tarski(F_77))=k4_enumset1(A_82, B_81, C_78, D_79, E_80, F_77))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.76/1.46  tff(c_4, plain, (![A_5, B_6, C_7]: (k2_xboole_0(k2_xboole_0(A_5, B_6), C_7)=k2_xboole_0(A_5, k2_xboole_0(B_6, C_7)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.76/1.46  tff(c_506, plain, (![C_160, C_161, F_159, B_157, E_158, A_162, D_163]: (k2_xboole_0(k3_enumset1(A_162, B_157, C_161, D_163, E_158), k2_xboole_0(k1_tarski(F_159), C_160))=k2_xboole_0(k4_enumset1(A_162, B_157, C_161, D_163, E_158, F_159), C_160))), inference(superposition, [status(thm), theory('equality')], [c_179, c_4])).
% 2.76/1.46  tff(c_530, plain, (![C_161, A_13, B_14, B_157, E_158, A_62, A_162, D_163]: (k2_xboole_0(k4_enumset1(A_162, B_157, C_161, D_163, E_158, A_62), k2_tarski(A_13, B_14))=k2_xboole_0(k3_enumset1(A_162, B_157, C_161, D_163, E_158), k1_enumset1(A_62, A_13, B_14)))), inference(superposition, [status(thm), theory('equality')], [c_122, c_506])).
% 2.76/1.46  tff(c_540, plain, (![C_161, A_13, B_14, B_157, E_158, A_62, A_162, D_163]: (k2_xboole_0(k4_enumset1(A_162, B_157, C_161, D_163, E_158, A_62), k2_tarski(A_13, B_14))=k6_enumset1(A_162, B_157, C_161, D_163, E_158, A_62, A_13, B_14))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_530])).
% 2.76/1.46  tff(c_30, plain, (k2_xboole_0(k4_enumset1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), k2_tarski('#skF_9', '#skF_10'))!=k6_enumset1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.76/1.46  tff(c_803, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_540, c_30])).
% 2.76/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.76/1.46  
% 2.76/1.46  Inference rules
% 2.76/1.46  ----------------------
% 2.76/1.46  #Ref     : 0
% 2.76/1.46  #Sup     : 199
% 2.76/1.46  #Fact    : 0
% 2.76/1.46  #Define  : 0
% 2.76/1.46  #Split   : 0
% 2.76/1.46  #Chain   : 0
% 2.76/1.46  #Close   : 0
% 2.76/1.46  
% 2.76/1.46  Ordering : KBO
% 2.76/1.46  
% 2.76/1.46  Simplification rules
% 2.76/1.46  ----------------------
% 2.76/1.46  #Subsume      : 0
% 2.76/1.46  #Demod        : 106
% 2.76/1.46  #Tautology    : 104
% 2.76/1.46  #SimpNegUnit  : 0
% 2.76/1.46  #BackRed      : 2
% 2.76/1.46  
% 2.76/1.46  #Partial instantiations: 0
% 2.76/1.46  #Strategies tried      : 1
% 2.76/1.46  
% 2.76/1.46  Timing (in seconds)
% 2.76/1.46  ----------------------
% 3.16/1.46  Preprocessing        : 0.29
% 3.16/1.46  Parsing              : 0.16
% 3.16/1.46  CNF conversion       : 0.02
% 3.16/1.46  Main loop            : 0.41
% 3.16/1.46  Inferencing          : 0.18
% 3.16/1.46  Reduction            : 0.13
% 3.16/1.46  Demodulation         : 0.11
% 3.16/1.46  BG Simplification    : 0.03
% 3.16/1.46  Subsumption          : 0.05
% 3.16/1.46  Abstraction          : 0.03
% 3.16/1.46  MUC search           : 0.00
% 3.16/1.46  Cooper               : 0.00
% 3.16/1.46  Total                : 0.73
% 3.16/1.46  Index Insertion      : 0.00
% 3.16/1.46  Index Deletion       : 0.00
% 3.16/1.46  Index Matching       : 0.00
% 3.16/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
