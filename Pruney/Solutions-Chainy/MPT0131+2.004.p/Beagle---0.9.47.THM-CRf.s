%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:40 EST 2020

% Result     : Theorem 5.91s
% Output     : CNFRefutation 5.91s
% Verified   : 
% Statistics : Number of formulae       :   43 (  51 expanded)
%              Number of leaves         :   25 (  30 expanded)
%              Depth                    :    8
%              Number of atoms          :   24 (  32 expanded)
%              Number of equality atoms :   23 (  31 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_2 > #skF_1

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_49,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_enumset1(A,B,C),k2_tarski(D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l57_enumset1)).

tff(f_55,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_51,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_53,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k2_tarski(A,B),k1_tarski(C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_tarski(A),k2_enumset1(B,C,D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).

tff(c_38,plain,(
    ! [A_21,B_22,D_24,C_23,E_25] : k2_xboole_0(k1_enumset1(A_21,B_22,C_23),k2_tarski(D_24,E_25)) = k3_enumset1(A_21,B_22,C_23,D_24,E_25) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_44,plain,(
    ! [A_31,B_32,C_33,D_34] : k2_xboole_0(k1_enumset1(A_31,B_32,C_33),k1_tarski(D_34)) = k2_enumset1(A_31,B_32,C_33,D_34) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_40,plain,(
    ! [A_26,B_27] : k2_xboole_0(k1_tarski(A_26),k1_tarski(B_27)) = k2_tarski(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_209,plain,(
    ! [A_56,B_57,C_58] : k2_xboole_0(k2_tarski(A_56,B_57),k1_tarski(C_58)) = k1_enumset1(A_56,B_57,C_58) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_6,plain,(
    ! [A_7,B_8,C_9] : k2_xboole_0(k2_xboole_0(A_7,B_8),C_9) = k2_xboole_0(A_7,k2_xboole_0(B_8,C_9)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1813,plain,(
    ! [A_173,B_174,C_175,C_176] : k2_xboole_0(k2_tarski(A_173,B_174),k2_xboole_0(k1_tarski(C_175),C_176)) = k2_xboole_0(k1_enumset1(A_173,B_174,C_175),C_176) ),
    inference(superposition,[status(thm),theory(equality)],[c_209,c_6])).

tff(c_1885,plain,(
    ! [A_173,B_174,A_26,B_27] : k2_xboole_0(k1_enumset1(A_173,B_174,A_26),k1_tarski(B_27)) = k2_xboole_0(k2_tarski(A_173,B_174),k2_tarski(A_26,B_27)) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_1813])).

tff(c_1905,plain,(
    ! [A_173,B_174,A_26,B_27] : k2_xboole_0(k2_tarski(A_173,B_174),k2_tarski(A_26,B_27)) = k2_enumset1(A_173,B_174,A_26,B_27) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1885])).

tff(c_42,plain,(
    ! [A_28,B_29,C_30] : k2_xboole_0(k2_tarski(A_28,B_29),k1_tarski(C_30)) = k1_enumset1(A_28,B_29,C_30) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_115,plain,(
    ! [A_49,B_50,C_51] : k2_xboole_0(k2_xboole_0(A_49,B_50),C_51) = k2_xboole_0(A_49,k2_xboole_0(B_50,C_51)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_363,plain,(
    ! [A_76,B_77,C_78] : k2_xboole_0(k1_tarski(A_76),k2_xboole_0(k1_tarski(B_77),C_78)) = k2_xboole_0(k2_tarski(A_76,B_77),C_78) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_115])).

tff(c_418,plain,(
    ! [A_76,A_26,B_27] : k2_xboole_0(k2_tarski(A_76,A_26),k1_tarski(B_27)) = k2_xboole_0(k1_tarski(A_76),k2_tarski(A_26,B_27)) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_363])).

tff(c_553,plain,(
    ! [A_93,A_94,B_95] : k2_xboole_0(k1_tarski(A_93),k2_tarski(A_94,B_95)) = k1_enumset1(A_93,A_94,B_95) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_418])).

tff(c_2586,plain,(
    ! [A_212,A_213,B_214,C_215] : k2_xboole_0(k1_tarski(A_212),k2_xboole_0(k2_tarski(A_213,B_214),C_215)) = k2_xboole_0(k1_enumset1(A_212,A_213,B_214),C_215) ),
    inference(superposition,[status(thm),theory(equality)],[c_553,c_6])).

tff(c_2628,plain,(
    ! [B_27,B_174,A_26,A_173,A_212] : k2_xboole_0(k1_enumset1(A_212,A_173,B_174),k2_tarski(A_26,B_27)) = k2_xboole_0(k1_tarski(A_212),k2_enumset1(A_173,B_174,A_26,B_27)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1905,c_2586])).

tff(c_2680,plain,(
    ! [B_27,B_174,A_26,A_173,A_212] : k2_xboole_0(k1_tarski(A_212),k2_enumset1(A_173,B_174,A_26,B_27)) = k3_enumset1(A_212,A_173,B_174,A_26,B_27) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_2628])).

tff(c_46,plain,(
    k2_xboole_0(k1_tarski('#skF_5'),k2_enumset1('#skF_6','#skF_7','#skF_8','#skF_9')) != k3_enumset1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_6324,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2680,c_46])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:00:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.91/2.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.91/2.18  
% 5.91/2.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.91/2.18  %$ r2_hidden > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_2 > #skF_1
% 5.91/2.18  
% 5.91/2.18  %Foreground sorts:
% 5.91/2.18  
% 5.91/2.18  
% 5.91/2.18  %Background operators:
% 5.91/2.18  
% 5.91/2.18  
% 5.91/2.18  %Foreground operators:
% 5.91/2.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.91/2.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.91/2.18  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.91/2.18  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.91/2.18  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 5.91/2.18  tff('#skF_7', type, '#skF_7': $i).
% 5.91/2.18  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.91/2.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.91/2.18  tff('#skF_5', type, '#skF_5': $i).
% 5.91/2.18  tff('#skF_6', type, '#skF_6': $i).
% 5.91/2.18  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.91/2.18  tff('#skF_9', type, '#skF_9': $i).
% 5.91/2.18  tff('#skF_8', type, '#skF_8': $i).
% 5.91/2.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.91/2.18  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 5.91/2.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.91/2.18  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.91/2.18  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.91/2.18  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.91/2.18  
% 5.91/2.19  tff(f_49, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_enumset1(A, B, C), k2_tarski(D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l57_enumset1)).
% 5.91/2.19  tff(f_55, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 5.91/2.19  tff(f_51, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 5.91/2.19  tff(f_53, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k2_tarski(A, B), k1_tarski(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_enumset1)).
% 5.91/2.19  tff(f_31, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 5.91/2.19  tff(f_58, negated_conjecture, ~(![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_tarski(A), k2_enumset1(B, C, D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_enumset1)).
% 5.91/2.19  tff(c_38, plain, (![A_21, B_22, D_24, C_23, E_25]: (k2_xboole_0(k1_enumset1(A_21, B_22, C_23), k2_tarski(D_24, E_25))=k3_enumset1(A_21, B_22, C_23, D_24, E_25))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.91/2.19  tff(c_44, plain, (![A_31, B_32, C_33, D_34]: (k2_xboole_0(k1_enumset1(A_31, B_32, C_33), k1_tarski(D_34))=k2_enumset1(A_31, B_32, C_33, D_34))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.91/2.19  tff(c_40, plain, (![A_26, B_27]: (k2_xboole_0(k1_tarski(A_26), k1_tarski(B_27))=k2_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.91/2.19  tff(c_209, plain, (![A_56, B_57, C_58]: (k2_xboole_0(k2_tarski(A_56, B_57), k1_tarski(C_58))=k1_enumset1(A_56, B_57, C_58))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.91/2.19  tff(c_6, plain, (![A_7, B_8, C_9]: (k2_xboole_0(k2_xboole_0(A_7, B_8), C_9)=k2_xboole_0(A_7, k2_xboole_0(B_8, C_9)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.91/2.19  tff(c_1813, plain, (![A_173, B_174, C_175, C_176]: (k2_xboole_0(k2_tarski(A_173, B_174), k2_xboole_0(k1_tarski(C_175), C_176))=k2_xboole_0(k1_enumset1(A_173, B_174, C_175), C_176))), inference(superposition, [status(thm), theory('equality')], [c_209, c_6])).
% 5.91/2.19  tff(c_1885, plain, (![A_173, B_174, A_26, B_27]: (k2_xboole_0(k1_enumset1(A_173, B_174, A_26), k1_tarski(B_27))=k2_xboole_0(k2_tarski(A_173, B_174), k2_tarski(A_26, B_27)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_1813])).
% 5.91/2.19  tff(c_1905, plain, (![A_173, B_174, A_26, B_27]: (k2_xboole_0(k2_tarski(A_173, B_174), k2_tarski(A_26, B_27))=k2_enumset1(A_173, B_174, A_26, B_27))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_1885])).
% 5.91/2.19  tff(c_42, plain, (![A_28, B_29, C_30]: (k2_xboole_0(k2_tarski(A_28, B_29), k1_tarski(C_30))=k1_enumset1(A_28, B_29, C_30))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.91/2.19  tff(c_115, plain, (![A_49, B_50, C_51]: (k2_xboole_0(k2_xboole_0(A_49, B_50), C_51)=k2_xboole_0(A_49, k2_xboole_0(B_50, C_51)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.91/2.19  tff(c_363, plain, (![A_76, B_77, C_78]: (k2_xboole_0(k1_tarski(A_76), k2_xboole_0(k1_tarski(B_77), C_78))=k2_xboole_0(k2_tarski(A_76, B_77), C_78))), inference(superposition, [status(thm), theory('equality')], [c_40, c_115])).
% 5.91/2.19  tff(c_418, plain, (![A_76, A_26, B_27]: (k2_xboole_0(k2_tarski(A_76, A_26), k1_tarski(B_27))=k2_xboole_0(k1_tarski(A_76), k2_tarski(A_26, B_27)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_363])).
% 5.91/2.19  tff(c_553, plain, (![A_93, A_94, B_95]: (k2_xboole_0(k1_tarski(A_93), k2_tarski(A_94, B_95))=k1_enumset1(A_93, A_94, B_95))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_418])).
% 5.91/2.19  tff(c_2586, plain, (![A_212, A_213, B_214, C_215]: (k2_xboole_0(k1_tarski(A_212), k2_xboole_0(k2_tarski(A_213, B_214), C_215))=k2_xboole_0(k1_enumset1(A_212, A_213, B_214), C_215))), inference(superposition, [status(thm), theory('equality')], [c_553, c_6])).
% 5.91/2.19  tff(c_2628, plain, (![B_27, B_174, A_26, A_173, A_212]: (k2_xboole_0(k1_enumset1(A_212, A_173, B_174), k2_tarski(A_26, B_27))=k2_xboole_0(k1_tarski(A_212), k2_enumset1(A_173, B_174, A_26, B_27)))), inference(superposition, [status(thm), theory('equality')], [c_1905, c_2586])).
% 5.91/2.19  tff(c_2680, plain, (![B_27, B_174, A_26, A_173, A_212]: (k2_xboole_0(k1_tarski(A_212), k2_enumset1(A_173, B_174, A_26, B_27))=k3_enumset1(A_212, A_173, B_174, A_26, B_27))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_2628])).
% 5.91/2.19  tff(c_46, plain, (k2_xboole_0(k1_tarski('#skF_5'), k2_enumset1('#skF_6', '#skF_7', '#skF_8', '#skF_9'))!=k3_enumset1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.91/2.19  tff(c_6324, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2680, c_46])).
% 5.91/2.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.91/2.19  
% 5.91/2.19  Inference rules
% 5.91/2.19  ----------------------
% 5.91/2.19  #Ref     : 0
% 5.91/2.19  #Sup     : 1430
% 5.91/2.19  #Fact    : 2
% 5.91/2.19  #Define  : 0
% 5.91/2.19  #Split   : 0
% 5.91/2.19  #Chain   : 0
% 5.91/2.19  #Close   : 0
% 5.91/2.19  
% 5.91/2.19  Ordering : KBO
% 5.91/2.19  
% 5.91/2.19  Simplification rules
% 5.91/2.19  ----------------------
% 5.91/2.19  #Subsume      : 9
% 5.91/2.19  #Demod        : 2216
% 5.91/2.19  #Tautology    : 1038
% 5.91/2.19  #SimpNegUnit  : 0
% 5.91/2.19  #BackRed      : 4
% 5.91/2.19  
% 5.91/2.19  #Partial instantiations: 0
% 5.91/2.19  #Strategies tried      : 1
% 5.91/2.19  
% 5.91/2.19  Timing (in seconds)
% 5.91/2.19  ----------------------
% 5.91/2.20  Preprocessing        : 0.29
% 5.91/2.20  Parsing              : 0.15
% 5.91/2.20  CNF conversion       : 0.02
% 5.91/2.20  Main loop            : 1.14
% 5.91/2.20  Inferencing          : 0.40
% 5.91/2.20  Reduction            : 0.53
% 5.91/2.20  Demodulation         : 0.46
% 5.91/2.20  BG Simplification    : 0.04
% 5.91/2.20  Subsumption          : 0.12
% 5.91/2.20  Abstraction          : 0.08
% 5.91/2.20  MUC search           : 0.00
% 5.91/2.20  Cooper               : 0.00
% 5.91/2.20  Total                : 1.45
% 5.91/2.20  Index Insertion      : 0.00
% 5.91/2.20  Index Deletion       : 0.00
% 5.91/2.20  Index Matching       : 0.00
% 5.91/2.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
