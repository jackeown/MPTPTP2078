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
% DateTime   : Thu Dec  3 09:45:58 EST 2020

% Result     : Theorem 2.91s
% Output     : CNFRefutation 2.91s
% Verified   : 
% Statistics : Number of formulae       :   42 (  53 expanded)
%              Number of leaves         :   26 (  31 expanded)
%              Depth                    :    8
%              Number of atoms          :   23 (  34 expanded)
%              Number of equality atoms :   22 (  33 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_39,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k1_tarski(A),k5_enumset1(B,C,D,E,F,G,H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k1_enumset1(A,B,C),k2_enumset1(D,E,F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_enumset1)).

tff(f_29,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_tarski(A),k2_enumset1(B,C,D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_42,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k1_enumset1(A,B,C),k3_enumset1(D,E,F,G,H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_enumset1)).

tff(c_14,plain,(
    ! [A_25,G_31,F_30,E_29,H_32,C_27,D_28,B_26] : k2_xboole_0(k1_tarski(A_25),k5_enumset1(B_26,C_27,D_28,E_29,F_30,G_31,H_32)) = k6_enumset1(A_25,B_26,C_27,D_28,E_29,F_30,G_31,H_32) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_12,plain,(
    ! [E_22,G_24,D_21,F_23,A_18,C_20,B_19] : k2_xboole_0(k1_enumset1(A_18,B_19,C_20),k2_enumset1(D_21,E_22,F_23,G_24)) = k5_enumset1(A_18,B_19,C_20,D_21,E_22,F_23,G_24) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4,plain,(
    ! [A_4,B_5] : k2_xboole_0(k1_tarski(A_4),k1_tarski(B_5)) = k2_tarski(A_4,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_26,plain,(
    ! [A_35,B_36,C_37] : k2_xboole_0(k2_xboole_0(A_35,B_36),C_37) = k2_xboole_0(A_35,k2_xboole_0(B_36,C_37)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_41,plain,(
    ! [A_4,B_5,C_37] : k2_xboole_0(k1_tarski(A_4),k2_xboole_0(k1_tarski(B_5),C_37)) = k2_xboole_0(k2_tarski(A_4,B_5),C_37) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_26])).

tff(c_100,plain,(
    ! [B_49,E_50,D_48,C_52,A_51] : k2_xboole_0(k1_tarski(A_51),k2_enumset1(B_49,C_52,D_48,E_50)) = k3_enumset1(A_51,B_49,C_52,D_48,E_50) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_414,plain,(
    ! [D_126,A_123,A_128,E_125,B_124,C_127] : k2_xboole_0(k2_tarski(A_128,A_123),k2_enumset1(B_124,C_127,D_126,E_125)) = k2_xboole_0(k1_tarski(A_128),k3_enumset1(A_123,B_124,C_127,D_126,E_125)) ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_41])).

tff(c_46,plain,(
    ! [A_38,B_39,C_40] : k2_xboole_0(k1_tarski(A_38),k2_tarski(B_39,C_40)) = k1_enumset1(A_38,B_39,C_40) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_xboole_0(k2_xboole_0(A_1,B_2),C_3) = k2_xboole_0(A_1,k2_xboole_0(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_52,plain,(
    ! [A_38,B_39,C_40,C_3] : k2_xboole_0(k1_tarski(A_38),k2_xboole_0(k2_tarski(B_39,C_40),C_3)) = k2_xboole_0(k1_enumset1(A_38,B_39,C_40),C_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_2])).

tff(c_423,plain,(
    ! [D_126,A_123,A_128,E_125,B_124,A_38,C_127] : k2_xboole_0(k1_tarski(A_38),k2_xboole_0(k1_tarski(A_128),k3_enumset1(A_123,B_124,C_127,D_126,E_125))) = k2_xboole_0(k1_enumset1(A_38,A_128,A_123),k2_enumset1(B_124,C_127,D_126,E_125)) ),
    inference(superposition,[status(thm),theory(equality)],[c_414,c_52])).

tff(c_555,plain,(
    ! [A_159,A_155,D_158,C_156,A_157,B_160,E_161] : k2_xboole_0(k2_tarski(A_155,A_157),k3_enumset1(A_159,B_160,C_156,D_158,E_161)) = k5_enumset1(A_155,A_157,A_159,B_160,C_156,D_158,E_161) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_41,c_423])).

tff(c_567,plain,(
    ! [A_159,A_155,D_158,A_38,C_156,A_157,B_160,E_161] : k2_xboole_0(k1_enumset1(A_38,A_155,A_157),k3_enumset1(A_159,B_160,C_156,D_158,E_161)) = k2_xboole_0(k1_tarski(A_38),k5_enumset1(A_155,A_157,A_159,B_160,C_156,D_158,E_161)) ),
    inference(superposition,[status(thm),theory(equality)],[c_555,c_52])).

tff(c_575,plain,(
    ! [A_159,A_155,D_158,A_38,C_156,A_157,B_160,E_161] : k2_xboole_0(k1_enumset1(A_38,A_155,A_157),k3_enumset1(A_159,B_160,C_156,D_158,E_161)) = k6_enumset1(A_38,A_155,A_157,A_159,B_160,C_156,D_158,E_161) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_567])).

tff(c_16,plain,(
    k2_xboole_0(k1_enumset1('#skF_1','#skF_2','#skF_3'),k3_enumset1('#skF_4','#skF_5','#skF_6','#skF_7','#skF_8')) != k6_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_732,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_575,c_16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:07:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.91/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.91/1.42  
% 2.91/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.91/1.42  %$ k6_enumset1 > k5_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 2.91/1.42  
% 2.91/1.42  %Foreground sorts:
% 2.91/1.42  
% 2.91/1.42  
% 2.91/1.42  %Background operators:
% 2.91/1.42  
% 2.91/1.42  
% 2.91/1.42  %Foreground operators:
% 2.91/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.91/1.42  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.91/1.42  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.91/1.42  tff('#skF_7', type, '#skF_7': $i).
% 2.91/1.42  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.91/1.42  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.91/1.42  tff('#skF_5', type, '#skF_5': $i).
% 2.91/1.42  tff('#skF_6', type, '#skF_6': $i).
% 2.91/1.42  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.91/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.91/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.91/1.42  tff('#skF_1', type, '#skF_1': $i).
% 2.91/1.42  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.91/1.42  tff('#skF_8', type, '#skF_8': $i).
% 2.91/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.91/1.42  tff('#skF_4', type, '#skF_4': $i).
% 2.91/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.91/1.42  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.91/1.42  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.91/1.42  
% 2.91/1.43  tff(f_39, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k1_tarski(A), k5_enumset1(B, C, D, E, F, G, H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_enumset1)).
% 2.91/1.43  tff(f_37, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k1_enumset1(A, B, C), k2_enumset1(D, E, F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_enumset1)).
% 2.91/1.43  tff(f_29, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 2.91/1.43  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 2.91/1.43  tff(f_35, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_tarski(A), k2_enumset1(B, C, D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_enumset1)).
% 2.91/1.43  tff(f_31, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_enumset1)).
% 2.91/1.43  tff(f_42, negated_conjecture, ~(![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k1_enumset1(A, B, C), k3_enumset1(D, E, F, G, H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_enumset1)).
% 2.91/1.43  tff(c_14, plain, (![A_25, G_31, F_30, E_29, H_32, C_27, D_28, B_26]: (k2_xboole_0(k1_tarski(A_25), k5_enumset1(B_26, C_27, D_28, E_29, F_30, G_31, H_32))=k6_enumset1(A_25, B_26, C_27, D_28, E_29, F_30, G_31, H_32))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.91/1.43  tff(c_12, plain, (![E_22, G_24, D_21, F_23, A_18, C_20, B_19]: (k2_xboole_0(k1_enumset1(A_18, B_19, C_20), k2_enumset1(D_21, E_22, F_23, G_24))=k5_enumset1(A_18, B_19, C_20, D_21, E_22, F_23, G_24))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.91/1.43  tff(c_4, plain, (![A_4, B_5]: (k2_xboole_0(k1_tarski(A_4), k1_tarski(B_5))=k2_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.91/1.43  tff(c_26, plain, (![A_35, B_36, C_37]: (k2_xboole_0(k2_xboole_0(A_35, B_36), C_37)=k2_xboole_0(A_35, k2_xboole_0(B_36, C_37)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.91/1.43  tff(c_41, plain, (![A_4, B_5, C_37]: (k2_xboole_0(k1_tarski(A_4), k2_xboole_0(k1_tarski(B_5), C_37))=k2_xboole_0(k2_tarski(A_4, B_5), C_37))), inference(superposition, [status(thm), theory('equality')], [c_4, c_26])).
% 2.91/1.43  tff(c_100, plain, (![B_49, E_50, D_48, C_52, A_51]: (k2_xboole_0(k1_tarski(A_51), k2_enumset1(B_49, C_52, D_48, E_50))=k3_enumset1(A_51, B_49, C_52, D_48, E_50))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.91/1.43  tff(c_414, plain, (![D_126, A_123, A_128, E_125, B_124, C_127]: (k2_xboole_0(k2_tarski(A_128, A_123), k2_enumset1(B_124, C_127, D_126, E_125))=k2_xboole_0(k1_tarski(A_128), k3_enumset1(A_123, B_124, C_127, D_126, E_125)))), inference(superposition, [status(thm), theory('equality')], [c_100, c_41])).
% 2.91/1.43  tff(c_46, plain, (![A_38, B_39, C_40]: (k2_xboole_0(k1_tarski(A_38), k2_tarski(B_39, C_40))=k1_enumset1(A_38, B_39, C_40))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.91/1.43  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_xboole_0(k2_xboole_0(A_1, B_2), C_3)=k2_xboole_0(A_1, k2_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.91/1.43  tff(c_52, plain, (![A_38, B_39, C_40, C_3]: (k2_xboole_0(k1_tarski(A_38), k2_xboole_0(k2_tarski(B_39, C_40), C_3))=k2_xboole_0(k1_enumset1(A_38, B_39, C_40), C_3))), inference(superposition, [status(thm), theory('equality')], [c_46, c_2])).
% 2.91/1.43  tff(c_423, plain, (![D_126, A_123, A_128, E_125, B_124, A_38, C_127]: (k2_xboole_0(k1_tarski(A_38), k2_xboole_0(k1_tarski(A_128), k3_enumset1(A_123, B_124, C_127, D_126, E_125)))=k2_xboole_0(k1_enumset1(A_38, A_128, A_123), k2_enumset1(B_124, C_127, D_126, E_125)))), inference(superposition, [status(thm), theory('equality')], [c_414, c_52])).
% 2.91/1.43  tff(c_555, plain, (![A_159, A_155, D_158, C_156, A_157, B_160, E_161]: (k2_xboole_0(k2_tarski(A_155, A_157), k3_enumset1(A_159, B_160, C_156, D_158, E_161))=k5_enumset1(A_155, A_157, A_159, B_160, C_156, D_158, E_161))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_41, c_423])).
% 2.91/1.43  tff(c_567, plain, (![A_159, A_155, D_158, A_38, C_156, A_157, B_160, E_161]: (k2_xboole_0(k1_enumset1(A_38, A_155, A_157), k3_enumset1(A_159, B_160, C_156, D_158, E_161))=k2_xboole_0(k1_tarski(A_38), k5_enumset1(A_155, A_157, A_159, B_160, C_156, D_158, E_161)))), inference(superposition, [status(thm), theory('equality')], [c_555, c_52])).
% 2.91/1.43  tff(c_575, plain, (![A_159, A_155, D_158, A_38, C_156, A_157, B_160, E_161]: (k2_xboole_0(k1_enumset1(A_38, A_155, A_157), k3_enumset1(A_159, B_160, C_156, D_158, E_161))=k6_enumset1(A_38, A_155, A_157, A_159, B_160, C_156, D_158, E_161))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_567])).
% 2.91/1.43  tff(c_16, plain, (k2_xboole_0(k1_enumset1('#skF_1', '#skF_2', '#skF_3'), k3_enumset1('#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'))!=k6_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.91/1.43  tff(c_732, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_575, c_16])).
% 2.91/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.91/1.43  
% 2.91/1.43  Inference rules
% 2.91/1.43  ----------------------
% 2.91/1.43  #Ref     : 0
% 2.91/1.43  #Sup     : 185
% 2.91/1.43  #Fact    : 0
% 2.91/1.43  #Define  : 0
% 2.91/1.43  #Split   : 0
% 2.91/1.43  #Chain   : 0
% 2.91/1.43  #Close   : 0
% 2.91/1.43  
% 2.91/1.43  Ordering : KBO
% 2.91/1.43  
% 2.91/1.43  Simplification rules
% 2.91/1.43  ----------------------
% 2.91/1.43  #Subsume      : 0
% 2.91/1.43  #Demod        : 112
% 2.91/1.43  #Tautology    : 101
% 2.91/1.43  #SimpNegUnit  : 0
% 2.91/1.43  #BackRed      : 1
% 2.91/1.43  
% 2.91/1.43  #Partial instantiations: 0
% 2.91/1.43  #Strategies tried      : 1
% 2.91/1.43  
% 2.91/1.43  Timing (in seconds)
% 2.91/1.43  ----------------------
% 2.91/1.44  Preprocessing        : 0.27
% 2.91/1.44  Parsing              : 0.15
% 2.91/1.44  CNF conversion       : 0.02
% 2.91/1.44  Main loop            : 0.41
% 2.91/1.44  Inferencing          : 0.18
% 2.91/1.44  Reduction            : 0.14
% 2.91/1.44  Demodulation         : 0.11
% 2.91/1.44  BG Simplification    : 0.03
% 2.91/1.44  Subsumption          : 0.04
% 2.91/1.44  Abstraction          : 0.04
% 2.91/1.44  MUC search           : 0.00
% 2.91/1.44  Cooper               : 0.00
% 2.91/1.44  Total                : 0.71
% 2.91/1.44  Index Insertion      : 0.00
% 2.91/1.44  Index Deletion       : 0.00
% 2.91/1.44  Index Matching       : 0.00
% 2.91/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
