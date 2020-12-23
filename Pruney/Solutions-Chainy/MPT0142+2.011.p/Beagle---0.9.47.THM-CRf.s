%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:50 EST 2020

% Result     : Theorem 2.24s
% Output     : CNFRefutation 2.24s
% Verified   : 
% Statistics : Number of formulae       :   42 (  43 expanded)
%              Number of leaves         :   27 (  28 expanded)
%              Depth                    :    7
%              Number of atoms          :   22 (  23 expanded)
%              Number of equality atoms :   21 (  22 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff(f_39,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k1_tarski(A),k4_enumset1(B,C,D,E,F,G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_tarski(A),k3_enumset1(B,C,D,E,F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_tarski(A),k2_enumset1(B,C,D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_42,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k1_enumset1(A,B,C),k2_enumset1(D,E,F,G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_enumset1)).

tff(c_14,plain,(
    ! [G_28,E_26,F_27,A_22,B_23,D_25,C_24] : k2_xboole_0(k1_tarski(A_22),k4_enumset1(B_23,C_24,D_25,E_26,F_27,G_28)) = k5_enumset1(A_22,B_23,C_24,D_25,E_26,F_27,G_28) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_12,plain,(
    ! [C_18,B_17,A_16,D_19,E_20,F_21] : k2_xboole_0(k1_tarski(A_16),k3_enumset1(B_17,C_18,D_19,E_20,F_21)) = k4_enumset1(A_16,B_17,C_18,D_19,E_20,F_21) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_93,plain,(
    ! [C_42,D_45,E_46,A_43,B_44] : k2_xboole_0(k1_tarski(A_43),k2_enumset1(B_44,C_42,D_45,E_46)) = k3_enumset1(A_43,B_44,C_42,D_45,E_46) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6,plain,(
    ! [A_6,B_7] : k2_xboole_0(k1_tarski(A_6),k1_tarski(B_7)) = k2_tarski(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_35,plain,(
    ! [A_33,B_34,C_35] : k2_xboole_0(k2_xboole_0(A_33,B_34),C_35) = k2_xboole_0(A_33,k2_xboole_0(B_34,C_35)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_50,plain,(
    ! [A_6,B_7,C_35] : k2_xboole_0(k1_tarski(A_6),k2_xboole_0(k1_tarski(B_7),C_35)) = k2_xboole_0(k2_tarski(A_6,B_7),C_35) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_35])).

tff(c_99,plain,(
    ! [C_42,D_45,E_46,A_43,B_44,A_6] : k2_xboole_0(k2_tarski(A_6,A_43),k2_enumset1(B_44,C_42,D_45,E_46)) = k2_xboole_0(k1_tarski(A_6),k3_enumset1(A_43,B_44,C_42,D_45,E_46)) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_50])).

tff(c_310,plain,(
    ! [A_98,D_96,E_95,B_99,C_97,A_100] : k2_xboole_0(k2_tarski(A_100,A_98),k2_enumset1(B_99,C_97,D_96,E_95)) = k4_enumset1(A_100,A_98,B_99,C_97,D_96,E_95) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_99])).

tff(c_55,plain,(
    ! [A_36,B_37,C_38] : k2_xboole_0(k1_tarski(A_36),k2_tarski(B_37,C_38)) = k1_enumset1(A_36,B_37,C_38) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_xboole_0(k2_xboole_0(A_1,B_2),C_3) = k2_xboole_0(A_1,k2_xboole_0(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_61,plain,(
    ! [A_36,B_37,C_38,C_3] : k2_xboole_0(k1_tarski(A_36),k2_xboole_0(k2_tarski(B_37,C_38),C_3)) = k2_xboole_0(k1_enumset1(A_36,B_37,C_38),C_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_2])).

tff(c_319,plain,(
    ! [A_98,D_96,A_36,E_95,B_99,C_97,A_100] : k2_xboole_0(k1_enumset1(A_36,A_100,A_98),k2_enumset1(B_99,C_97,D_96,E_95)) = k2_xboole_0(k1_tarski(A_36),k4_enumset1(A_100,A_98,B_99,C_97,D_96,E_95)) ),
    inference(superposition,[status(thm),theory(equality)],[c_310,c_61])).

tff(c_327,plain,(
    ! [A_98,D_96,A_36,E_95,B_99,C_97,A_100] : k2_xboole_0(k1_enumset1(A_36,A_100,A_98),k2_enumset1(B_99,C_97,D_96,E_95)) = k5_enumset1(A_36,A_100,A_98,B_99,C_97,D_96,E_95) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_319])).

tff(c_16,plain,(
    k2_xboole_0(k1_enumset1('#skF_1','#skF_2','#skF_3'),k2_enumset1('#skF_4','#skF_5','#skF_6','#skF_7')) != k5_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_332,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_327,c_16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:28:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.24/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.27  
% 2.24/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.27  %$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.24/1.27  
% 2.24/1.27  %Foreground sorts:
% 2.24/1.27  
% 2.24/1.27  
% 2.24/1.27  %Background operators:
% 2.24/1.27  
% 2.24/1.27  
% 2.24/1.27  %Foreground operators:
% 2.24/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.24/1.27  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.24/1.27  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.24/1.27  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.24/1.27  tff('#skF_7', type, '#skF_7': $i).
% 2.24/1.27  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.24/1.27  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.24/1.27  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.24/1.27  tff('#skF_5', type, '#skF_5': $i).
% 2.24/1.27  tff('#skF_6', type, '#skF_6': $i).
% 2.24/1.27  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.24/1.27  tff('#skF_2', type, '#skF_2': $i).
% 2.24/1.27  tff('#skF_3', type, '#skF_3': $i).
% 2.24/1.27  tff('#skF_1', type, '#skF_1': $i).
% 2.24/1.27  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.24/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.24/1.27  tff('#skF_4', type, '#skF_4': $i).
% 2.24/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.24/1.27  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.24/1.27  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.24/1.27  
% 2.24/1.28  tff(f_39, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k1_tarski(A), k4_enumset1(B, C, D, E, F, G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_enumset1)).
% 2.24/1.28  tff(f_37, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_tarski(A), k3_enumset1(B, C, D, E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_enumset1)).
% 2.24/1.28  tff(f_35, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_tarski(A), k2_enumset1(B, C, D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_enumset1)).
% 2.24/1.28  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 2.24/1.28  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 2.24/1.28  tff(f_33, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_enumset1)).
% 2.24/1.28  tff(f_42, negated_conjecture, ~(![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k1_enumset1(A, B, C), k2_enumset1(D, E, F, G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_enumset1)).
% 2.24/1.28  tff(c_14, plain, (![G_28, E_26, F_27, A_22, B_23, D_25, C_24]: (k2_xboole_0(k1_tarski(A_22), k4_enumset1(B_23, C_24, D_25, E_26, F_27, G_28))=k5_enumset1(A_22, B_23, C_24, D_25, E_26, F_27, G_28))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.24/1.28  tff(c_12, plain, (![C_18, B_17, A_16, D_19, E_20, F_21]: (k2_xboole_0(k1_tarski(A_16), k3_enumset1(B_17, C_18, D_19, E_20, F_21))=k4_enumset1(A_16, B_17, C_18, D_19, E_20, F_21))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.24/1.28  tff(c_93, plain, (![C_42, D_45, E_46, A_43, B_44]: (k2_xboole_0(k1_tarski(A_43), k2_enumset1(B_44, C_42, D_45, E_46))=k3_enumset1(A_43, B_44, C_42, D_45, E_46))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.24/1.28  tff(c_6, plain, (![A_6, B_7]: (k2_xboole_0(k1_tarski(A_6), k1_tarski(B_7))=k2_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.24/1.28  tff(c_35, plain, (![A_33, B_34, C_35]: (k2_xboole_0(k2_xboole_0(A_33, B_34), C_35)=k2_xboole_0(A_33, k2_xboole_0(B_34, C_35)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.24/1.28  tff(c_50, plain, (![A_6, B_7, C_35]: (k2_xboole_0(k1_tarski(A_6), k2_xboole_0(k1_tarski(B_7), C_35))=k2_xboole_0(k2_tarski(A_6, B_7), C_35))), inference(superposition, [status(thm), theory('equality')], [c_6, c_35])).
% 2.24/1.28  tff(c_99, plain, (![C_42, D_45, E_46, A_43, B_44, A_6]: (k2_xboole_0(k2_tarski(A_6, A_43), k2_enumset1(B_44, C_42, D_45, E_46))=k2_xboole_0(k1_tarski(A_6), k3_enumset1(A_43, B_44, C_42, D_45, E_46)))), inference(superposition, [status(thm), theory('equality')], [c_93, c_50])).
% 2.24/1.28  tff(c_310, plain, (![A_98, D_96, E_95, B_99, C_97, A_100]: (k2_xboole_0(k2_tarski(A_100, A_98), k2_enumset1(B_99, C_97, D_96, E_95))=k4_enumset1(A_100, A_98, B_99, C_97, D_96, E_95))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_99])).
% 2.24/1.28  tff(c_55, plain, (![A_36, B_37, C_38]: (k2_xboole_0(k1_tarski(A_36), k2_tarski(B_37, C_38))=k1_enumset1(A_36, B_37, C_38))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.24/1.28  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_xboole_0(k2_xboole_0(A_1, B_2), C_3)=k2_xboole_0(A_1, k2_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.24/1.28  tff(c_61, plain, (![A_36, B_37, C_38, C_3]: (k2_xboole_0(k1_tarski(A_36), k2_xboole_0(k2_tarski(B_37, C_38), C_3))=k2_xboole_0(k1_enumset1(A_36, B_37, C_38), C_3))), inference(superposition, [status(thm), theory('equality')], [c_55, c_2])).
% 2.24/1.28  tff(c_319, plain, (![A_98, D_96, A_36, E_95, B_99, C_97, A_100]: (k2_xboole_0(k1_enumset1(A_36, A_100, A_98), k2_enumset1(B_99, C_97, D_96, E_95))=k2_xboole_0(k1_tarski(A_36), k4_enumset1(A_100, A_98, B_99, C_97, D_96, E_95)))), inference(superposition, [status(thm), theory('equality')], [c_310, c_61])).
% 2.24/1.28  tff(c_327, plain, (![A_98, D_96, A_36, E_95, B_99, C_97, A_100]: (k2_xboole_0(k1_enumset1(A_36, A_100, A_98), k2_enumset1(B_99, C_97, D_96, E_95))=k5_enumset1(A_36, A_100, A_98, B_99, C_97, D_96, E_95))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_319])).
% 2.24/1.28  tff(c_16, plain, (k2_xboole_0(k1_enumset1('#skF_1', '#skF_2', '#skF_3'), k2_enumset1('#skF_4', '#skF_5', '#skF_6', '#skF_7'))!=k5_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.24/1.28  tff(c_332, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_327, c_16])).
% 2.24/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.28  
% 2.24/1.28  Inference rules
% 2.24/1.28  ----------------------
% 2.24/1.28  #Ref     : 0
% 2.24/1.28  #Sup     : 79
% 2.24/1.28  #Fact    : 0
% 2.24/1.28  #Define  : 0
% 2.24/1.28  #Split   : 0
% 2.24/1.28  #Chain   : 0
% 2.24/1.28  #Close   : 0
% 2.24/1.28  
% 2.24/1.28  Ordering : KBO
% 2.24/1.28  
% 2.24/1.28  Simplification rules
% 2.24/1.28  ----------------------
% 2.24/1.28  #Subsume      : 0
% 2.24/1.28  #Demod        : 46
% 2.24/1.28  #Tautology    : 48
% 2.24/1.28  #SimpNegUnit  : 0
% 2.24/1.28  #BackRed      : 1
% 2.24/1.28  
% 2.24/1.28  #Partial instantiations: 0
% 2.24/1.28  #Strategies tried      : 1
% 2.24/1.28  
% 2.24/1.28  Timing (in seconds)
% 2.24/1.28  ----------------------
% 2.24/1.29  Preprocessing        : 0.28
% 2.24/1.29  Parsing              : 0.15
% 2.24/1.29  CNF conversion       : 0.02
% 2.24/1.29  Main loop            : 0.25
% 2.24/1.29  Inferencing          : 0.11
% 2.24/1.29  Reduction            : 0.08
% 2.24/1.29  Demodulation         : 0.07
% 2.24/1.29  BG Simplification    : 0.02
% 2.24/1.29  Subsumption          : 0.03
% 2.24/1.29  Abstraction          : 0.02
% 2.24/1.29  MUC search           : 0.00
% 2.24/1.29  Cooper               : 0.00
% 2.24/1.29  Total                : 0.55
% 2.24/1.29  Index Insertion      : 0.00
% 2.24/1.29  Index Deletion       : 0.00
% 2.24/1.29  Index Matching       : 0.00
% 2.24/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
