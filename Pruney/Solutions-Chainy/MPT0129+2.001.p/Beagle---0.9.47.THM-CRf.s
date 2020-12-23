%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:38 EST 2020

% Result     : Theorem 6.65s
% Output     : CNFRefutation 6.65s
% Verified   : 
% Statistics : Number of formulae       :   45 (  83 expanded)
%              Number of leaves         :   18 (  37 expanded)
%              Depth                    :    7
%              Number of atoms          :   33 (  71 expanded)
%              Number of equality atoms :   32 (  70 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_33,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_38,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_enumset1)).

tff(c_400,plain,(
    ! [A_35,B_36,C_37,D_38] : k2_xboole_0(k1_tarski(A_35),k1_enumset1(B_36,C_37,D_38)) = k2_enumset1(A_35,B_36,C_37,D_38) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_418,plain,(
    ! [B_36,C_37,D_38,A_35] : k2_xboole_0(k1_enumset1(B_36,C_37,D_38),k1_tarski(A_35)) = k2_enumset1(A_35,B_36,C_37,D_38) ),
    inference(superposition,[status(thm),theory(equality)],[c_400,c_2])).

tff(c_10,plain,(
    ! [A_11,B_12,C_13,D_14] : k2_xboole_0(k1_tarski(A_11),k1_enumset1(B_12,C_13,D_14)) = k2_enumset1(A_11,B_12,C_13,D_14) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_131,plain,(
    ! [A_23,B_24,C_25] : k2_xboole_0(k1_tarski(A_23),k2_tarski(B_24,C_25)) = k1_enumset1(A_23,B_24,C_25) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_155,plain,(
    ! [B_24,C_25,A_23] : k2_xboole_0(k2_tarski(B_24,C_25),k1_tarski(A_23)) = k1_enumset1(A_23,B_24,C_25) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_131])).

tff(c_8,plain,(
    ! [A_8,B_9,C_10] : k2_xboole_0(k1_tarski(A_8),k2_tarski(B_9,C_10)) = k1_enumset1(A_8,B_9,C_10) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_162,plain,(
    ! [A_26,B_27,C_28] : k2_xboole_0(k2_xboole_0(A_26,B_27),C_28) = k2_xboole_0(A_26,k2_xboole_0(B_27,C_28)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2810,plain,(
    ! [A_82,B_83,C_84,C_85] : k2_xboole_0(k1_tarski(A_82),k2_xboole_0(k2_tarski(B_83,C_84),C_85)) = k2_xboole_0(k1_enumset1(A_82,B_83,C_84),C_85) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_162])).

tff(c_2959,plain,(
    ! [A_82,B_24,C_25,A_23] : k2_xboole_0(k1_enumset1(A_82,B_24,C_25),k1_tarski(A_23)) = k2_xboole_0(k1_tarski(A_82),k1_enumset1(A_23,B_24,C_25)) ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_2810])).

tff(c_2995,plain,(
    ! [A_82,A_23,B_24,C_25] : k2_enumset1(A_82,A_23,B_24,C_25) = k2_enumset1(A_23,A_82,B_24,C_25) ),
    inference(demodulation,[status(thm),theory(equality)],[c_418,c_10,c_2959])).

tff(c_6,plain,(
    ! [A_6,B_7] : k2_xboole_0(k1_tarski(A_6),k1_tarski(B_7)) = k2_tarski(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1310,plain,(
    ! [A_55,B_56,C_57] : k2_xboole_0(k1_tarski(A_55),k2_xboole_0(k1_tarski(B_56),C_57)) = k2_xboole_0(k2_tarski(A_55,B_56),C_57) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_162])).

tff(c_1427,plain,(
    ! [A_55,A_8,B_9,C_10] : k2_xboole_0(k2_tarski(A_55,A_8),k2_tarski(B_9,C_10)) = k2_xboole_0(k1_tarski(A_55),k1_enumset1(A_8,B_9,C_10)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_1310])).

tff(c_1460,plain,(
    ! [A_55,A_8,B_9,C_10] : k2_xboole_0(k2_tarski(A_55,A_8),k2_tarski(B_9,C_10)) = k2_enumset1(A_55,A_8,B_9,C_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1427])).

tff(c_243,plain,(
    ! [C_32,A_33,B_34] : k2_xboole_0(C_32,k2_xboole_0(A_33,B_34)) = k2_xboole_0(A_33,k2_xboole_0(B_34,C_32)) ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_2])).

tff(c_4820,plain,(
    ! [A_111,B_112,C_113] : k2_xboole_0(k1_tarski(A_111),k2_xboole_0(k1_tarski(B_112),C_113)) = k2_xboole_0(C_113,k2_tarski(A_111,B_112)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_243])).

tff(c_5018,plain,(
    ! [B_9,C_10,A_111,A_8] : k2_xboole_0(k2_tarski(B_9,C_10),k2_tarski(A_111,A_8)) = k2_xboole_0(k1_tarski(A_111),k1_enumset1(A_8,B_9,C_10)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_4820])).

tff(c_5074,plain,(
    ! [B_114,C_115,A_116,A_117] : k2_enumset1(B_114,C_115,A_116,A_117) = k2_enumset1(A_116,A_117,B_114,C_115) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1460,c_10,c_5018])).

tff(c_5122,plain,(
    ! [B_24,C_25,A_82,A_23] : k2_enumset1(B_24,C_25,A_82,A_23) = k2_enumset1(A_23,A_82,B_24,C_25) ),
    inference(superposition,[status(thm),theory(equality)],[c_2995,c_5074])).

tff(c_46,plain,(
    ! [A_17,B_18] : k2_xboole_0(k1_tarski(A_17),k1_tarski(B_18)) = k2_tarski(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_67,plain,(
    ! [B_19,A_20] : k2_xboole_0(k1_tarski(B_19),k1_tarski(A_20)) = k2_tarski(A_20,B_19) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_2])).

tff(c_73,plain,(
    ! [B_19,A_20] : k2_tarski(B_19,A_20) = k2_tarski(A_20,B_19) ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_6])).

tff(c_12,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),k2_tarski('#skF_3','#skF_4')) != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_161,plain,(
    k2_xboole_0(k2_tarski('#skF_4','#skF_3'),k2_tarski('#skF_1','#skF_2')) != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_73,c_12])).

tff(c_4692,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_enumset1('#skF_4','#skF_3','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1460,c_161])).

tff(c_5134,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5122,c_4692])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:59:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.65/2.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.65/2.44  
% 6.65/2.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.65/2.45  %$ k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.65/2.45  
% 6.65/2.45  %Foreground sorts:
% 6.65/2.45  
% 6.65/2.45  
% 6.65/2.45  %Background operators:
% 6.65/2.45  
% 6.65/2.45  
% 6.65/2.45  %Foreground operators:
% 6.65/2.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.65/2.45  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.65/2.45  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.65/2.45  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.65/2.45  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.65/2.45  tff('#skF_2', type, '#skF_2': $i).
% 6.65/2.45  tff('#skF_3', type, '#skF_3': $i).
% 6.65/2.45  tff('#skF_1', type, '#skF_1': $i).
% 6.65/2.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.65/2.45  tff('#skF_4', type, '#skF_4': $i).
% 6.65/2.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.65/2.45  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.65/2.45  
% 6.65/2.46  tff(f_35, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_enumset1)).
% 6.65/2.46  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 6.65/2.46  tff(f_33, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_enumset1)).
% 6.65/2.46  tff(f_29, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 6.65/2.46  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 6.65/2.46  tff(f_38, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_enumset1)).
% 6.65/2.46  tff(c_400, plain, (![A_35, B_36, C_37, D_38]: (k2_xboole_0(k1_tarski(A_35), k1_enumset1(B_36, C_37, D_38))=k2_enumset1(A_35, B_36, C_37, D_38))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.65/2.46  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.65/2.46  tff(c_418, plain, (![B_36, C_37, D_38, A_35]: (k2_xboole_0(k1_enumset1(B_36, C_37, D_38), k1_tarski(A_35))=k2_enumset1(A_35, B_36, C_37, D_38))), inference(superposition, [status(thm), theory('equality')], [c_400, c_2])).
% 6.65/2.46  tff(c_10, plain, (![A_11, B_12, C_13, D_14]: (k2_xboole_0(k1_tarski(A_11), k1_enumset1(B_12, C_13, D_14))=k2_enumset1(A_11, B_12, C_13, D_14))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.65/2.46  tff(c_131, plain, (![A_23, B_24, C_25]: (k2_xboole_0(k1_tarski(A_23), k2_tarski(B_24, C_25))=k1_enumset1(A_23, B_24, C_25))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.65/2.46  tff(c_155, plain, (![B_24, C_25, A_23]: (k2_xboole_0(k2_tarski(B_24, C_25), k1_tarski(A_23))=k1_enumset1(A_23, B_24, C_25))), inference(superposition, [status(thm), theory('equality')], [c_2, c_131])).
% 6.65/2.46  tff(c_8, plain, (![A_8, B_9, C_10]: (k2_xboole_0(k1_tarski(A_8), k2_tarski(B_9, C_10))=k1_enumset1(A_8, B_9, C_10))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.65/2.46  tff(c_162, plain, (![A_26, B_27, C_28]: (k2_xboole_0(k2_xboole_0(A_26, B_27), C_28)=k2_xboole_0(A_26, k2_xboole_0(B_27, C_28)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.65/2.46  tff(c_2810, plain, (![A_82, B_83, C_84, C_85]: (k2_xboole_0(k1_tarski(A_82), k2_xboole_0(k2_tarski(B_83, C_84), C_85))=k2_xboole_0(k1_enumset1(A_82, B_83, C_84), C_85))), inference(superposition, [status(thm), theory('equality')], [c_8, c_162])).
% 6.65/2.46  tff(c_2959, plain, (![A_82, B_24, C_25, A_23]: (k2_xboole_0(k1_enumset1(A_82, B_24, C_25), k1_tarski(A_23))=k2_xboole_0(k1_tarski(A_82), k1_enumset1(A_23, B_24, C_25)))), inference(superposition, [status(thm), theory('equality')], [c_155, c_2810])).
% 6.65/2.46  tff(c_2995, plain, (![A_82, A_23, B_24, C_25]: (k2_enumset1(A_82, A_23, B_24, C_25)=k2_enumset1(A_23, A_82, B_24, C_25))), inference(demodulation, [status(thm), theory('equality')], [c_418, c_10, c_2959])).
% 6.65/2.46  tff(c_6, plain, (![A_6, B_7]: (k2_xboole_0(k1_tarski(A_6), k1_tarski(B_7))=k2_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.65/2.46  tff(c_1310, plain, (![A_55, B_56, C_57]: (k2_xboole_0(k1_tarski(A_55), k2_xboole_0(k1_tarski(B_56), C_57))=k2_xboole_0(k2_tarski(A_55, B_56), C_57))), inference(superposition, [status(thm), theory('equality')], [c_6, c_162])).
% 6.65/2.46  tff(c_1427, plain, (![A_55, A_8, B_9, C_10]: (k2_xboole_0(k2_tarski(A_55, A_8), k2_tarski(B_9, C_10))=k2_xboole_0(k1_tarski(A_55), k1_enumset1(A_8, B_9, C_10)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_1310])).
% 6.65/2.46  tff(c_1460, plain, (![A_55, A_8, B_9, C_10]: (k2_xboole_0(k2_tarski(A_55, A_8), k2_tarski(B_9, C_10))=k2_enumset1(A_55, A_8, B_9, C_10))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_1427])).
% 6.65/2.46  tff(c_243, plain, (![C_32, A_33, B_34]: (k2_xboole_0(C_32, k2_xboole_0(A_33, B_34))=k2_xboole_0(A_33, k2_xboole_0(B_34, C_32)))), inference(superposition, [status(thm), theory('equality')], [c_162, c_2])).
% 6.65/2.46  tff(c_4820, plain, (![A_111, B_112, C_113]: (k2_xboole_0(k1_tarski(A_111), k2_xboole_0(k1_tarski(B_112), C_113))=k2_xboole_0(C_113, k2_tarski(A_111, B_112)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_243])).
% 6.65/2.46  tff(c_5018, plain, (![B_9, C_10, A_111, A_8]: (k2_xboole_0(k2_tarski(B_9, C_10), k2_tarski(A_111, A_8))=k2_xboole_0(k1_tarski(A_111), k1_enumset1(A_8, B_9, C_10)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_4820])).
% 6.65/2.46  tff(c_5074, plain, (![B_114, C_115, A_116, A_117]: (k2_enumset1(B_114, C_115, A_116, A_117)=k2_enumset1(A_116, A_117, B_114, C_115))), inference(demodulation, [status(thm), theory('equality')], [c_1460, c_10, c_5018])).
% 6.65/2.46  tff(c_5122, plain, (![B_24, C_25, A_82, A_23]: (k2_enumset1(B_24, C_25, A_82, A_23)=k2_enumset1(A_23, A_82, B_24, C_25))), inference(superposition, [status(thm), theory('equality')], [c_2995, c_5074])).
% 6.65/2.46  tff(c_46, plain, (![A_17, B_18]: (k2_xboole_0(k1_tarski(A_17), k1_tarski(B_18))=k2_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.65/2.46  tff(c_67, plain, (![B_19, A_20]: (k2_xboole_0(k1_tarski(B_19), k1_tarski(A_20))=k2_tarski(A_20, B_19))), inference(superposition, [status(thm), theory('equality')], [c_46, c_2])).
% 6.65/2.46  tff(c_73, plain, (![B_19, A_20]: (k2_tarski(B_19, A_20)=k2_tarski(A_20, B_19))), inference(superposition, [status(thm), theory('equality')], [c_67, c_6])).
% 6.65/2.46  tff(c_12, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), k2_tarski('#skF_3', '#skF_4'))!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.65/2.46  tff(c_161, plain, (k2_xboole_0(k2_tarski('#skF_4', '#skF_3'), k2_tarski('#skF_1', '#skF_2'))!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_73, c_12])).
% 6.65/2.46  tff(c_4692, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_enumset1('#skF_4', '#skF_3', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1460, c_161])).
% 6.65/2.46  tff(c_5134, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5122, c_4692])).
% 6.65/2.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.65/2.46  
% 6.65/2.46  Inference rules
% 6.65/2.46  ----------------------
% 6.65/2.46  #Ref     : 0
% 6.65/2.46  #Sup     : 1393
% 6.65/2.46  #Fact    : 0
% 6.65/2.46  #Define  : 0
% 6.65/2.46  #Split   : 0
% 6.65/2.46  #Chain   : 0
% 6.65/2.46  #Close   : 0
% 6.65/2.46  
% 6.65/2.46  Ordering : KBO
% 6.65/2.46  
% 6.65/2.46  Simplification rules
% 6.65/2.46  ----------------------
% 6.65/2.46  #Subsume      : 249
% 6.65/2.46  #Demod        : 559
% 6.65/2.46  #Tautology    : 275
% 6.65/2.46  #SimpNegUnit  : 0
% 6.65/2.46  #BackRed      : 2
% 6.65/2.46  
% 6.65/2.46  #Partial instantiations: 0
% 6.65/2.46  #Strategies tried      : 1
% 6.65/2.46  
% 6.65/2.46  Timing (in seconds)
% 6.65/2.46  ----------------------
% 6.65/2.46  Preprocessing        : 0.25
% 6.65/2.46  Parsing              : 0.14
% 6.65/2.46  CNF conversion       : 0.01
% 6.65/2.46  Main loop            : 1.45
% 6.65/2.46  Inferencing          : 0.32
% 6.65/2.46  Reduction            : 0.88
% 6.65/2.46  Demodulation         : 0.82
% 6.65/2.46  BG Simplification    : 0.06
% 6.65/2.46  Subsumption          : 0.14
% 6.65/2.46  Abstraction          : 0.07
% 6.65/2.46  MUC search           : 0.00
% 6.65/2.46  Cooper               : 0.00
% 6.65/2.46  Total                : 1.73
% 6.65/2.46  Index Insertion      : 0.00
% 6.65/2.46  Index Deletion       : 0.00
% 6.65/2.46  Index Matching       : 0.00
% 6.65/2.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
