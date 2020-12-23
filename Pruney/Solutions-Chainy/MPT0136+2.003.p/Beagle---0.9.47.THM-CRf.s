%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:44 EST 2020

% Result     : Theorem 2.58s
% Output     : CNFRefutation 2.58s
% Verified   : 
% Statistics : Number of formulae       :   41 (  49 expanded)
%              Number of leaves         :   23 (  28 expanded)
%              Depth                    :   10
%              Number of atoms          :   24 (  32 expanded)
%              Number of equality atoms :   23 (  31 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_33,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_enumset1(A,B,C),k1_enumset1(D,E,F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l62_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k2_tarski(A,B),k1_tarski(C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).

tff(f_35,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_42,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k2_tarski(A,B),k2_enumset1(C,D,E,F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_enumset1)).

tff(c_8,plain,(
    ! [B_11,A_10,C_12,F_15,E_14,D_13] : k2_xboole_0(k1_enumset1(A_10,B_11,C_12),k1_enumset1(D_13,E_14,F_15)) = k4_enumset1(A_10,B_11,C_12,D_13,E_14,F_15) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_14,plain,(
    ! [A_21,B_22,C_23,D_24] : k2_xboole_0(k1_enumset1(A_21,B_22,C_23),k1_tarski(D_24)) = k2_enumset1(A_21,B_22,C_23,D_24) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_12,plain,(
    ! [A_18,B_19,C_20] : k2_xboole_0(k2_tarski(A_18,B_19),k1_tarski(C_20)) = k1_enumset1(A_18,B_19,C_20) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [A_16,B_17] : k2_xboole_0(k1_tarski(A_16),k1_tarski(B_17)) = k2_tarski(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_27,plain,(
    ! [A_27,B_28,C_29] : k2_xboole_0(k2_xboole_0(A_27,B_28),C_29) = k2_xboole_0(A_27,k2_xboole_0(B_28,C_29)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_86,plain,(
    ! [A_39,B_40,C_41] : k2_xboole_0(k1_tarski(A_39),k2_xboole_0(k1_tarski(B_40),C_41)) = k2_xboole_0(k2_tarski(A_39,B_40),C_41) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_27])).

tff(c_104,plain,(
    ! [A_39,A_16,B_17] : k2_xboole_0(k2_tarski(A_39,A_16),k1_tarski(B_17)) = k2_xboole_0(k1_tarski(A_39),k2_tarski(A_16,B_17)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_86])).

tff(c_109,plain,(
    ! [A_42,A_43,B_44] : k2_xboole_0(k1_tarski(A_42),k2_tarski(A_43,B_44)) = k1_enumset1(A_42,A_43,B_44) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_104])).

tff(c_4,plain,(
    ! [A_5,B_6,C_7] : k2_xboole_0(k2_xboole_0(A_5,B_6),C_7) = k2_xboole_0(A_5,k2_xboole_0(B_6,C_7)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_171,plain,(
    ! [A_59,A_60,B_61,C_62] : k2_xboole_0(k1_tarski(A_59),k2_xboole_0(k2_tarski(A_60,B_61),C_62)) = k2_xboole_0(k1_enumset1(A_59,A_60,B_61),C_62) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_4])).

tff(c_195,plain,(
    ! [A_59,A_18,B_19,C_20] : k2_xboole_0(k1_enumset1(A_59,A_18,B_19),k1_tarski(C_20)) = k2_xboole_0(k1_tarski(A_59),k1_enumset1(A_18,B_19,C_20)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_171])).

tff(c_200,plain,(
    ! [A_63,A_64,B_65,C_66] : k2_xboole_0(k1_tarski(A_63),k1_enumset1(A_64,B_65,C_66)) = k2_enumset1(A_63,A_64,B_65,C_66) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_195])).

tff(c_47,plain,(
    ! [A_30,B_31,C_32] : k2_xboole_0(k2_tarski(A_30,B_31),k1_tarski(C_32)) = k1_enumset1(A_30,B_31,C_32) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_53,plain,(
    ! [A_30,B_31,C_32,C_7] : k2_xboole_0(k2_tarski(A_30,B_31),k2_xboole_0(k1_tarski(C_32),C_7)) = k2_xboole_0(k1_enumset1(A_30,B_31,C_32),C_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_47,c_4])).

tff(c_206,plain,(
    ! [A_30,A_63,B_31,C_66,A_64,B_65] : k2_xboole_0(k1_enumset1(A_30,B_31,A_63),k1_enumset1(A_64,B_65,C_66)) = k2_xboole_0(k2_tarski(A_30,B_31),k2_enumset1(A_63,A_64,B_65,C_66)) ),
    inference(superposition,[status(thm),theory(equality)],[c_200,c_53])).

tff(c_217,plain,(
    ! [A_30,A_63,B_31,C_66,A_64,B_65] : k2_xboole_0(k2_tarski(A_30,B_31),k2_enumset1(A_63,A_64,B_65,C_66)) = k4_enumset1(A_30,B_31,A_63,A_64,B_65,C_66) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_206])).

tff(c_16,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),k2_enumset1('#skF_3','#skF_4','#skF_5','#skF_6')) != k4_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_472,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_217,c_16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:42:29 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.58/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.58/1.31  
% 2.58/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.58/1.31  %$ k4_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.58/1.31  
% 2.58/1.31  %Foreground sorts:
% 2.58/1.31  
% 2.58/1.31  
% 2.58/1.31  %Background operators:
% 2.58/1.31  
% 2.58/1.31  
% 2.58/1.31  %Foreground operators:
% 2.58/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.58/1.31  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.58/1.31  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.58/1.31  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.58/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.58/1.31  tff('#skF_5', type, '#skF_5': $i).
% 2.58/1.31  tff('#skF_6', type, '#skF_6': $i).
% 2.58/1.31  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.58/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.58/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.58/1.31  tff('#skF_1', type, '#skF_1': $i).
% 2.58/1.31  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.58/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.58/1.31  tff('#skF_4', type, '#skF_4': $i).
% 2.58/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.58/1.31  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.58/1.31  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.58/1.31  
% 2.58/1.32  tff(f_33, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_enumset1(A, B, C), k1_enumset1(D, E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l62_enumset1)).
% 2.58/1.32  tff(f_39, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_enumset1)).
% 2.58/1.32  tff(f_37, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k2_tarski(A, B), k1_tarski(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_enumset1)).
% 2.58/1.32  tff(f_35, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 2.58/1.32  tff(f_29, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 2.58/1.32  tff(f_42, negated_conjecture, ~(![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k2_tarski(A, B), k2_enumset1(C, D, E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_enumset1)).
% 2.58/1.32  tff(c_8, plain, (![B_11, A_10, C_12, F_15, E_14, D_13]: (k2_xboole_0(k1_enumset1(A_10, B_11, C_12), k1_enumset1(D_13, E_14, F_15))=k4_enumset1(A_10, B_11, C_12, D_13, E_14, F_15))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.58/1.32  tff(c_14, plain, (![A_21, B_22, C_23, D_24]: (k2_xboole_0(k1_enumset1(A_21, B_22, C_23), k1_tarski(D_24))=k2_enumset1(A_21, B_22, C_23, D_24))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.58/1.32  tff(c_12, plain, (![A_18, B_19, C_20]: (k2_xboole_0(k2_tarski(A_18, B_19), k1_tarski(C_20))=k1_enumset1(A_18, B_19, C_20))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.58/1.32  tff(c_10, plain, (![A_16, B_17]: (k2_xboole_0(k1_tarski(A_16), k1_tarski(B_17))=k2_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.58/1.32  tff(c_27, plain, (![A_27, B_28, C_29]: (k2_xboole_0(k2_xboole_0(A_27, B_28), C_29)=k2_xboole_0(A_27, k2_xboole_0(B_28, C_29)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.58/1.32  tff(c_86, plain, (![A_39, B_40, C_41]: (k2_xboole_0(k1_tarski(A_39), k2_xboole_0(k1_tarski(B_40), C_41))=k2_xboole_0(k2_tarski(A_39, B_40), C_41))), inference(superposition, [status(thm), theory('equality')], [c_10, c_27])).
% 2.58/1.32  tff(c_104, plain, (![A_39, A_16, B_17]: (k2_xboole_0(k2_tarski(A_39, A_16), k1_tarski(B_17))=k2_xboole_0(k1_tarski(A_39), k2_tarski(A_16, B_17)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_86])).
% 2.58/1.32  tff(c_109, plain, (![A_42, A_43, B_44]: (k2_xboole_0(k1_tarski(A_42), k2_tarski(A_43, B_44))=k1_enumset1(A_42, A_43, B_44))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_104])).
% 2.58/1.32  tff(c_4, plain, (![A_5, B_6, C_7]: (k2_xboole_0(k2_xboole_0(A_5, B_6), C_7)=k2_xboole_0(A_5, k2_xboole_0(B_6, C_7)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.58/1.32  tff(c_171, plain, (![A_59, A_60, B_61, C_62]: (k2_xboole_0(k1_tarski(A_59), k2_xboole_0(k2_tarski(A_60, B_61), C_62))=k2_xboole_0(k1_enumset1(A_59, A_60, B_61), C_62))), inference(superposition, [status(thm), theory('equality')], [c_109, c_4])).
% 2.58/1.32  tff(c_195, plain, (![A_59, A_18, B_19, C_20]: (k2_xboole_0(k1_enumset1(A_59, A_18, B_19), k1_tarski(C_20))=k2_xboole_0(k1_tarski(A_59), k1_enumset1(A_18, B_19, C_20)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_171])).
% 2.58/1.32  tff(c_200, plain, (![A_63, A_64, B_65, C_66]: (k2_xboole_0(k1_tarski(A_63), k1_enumset1(A_64, B_65, C_66))=k2_enumset1(A_63, A_64, B_65, C_66))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_195])).
% 2.58/1.32  tff(c_47, plain, (![A_30, B_31, C_32]: (k2_xboole_0(k2_tarski(A_30, B_31), k1_tarski(C_32))=k1_enumset1(A_30, B_31, C_32))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.58/1.32  tff(c_53, plain, (![A_30, B_31, C_32, C_7]: (k2_xboole_0(k2_tarski(A_30, B_31), k2_xboole_0(k1_tarski(C_32), C_7))=k2_xboole_0(k1_enumset1(A_30, B_31, C_32), C_7))), inference(superposition, [status(thm), theory('equality')], [c_47, c_4])).
% 2.58/1.32  tff(c_206, plain, (![A_30, A_63, B_31, C_66, A_64, B_65]: (k2_xboole_0(k1_enumset1(A_30, B_31, A_63), k1_enumset1(A_64, B_65, C_66))=k2_xboole_0(k2_tarski(A_30, B_31), k2_enumset1(A_63, A_64, B_65, C_66)))), inference(superposition, [status(thm), theory('equality')], [c_200, c_53])).
% 2.58/1.32  tff(c_217, plain, (![A_30, A_63, B_31, C_66, A_64, B_65]: (k2_xboole_0(k2_tarski(A_30, B_31), k2_enumset1(A_63, A_64, B_65, C_66))=k4_enumset1(A_30, B_31, A_63, A_64, B_65, C_66))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_206])).
% 2.58/1.32  tff(c_16, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), k2_enumset1('#skF_3', '#skF_4', '#skF_5', '#skF_6'))!=k4_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.58/1.32  tff(c_472, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_217, c_16])).
% 2.58/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.58/1.32  
% 2.58/1.32  Inference rules
% 2.58/1.32  ----------------------
% 2.58/1.32  #Ref     : 0
% 2.58/1.32  #Sup     : 118
% 2.58/1.32  #Fact    : 0
% 2.58/1.32  #Define  : 0
% 2.58/1.32  #Split   : 0
% 2.58/1.32  #Chain   : 0
% 2.58/1.32  #Close   : 0
% 2.58/1.32  
% 2.58/1.32  Ordering : KBO
% 2.58/1.32  
% 2.58/1.32  Simplification rules
% 2.58/1.32  ----------------------
% 2.58/1.32  #Subsume      : 0
% 2.58/1.32  #Demod        : 58
% 2.58/1.32  #Tautology    : 57
% 2.58/1.32  #SimpNegUnit  : 0
% 2.58/1.32  #BackRed      : 4
% 2.58/1.32  
% 2.58/1.32  #Partial instantiations: 0
% 2.58/1.32  #Strategies tried      : 1
% 2.58/1.32  
% 2.58/1.32  Timing (in seconds)
% 2.58/1.32  ----------------------
% 2.58/1.33  Preprocessing        : 0.28
% 2.58/1.33  Parsing              : 0.16
% 2.58/1.33  CNF conversion       : 0.02
% 2.58/1.33  Main loop            : 0.31
% 2.58/1.33  Inferencing          : 0.14
% 2.58/1.33  Reduction            : 0.10
% 2.58/1.33  Demodulation         : 0.08
% 2.58/1.33  BG Simplification    : 0.02
% 2.58/1.33  Subsumption          : 0.04
% 2.58/1.33  Abstraction          : 0.02
% 2.58/1.33  MUC search           : 0.00
% 2.58/1.33  Cooper               : 0.00
% 2.58/1.33  Total                : 0.61
% 2.58/1.33  Index Insertion      : 0.00
% 2.58/1.33  Index Deletion       : 0.00
% 2.58/1.33  Index Matching       : 0.00
% 2.58/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
