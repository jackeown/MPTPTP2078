%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:42 EST 2020

% Result     : Theorem 2.07s
% Output     : CNFRefutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :   40 (  48 expanded)
%              Number of leaves         :   22 (  27 expanded)
%              Depth                    :    9
%              Number of atoms          :   24 (  32 expanded)
%              Number of equality atoms :   23 (  31 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_37,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_tarski(A),k2_enumset1(B,C,D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_40,negated_conjecture,(
    ~ ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_tarski(E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_enumset1)).

tff(c_12,plain,(
    ! [B_16,A_15,D_18,E_19,C_17] : k2_xboole_0(k1_tarski(A_15),k2_enumset1(B_16,C_17,D_18,E_19)) = k3_enumset1(A_15,B_16,C_17,D_18,E_19) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [A_11,B_12,C_13,D_14] : k2_xboole_0(k1_tarski(A_11),k1_enumset1(B_12,C_13,D_14)) = k2_enumset1(A_11,B_12,C_13,D_14) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [A_8,B_9,C_10] : k2_xboole_0(k1_tarski(A_8),k2_tarski(B_9,C_10)) = k1_enumset1(A_8,B_9,C_10) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [A_6,B_7] : k2_xboole_0(k1_tarski(A_6),k1_tarski(B_7)) = k2_tarski(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_42,plain,(
    ! [A_27,B_28,C_29] : k2_xboole_0(k2_xboole_0(A_27,B_28),C_29) = k2_xboole_0(A_27,k2_xboole_0(B_28,C_29)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_89,plain,(
    ! [A_39,B_40,C_41] : k2_xboole_0(k1_tarski(A_39),k2_xboole_0(k1_tarski(B_40),C_41)) = k2_xboole_0(k2_tarski(A_39,B_40),C_41) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_42])).

tff(c_116,plain,(
    ! [A_39,A_6,B_7] : k2_xboole_0(k2_tarski(A_39,A_6),k1_tarski(B_7)) = k2_xboole_0(k1_tarski(A_39),k2_tarski(A_6,B_7)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_89])).

tff(c_122,plain,(
    ! [A_39,A_6,B_7] : k2_xboole_0(k2_tarski(A_39,A_6),k1_tarski(B_7)) = k1_enumset1(A_39,A_6,B_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_116])).

tff(c_147,plain,(
    ! [A_49,B_50,C_51,C_52] : k2_xboole_0(k1_tarski(A_49),k2_xboole_0(k2_tarski(B_50,C_51),C_52)) = k2_xboole_0(k1_enumset1(A_49,B_50,C_51),C_52) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_42])).

tff(c_165,plain,(
    ! [A_49,A_39,A_6,B_7] : k2_xboole_0(k1_enumset1(A_49,A_39,A_6),k1_tarski(B_7)) = k2_xboole_0(k1_tarski(A_49),k1_enumset1(A_39,A_6,B_7)) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_147])).

tff(c_170,plain,(
    ! [A_49,A_39,A_6,B_7] : k2_xboole_0(k1_enumset1(A_49,A_39,A_6),k1_tarski(B_7)) = k2_enumset1(A_49,A_39,A_6,B_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_165])).

tff(c_65,plain,(
    ! [A_30,B_31,C_32,D_33] : k2_xboole_0(k1_tarski(A_30),k1_enumset1(B_31,C_32,D_33)) = k2_enumset1(A_30,B_31,C_32,D_33) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_xboole_0(k2_xboole_0(A_1,B_2),C_3) = k2_xboole_0(A_1,k2_xboole_0(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_246,plain,(
    ! [C_74,B_72,D_75,C_71,A_73] : k2_xboole_0(k1_tarski(A_73),k2_xboole_0(k1_enumset1(B_72,C_71,D_75),C_74)) = k2_xboole_0(k2_enumset1(A_73,B_72,C_71,D_75),C_74) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_2])).

tff(c_267,plain,(
    ! [B_7,A_49,A_39,A_73,A_6] : k2_xboole_0(k2_enumset1(A_73,A_49,A_39,A_6),k1_tarski(B_7)) = k2_xboole_0(k1_tarski(A_73),k2_enumset1(A_49,A_39,A_6,B_7)) ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_246])).

tff(c_271,plain,(
    ! [B_7,A_49,A_39,A_73,A_6] : k2_xboole_0(k2_enumset1(A_73,A_49,A_39,A_6),k1_tarski(B_7)) = k3_enumset1(A_73,A_49,A_39,A_6,B_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_267])).

tff(c_14,plain,(
    k2_xboole_0(k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4'),k1_tarski('#skF_5')) != k3_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_274,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_271,c_14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:17:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.07/1.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.07/1.23  
% 2.07/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.07/1.23  %$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.07/1.23  
% 2.07/1.23  %Foreground sorts:
% 2.07/1.23  
% 2.07/1.23  
% 2.07/1.23  %Background operators:
% 2.07/1.23  
% 2.07/1.23  
% 2.07/1.23  %Foreground operators:
% 2.07/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.07/1.23  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.07/1.23  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.07/1.23  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.07/1.23  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.07/1.23  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.07/1.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.07/1.23  tff('#skF_5', type, '#skF_5': $i).
% 2.07/1.23  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.07/1.23  tff('#skF_2', type, '#skF_2': $i).
% 2.07/1.23  tff('#skF_3', type, '#skF_3': $i).
% 2.07/1.23  tff('#skF_1', type, '#skF_1': $i).
% 2.07/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.07/1.23  tff('#skF_4', type, '#skF_4': $i).
% 2.07/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.07/1.23  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.07/1.23  
% 2.07/1.24  tff(f_37, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_tarski(A), k2_enumset1(B, C, D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_enumset1)).
% 2.07/1.24  tff(f_35, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_enumset1)).
% 2.07/1.24  tff(f_33, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_enumset1)).
% 2.07/1.24  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 2.07/1.24  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 2.07/1.24  tff(f_40, negated_conjecture, ~(![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_tarski(E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_enumset1)).
% 2.07/1.24  tff(c_12, plain, (![B_16, A_15, D_18, E_19, C_17]: (k2_xboole_0(k1_tarski(A_15), k2_enumset1(B_16, C_17, D_18, E_19))=k3_enumset1(A_15, B_16, C_17, D_18, E_19))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.07/1.24  tff(c_10, plain, (![A_11, B_12, C_13, D_14]: (k2_xboole_0(k1_tarski(A_11), k1_enumset1(B_12, C_13, D_14))=k2_enumset1(A_11, B_12, C_13, D_14))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.07/1.24  tff(c_8, plain, (![A_8, B_9, C_10]: (k2_xboole_0(k1_tarski(A_8), k2_tarski(B_9, C_10))=k1_enumset1(A_8, B_9, C_10))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.07/1.24  tff(c_6, plain, (![A_6, B_7]: (k2_xboole_0(k1_tarski(A_6), k1_tarski(B_7))=k2_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.07/1.24  tff(c_42, plain, (![A_27, B_28, C_29]: (k2_xboole_0(k2_xboole_0(A_27, B_28), C_29)=k2_xboole_0(A_27, k2_xboole_0(B_28, C_29)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.07/1.24  tff(c_89, plain, (![A_39, B_40, C_41]: (k2_xboole_0(k1_tarski(A_39), k2_xboole_0(k1_tarski(B_40), C_41))=k2_xboole_0(k2_tarski(A_39, B_40), C_41))), inference(superposition, [status(thm), theory('equality')], [c_6, c_42])).
% 2.07/1.24  tff(c_116, plain, (![A_39, A_6, B_7]: (k2_xboole_0(k2_tarski(A_39, A_6), k1_tarski(B_7))=k2_xboole_0(k1_tarski(A_39), k2_tarski(A_6, B_7)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_89])).
% 2.07/1.24  tff(c_122, plain, (![A_39, A_6, B_7]: (k2_xboole_0(k2_tarski(A_39, A_6), k1_tarski(B_7))=k1_enumset1(A_39, A_6, B_7))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_116])).
% 2.07/1.24  tff(c_147, plain, (![A_49, B_50, C_51, C_52]: (k2_xboole_0(k1_tarski(A_49), k2_xboole_0(k2_tarski(B_50, C_51), C_52))=k2_xboole_0(k1_enumset1(A_49, B_50, C_51), C_52))), inference(superposition, [status(thm), theory('equality')], [c_8, c_42])).
% 2.07/1.24  tff(c_165, plain, (![A_49, A_39, A_6, B_7]: (k2_xboole_0(k1_enumset1(A_49, A_39, A_6), k1_tarski(B_7))=k2_xboole_0(k1_tarski(A_49), k1_enumset1(A_39, A_6, B_7)))), inference(superposition, [status(thm), theory('equality')], [c_122, c_147])).
% 2.07/1.24  tff(c_170, plain, (![A_49, A_39, A_6, B_7]: (k2_xboole_0(k1_enumset1(A_49, A_39, A_6), k1_tarski(B_7))=k2_enumset1(A_49, A_39, A_6, B_7))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_165])).
% 2.07/1.24  tff(c_65, plain, (![A_30, B_31, C_32, D_33]: (k2_xboole_0(k1_tarski(A_30), k1_enumset1(B_31, C_32, D_33))=k2_enumset1(A_30, B_31, C_32, D_33))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.07/1.24  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_xboole_0(k2_xboole_0(A_1, B_2), C_3)=k2_xboole_0(A_1, k2_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.07/1.24  tff(c_246, plain, (![C_74, B_72, D_75, C_71, A_73]: (k2_xboole_0(k1_tarski(A_73), k2_xboole_0(k1_enumset1(B_72, C_71, D_75), C_74))=k2_xboole_0(k2_enumset1(A_73, B_72, C_71, D_75), C_74))), inference(superposition, [status(thm), theory('equality')], [c_65, c_2])).
% 2.07/1.24  tff(c_267, plain, (![B_7, A_49, A_39, A_73, A_6]: (k2_xboole_0(k2_enumset1(A_73, A_49, A_39, A_6), k1_tarski(B_7))=k2_xboole_0(k1_tarski(A_73), k2_enumset1(A_49, A_39, A_6, B_7)))), inference(superposition, [status(thm), theory('equality')], [c_170, c_246])).
% 2.07/1.24  tff(c_271, plain, (![B_7, A_49, A_39, A_73, A_6]: (k2_xboole_0(k2_enumset1(A_73, A_49, A_39, A_6), k1_tarski(B_7))=k3_enumset1(A_73, A_49, A_39, A_6, B_7))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_267])).
% 2.07/1.24  tff(c_14, plain, (k2_xboole_0(k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_tarski('#skF_5'))!=k3_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.07/1.24  tff(c_274, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_271, c_14])).
% 2.07/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.07/1.24  
% 2.07/1.24  Inference rules
% 2.07/1.24  ----------------------
% 2.07/1.24  #Ref     : 0
% 2.07/1.24  #Sup     : 66
% 2.07/1.24  #Fact    : 0
% 2.07/1.24  #Define  : 0
% 2.07/1.24  #Split   : 0
% 2.07/1.24  #Chain   : 0
% 2.07/1.24  #Close   : 0
% 2.07/1.24  
% 2.07/1.24  Ordering : KBO
% 2.07/1.24  
% 2.07/1.24  Simplification rules
% 2.07/1.24  ----------------------
% 2.07/1.24  #Subsume      : 0
% 2.07/1.24  #Demod        : 29
% 2.07/1.24  #Tautology    : 38
% 2.07/1.24  #SimpNegUnit  : 0
% 2.07/1.24  #BackRed      : 1
% 2.07/1.24  
% 2.07/1.24  #Partial instantiations: 0
% 2.07/1.24  #Strategies tried      : 1
% 2.07/1.24  
% 2.07/1.24  Timing (in seconds)
% 2.07/1.24  ----------------------
% 2.15/1.24  Preprocessing        : 0.26
% 2.15/1.24  Parsing              : 0.15
% 2.15/1.24  CNF conversion       : 0.02
% 2.15/1.24  Main loop            : 0.21
% 2.15/1.24  Inferencing          : 0.10
% 2.15/1.24  Reduction            : 0.06
% 2.15/1.24  Demodulation         : 0.05
% 2.15/1.24  BG Simplification    : 0.01
% 2.15/1.25  Subsumption          : 0.02
% 2.15/1.25  Abstraction          : 0.01
% 2.15/1.25  MUC search           : 0.00
% 2.15/1.25  Cooper               : 0.00
% 2.15/1.25  Total                : 0.49
% 2.15/1.25  Index Insertion      : 0.00
% 2.15/1.25  Index Deletion       : 0.00
% 2.15/1.25  Index Matching       : 0.00
% 2.15/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
