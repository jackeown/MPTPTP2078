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
% DateTime   : Thu Dec  3 09:45:44 EST 2020

% Result     : Theorem 2.25s
% Output     : CNFRefutation 2.58s
% Verified   : 
% Statistics : Number of formulae       :   40 (  41 expanded)
%              Number of leaves         :   25 (  26 expanded)
%              Depth                    :    7
%              Number of atoms          :   22 (  23 expanded)
%              Number of equality atoms :   21 (  22 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_39,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_tarski(A),k3_enumset1(B,C,D,E,F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_tarski(A),k2_enumset1(B,C,D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

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
    ~ ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_enumset1(A,B,C),k1_enumset1(D,E,F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_enumset1)).

tff(c_14,plain,(
    ! [C_22,D_23,A_20,B_21,F_25,E_24] : k2_xboole_0(k1_tarski(A_20),k3_enumset1(B_21,C_22,D_23,E_24,F_25)) = k4_enumset1(A_20,B_21,C_22,D_23,E_24,F_25) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_12,plain,(
    ! [B_16,A_15,D_18,E_19,C_17] : k2_xboole_0(k1_tarski(A_15),k2_enumset1(B_16,C_17,D_18,E_19)) = k3_enumset1(A_15,B_16,C_17,D_18,E_19) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [A_11,B_12,C_13,D_14] : k2_xboole_0(k1_tarski(A_11),k1_enumset1(B_12,C_13,D_14)) = k2_enumset1(A_11,B_12,C_13,D_14) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6,plain,(
    ! [A_6,B_7] : k2_xboole_0(k1_tarski(A_6),k1_tarski(B_7)) = k2_tarski(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_35,plain,(
    ! [A_30,B_31,C_32] : k2_xboole_0(k2_xboole_0(A_30,B_31),C_32) = k2_xboole_0(A_30,k2_xboole_0(B_31,C_32)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_91,plain,(
    ! [A_45,B_46,C_47] : k2_xboole_0(k1_tarski(A_45),k2_xboole_0(k1_tarski(B_46),C_47)) = k2_xboole_0(k2_tarski(A_45,B_46),C_47) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_35])).

tff(c_112,plain,(
    ! [A_45,D_14,B_12,A_11,C_13] : k2_xboole_0(k2_tarski(A_45,A_11),k1_enumset1(B_12,C_13,D_14)) = k2_xboole_0(k1_tarski(A_45),k2_enumset1(A_11,B_12,C_13,D_14)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_91])).

tff(c_185,plain,(
    ! [B_66,A_65,D_67,C_63,A_64] : k2_xboole_0(k2_tarski(A_64,A_65),k1_enumset1(B_66,C_63,D_67)) = k3_enumset1(A_64,A_65,B_66,C_63,D_67) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_112])).

tff(c_55,plain,(
    ! [A_33,B_34,C_35] : k2_xboole_0(k1_tarski(A_33),k2_tarski(B_34,C_35)) = k1_enumset1(A_33,B_34,C_35) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_xboole_0(k2_xboole_0(A_1,B_2),C_3) = k2_xboole_0(A_1,k2_xboole_0(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_61,plain,(
    ! [A_33,B_34,C_35,C_3] : k2_xboole_0(k1_tarski(A_33),k2_xboole_0(k2_tarski(B_34,C_35),C_3)) = k2_xboole_0(k1_enumset1(A_33,B_34,C_35),C_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_2])).

tff(c_191,plain,(
    ! [B_66,A_65,D_67,C_63,A_33,A_64] : k2_xboole_0(k1_enumset1(A_33,A_64,A_65),k1_enumset1(B_66,C_63,D_67)) = k2_xboole_0(k1_tarski(A_33),k3_enumset1(A_64,A_65,B_66,C_63,D_67)) ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_61])).

tff(c_512,plain,(
    ! [B_66,A_65,D_67,C_63,A_33,A_64] : k2_xboole_0(k1_enumset1(A_33,A_64,A_65),k1_enumset1(B_66,C_63,D_67)) = k4_enumset1(A_33,A_64,A_65,B_66,C_63,D_67) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_191])).

tff(c_16,plain,(
    k2_xboole_0(k1_enumset1('#skF_1','#skF_2','#skF_3'),k1_enumset1('#skF_4','#skF_5','#skF_6')) != k4_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_515,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_512,c_16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:55:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.25/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.58/1.33  
% 2.58/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.58/1.33  %$ k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.58/1.33  
% 2.58/1.33  %Foreground sorts:
% 2.58/1.33  
% 2.58/1.33  
% 2.58/1.33  %Background operators:
% 2.58/1.33  
% 2.58/1.33  
% 2.58/1.33  %Foreground operators:
% 2.58/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.58/1.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.58/1.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.58/1.33  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.58/1.33  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.58/1.33  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.58/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.58/1.33  tff('#skF_5', type, '#skF_5': $i).
% 2.58/1.33  tff('#skF_6', type, '#skF_6': $i).
% 2.58/1.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.58/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.58/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.58/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.58/1.33  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.58/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.58/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.58/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.58/1.33  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.58/1.33  
% 2.58/1.34  tff(f_39, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_tarski(A), k3_enumset1(B, C, D, E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_enumset1)).
% 2.58/1.34  tff(f_37, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_tarski(A), k2_enumset1(B, C, D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_enumset1)).
% 2.58/1.34  tff(f_35, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_enumset1)).
% 2.58/1.34  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 2.58/1.34  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 2.58/1.34  tff(f_33, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_enumset1)).
% 2.58/1.34  tff(f_42, negated_conjecture, ~(![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_enumset1(A, B, C), k1_enumset1(D, E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_enumset1)).
% 2.58/1.34  tff(c_14, plain, (![C_22, D_23, A_20, B_21, F_25, E_24]: (k2_xboole_0(k1_tarski(A_20), k3_enumset1(B_21, C_22, D_23, E_24, F_25))=k4_enumset1(A_20, B_21, C_22, D_23, E_24, F_25))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.58/1.34  tff(c_12, plain, (![B_16, A_15, D_18, E_19, C_17]: (k2_xboole_0(k1_tarski(A_15), k2_enumset1(B_16, C_17, D_18, E_19))=k3_enumset1(A_15, B_16, C_17, D_18, E_19))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.58/1.34  tff(c_10, plain, (![A_11, B_12, C_13, D_14]: (k2_xboole_0(k1_tarski(A_11), k1_enumset1(B_12, C_13, D_14))=k2_enumset1(A_11, B_12, C_13, D_14))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.58/1.34  tff(c_6, plain, (![A_6, B_7]: (k2_xboole_0(k1_tarski(A_6), k1_tarski(B_7))=k2_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.58/1.34  tff(c_35, plain, (![A_30, B_31, C_32]: (k2_xboole_0(k2_xboole_0(A_30, B_31), C_32)=k2_xboole_0(A_30, k2_xboole_0(B_31, C_32)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.58/1.34  tff(c_91, plain, (![A_45, B_46, C_47]: (k2_xboole_0(k1_tarski(A_45), k2_xboole_0(k1_tarski(B_46), C_47))=k2_xboole_0(k2_tarski(A_45, B_46), C_47))), inference(superposition, [status(thm), theory('equality')], [c_6, c_35])).
% 2.58/1.34  tff(c_112, plain, (![A_45, D_14, B_12, A_11, C_13]: (k2_xboole_0(k2_tarski(A_45, A_11), k1_enumset1(B_12, C_13, D_14))=k2_xboole_0(k1_tarski(A_45), k2_enumset1(A_11, B_12, C_13, D_14)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_91])).
% 2.58/1.34  tff(c_185, plain, (![B_66, A_65, D_67, C_63, A_64]: (k2_xboole_0(k2_tarski(A_64, A_65), k1_enumset1(B_66, C_63, D_67))=k3_enumset1(A_64, A_65, B_66, C_63, D_67))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_112])).
% 2.58/1.34  tff(c_55, plain, (![A_33, B_34, C_35]: (k2_xboole_0(k1_tarski(A_33), k2_tarski(B_34, C_35))=k1_enumset1(A_33, B_34, C_35))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.58/1.34  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_xboole_0(k2_xboole_0(A_1, B_2), C_3)=k2_xboole_0(A_1, k2_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.58/1.34  tff(c_61, plain, (![A_33, B_34, C_35, C_3]: (k2_xboole_0(k1_tarski(A_33), k2_xboole_0(k2_tarski(B_34, C_35), C_3))=k2_xboole_0(k1_enumset1(A_33, B_34, C_35), C_3))), inference(superposition, [status(thm), theory('equality')], [c_55, c_2])).
% 2.58/1.34  tff(c_191, plain, (![B_66, A_65, D_67, C_63, A_33, A_64]: (k2_xboole_0(k1_enumset1(A_33, A_64, A_65), k1_enumset1(B_66, C_63, D_67))=k2_xboole_0(k1_tarski(A_33), k3_enumset1(A_64, A_65, B_66, C_63, D_67)))), inference(superposition, [status(thm), theory('equality')], [c_185, c_61])).
% 2.58/1.34  tff(c_512, plain, (![B_66, A_65, D_67, C_63, A_33, A_64]: (k2_xboole_0(k1_enumset1(A_33, A_64, A_65), k1_enumset1(B_66, C_63, D_67))=k4_enumset1(A_33, A_64, A_65, B_66, C_63, D_67))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_191])).
% 2.58/1.34  tff(c_16, plain, (k2_xboole_0(k1_enumset1('#skF_1', '#skF_2', '#skF_3'), k1_enumset1('#skF_4', '#skF_5', '#skF_6'))!=k4_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.58/1.34  tff(c_515, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_512, c_16])).
% 2.58/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.58/1.34  
% 2.58/1.34  Inference rules
% 2.58/1.34  ----------------------
% 2.58/1.34  #Ref     : 0
% 2.58/1.34  #Sup     : 130
% 2.58/1.34  #Fact    : 0
% 2.58/1.34  #Define  : 0
% 2.58/1.34  #Split   : 0
% 2.58/1.34  #Chain   : 0
% 2.58/1.34  #Close   : 0
% 2.58/1.34  
% 2.58/1.34  Ordering : KBO
% 2.58/1.34  
% 2.58/1.34  Simplification rules
% 2.58/1.34  ----------------------
% 2.58/1.34  #Subsume      : 0
% 2.58/1.34  #Demod        : 61
% 2.58/1.34  #Tautology    : 69
% 2.58/1.34  #SimpNegUnit  : 0
% 2.58/1.34  #BackRed      : 1
% 2.58/1.34  
% 2.58/1.34  #Partial instantiations: 0
% 2.58/1.34  #Strategies tried      : 1
% 2.58/1.34  
% 2.58/1.34  Timing (in seconds)
% 2.58/1.34  ----------------------
% 2.58/1.34  Preprocessing        : 0.26
% 2.58/1.34  Parsing              : 0.15
% 2.58/1.34  CNF conversion       : 0.02
% 2.58/1.34  Main loop            : 0.31
% 2.58/1.34  Inferencing          : 0.14
% 2.58/1.34  Reduction            : 0.10
% 2.58/1.34  Demodulation         : 0.08
% 2.58/1.34  BG Simplification    : 0.02
% 2.58/1.34  Subsumption          : 0.03
% 2.58/1.34  Abstraction          : 0.02
% 2.58/1.34  MUC search           : 0.00
% 2.58/1.34  Cooper               : 0.00
% 2.58/1.34  Total                : 0.60
% 2.58/1.34  Index Insertion      : 0.00
% 2.58/1.34  Index Deletion       : 0.00
% 2.58/1.34  Index Matching       : 0.00
% 2.58/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
