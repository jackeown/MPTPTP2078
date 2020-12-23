%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:56 EST 2020

% Result     : Theorem 5.37s
% Output     : CNFRefutation 5.76s
% Verified   : 
% Statistics : Number of formulae       :   48 (  53 expanded)
%              Number of leaves         :   29 (  32 expanded)
%              Depth                    :    8
%              Number of atoms          :   27 (  32 expanded)
%              Number of equality atoms :   26 (  31 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

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

tff(f_33,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k2_enumset1(A,B,C,D),k2_enumset1(E,F,G,H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l75_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_tarski(A),k3_enumset1(B,C,D,E,F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_tarski(A),k2_enumset1(B,C,D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).

tff(f_35,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_46,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k2_tarski(A,B),k4_enumset1(C,D,E,F,G,H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_enumset1)).

tff(c_8,plain,(
    ! [C_11,E_13,B_10,H_16,F_14,G_15,D_12,A_9] : k2_xboole_0(k2_enumset1(A_9,B_10,C_11,D_12),k2_enumset1(E_13,F_14,G_15,H_16)) = k6_enumset1(A_9,B_10,C_11,D_12,E_13,F_14,G_15,H_16) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_18,plain,(
    ! [A_31,C_33,B_32,F_36,E_35,D_34] : k2_xboole_0(k1_tarski(A_31),k3_enumset1(B_32,C_33,D_34,E_35,F_36)) = k4_enumset1(A_31,B_32,C_33,D_34,E_35,F_36) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_198,plain,(
    ! [C_70,D_67,B_68,E_71,A_69] : k2_xboole_0(k1_tarski(A_69),k2_enumset1(B_68,C_70,D_67,E_71)) = k3_enumset1(A_69,B_68,C_70,D_67,E_71) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_10,plain,(
    ! [A_17,B_18] : k2_xboole_0(k1_tarski(A_17),k1_tarski(B_18)) = k2_tarski(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_67,plain,(
    ! [A_44,B_45,C_46] : k2_xboole_0(k2_xboole_0(A_44,B_45),C_46) = k2_xboole_0(A_44,k2_xboole_0(B_45,C_46)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_82,plain,(
    ! [A_17,B_18,C_46] : k2_xboole_0(k1_tarski(A_17),k2_xboole_0(k1_tarski(B_18),C_46)) = k2_xboole_0(k2_tarski(A_17,B_18),C_46) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_67])).

tff(c_204,plain,(
    ! [C_70,D_67,B_68,A_17,E_71,A_69] : k2_xboole_0(k2_tarski(A_17,A_69),k2_enumset1(B_68,C_70,D_67,E_71)) = k2_xboole_0(k1_tarski(A_17),k3_enumset1(A_69,B_68,C_70,D_67,E_71)) ),
    inference(superposition,[status(thm),theory(equality)],[c_198,c_82])).

tff(c_1175,plain,(
    ! [E_177,A_178,C_180,D_175,A_179,B_176] : k2_xboole_0(k2_tarski(A_178,A_179),k2_enumset1(B_176,C_180,D_175,E_177)) = k4_enumset1(A_178,A_179,B_176,C_180,D_175,E_177) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_204])).

tff(c_14,plain,(
    ! [A_22,B_23,C_24,D_25] : k2_xboole_0(k1_tarski(A_22),k1_enumset1(B_23,C_24,D_25)) = k2_enumset1(A_22,B_23,C_24,D_25) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_12,plain,(
    ! [A_19,B_20,C_21] : k2_xboole_0(k1_tarski(A_19),k2_tarski(B_20,C_21)) = k1_enumset1(A_19,B_20,C_21) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_111,plain,(
    ! [A_54,B_55,C_56] : k2_xboole_0(k1_tarski(A_54),k2_xboole_0(k1_tarski(B_55),C_56)) = k2_xboole_0(k2_tarski(A_54,B_55),C_56) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_67])).

tff(c_132,plain,(
    ! [A_54,A_19,B_20,C_21] : k2_xboole_0(k2_tarski(A_54,A_19),k2_tarski(B_20,C_21)) = k2_xboole_0(k1_tarski(A_54),k1_enumset1(A_19,B_20,C_21)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_111])).

tff(c_186,plain,(
    ! [A_63,A_64,B_65,C_66] : k2_xboole_0(k2_tarski(A_63,A_64),k2_tarski(B_65,C_66)) = k2_enumset1(A_63,A_64,B_65,C_66) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_132])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_xboole_0(k2_xboole_0(A_1,B_2),C_3) = k2_xboole_0(A_1,k2_xboole_0(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_192,plain,(
    ! [C_3,A_63,C_66,A_64,B_65] : k2_xboole_0(k2_tarski(A_63,A_64),k2_xboole_0(k2_tarski(B_65,C_66),C_3)) = k2_xboole_0(k2_enumset1(A_63,A_64,B_65,C_66),C_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_186,c_2])).

tff(c_1181,plain,(
    ! [E_177,A_178,C_180,A_63,D_175,A_179,A_64,B_176] : k2_xboole_0(k2_enumset1(A_63,A_64,A_178,A_179),k2_enumset1(B_176,C_180,D_175,E_177)) = k2_xboole_0(k2_tarski(A_63,A_64),k4_enumset1(A_178,A_179,B_176,C_180,D_175,E_177)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1175,c_192])).

tff(c_1204,plain,(
    ! [E_177,A_178,C_180,A_63,D_175,A_179,A_64,B_176] : k2_xboole_0(k2_tarski(A_63,A_64),k4_enumset1(A_178,A_179,B_176,C_180,D_175,E_177)) = k6_enumset1(A_63,A_64,A_178,A_179,B_176,C_180,D_175,E_177) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1181])).

tff(c_20,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),k4_enumset1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8')) != k6_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2869,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1204,c_20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:09:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.37/2.07  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.37/2.07  
% 5.37/2.07  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.37/2.08  %$ k6_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 5.37/2.08  
% 5.37/2.08  %Foreground sorts:
% 5.37/2.08  
% 5.37/2.08  
% 5.37/2.08  %Background operators:
% 5.37/2.08  
% 5.37/2.08  
% 5.37/2.08  %Foreground operators:
% 5.37/2.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.37/2.08  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.37/2.08  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.37/2.08  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.37/2.08  tff('#skF_7', type, '#skF_7': $i).
% 5.37/2.08  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.37/2.08  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.37/2.08  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.37/2.08  tff('#skF_5', type, '#skF_5': $i).
% 5.37/2.08  tff('#skF_6', type, '#skF_6': $i).
% 5.37/2.08  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.37/2.08  tff('#skF_2', type, '#skF_2': $i).
% 5.37/2.08  tff('#skF_3', type, '#skF_3': $i).
% 5.37/2.08  tff('#skF_1', type, '#skF_1': $i).
% 5.37/2.08  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.37/2.08  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.37/2.08  tff('#skF_8', type, '#skF_8': $i).
% 5.37/2.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.37/2.08  tff('#skF_4', type, '#skF_4': $i).
% 5.37/2.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.37/2.08  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.37/2.08  
% 5.76/2.09  tff(f_33, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k2_enumset1(A, B, C, D), k2_enumset1(E, F, G, H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l75_enumset1)).
% 5.76/2.09  tff(f_43, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_tarski(A), k3_enumset1(B, C, D, E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_enumset1)).
% 5.76/2.09  tff(f_41, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_tarski(A), k2_enumset1(B, C, D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_enumset1)).
% 5.76/2.09  tff(f_35, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 5.76/2.09  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 5.76/2.09  tff(f_39, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_enumset1)).
% 5.76/2.09  tff(f_37, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_enumset1)).
% 5.76/2.09  tff(f_46, negated_conjecture, ~(![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k2_tarski(A, B), k4_enumset1(C, D, E, F, G, H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_enumset1)).
% 5.76/2.09  tff(c_8, plain, (![C_11, E_13, B_10, H_16, F_14, G_15, D_12, A_9]: (k2_xboole_0(k2_enumset1(A_9, B_10, C_11, D_12), k2_enumset1(E_13, F_14, G_15, H_16))=k6_enumset1(A_9, B_10, C_11, D_12, E_13, F_14, G_15, H_16))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.76/2.09  tff(c_18, plain, (![A_31, C_33, B_32, F_36, E_35, D_34]: (k2_xboole_0(k1_tarski(A_31), k3_enumset1(B_32, C_33, D_34, E_35, F_36))=k4_enumset1(A_31, B_32, C_33, D_34, E_35, F_36))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.76/2.09  tff(c_198, plain, (![C_70, D_67, B_68, E_71, A_69]: (k2_xboole_0(k1_tarski(A_69), k2_enumset1(B_68, C_70, D_67, E_71))=k3_enumset1(A_69, B_68, C_70, D_67, E_71))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.76/2.09  tff(c_10, plain, (![A_17, B_18]: (k2_xboole_0(k1_tarski(A_17), k1_tarski(B_18))=k2_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.76/2.09  tff(c_67, plain, (![A_44, B_45, C_46]: (k2_xboole_0(k2_xboole_0(A_44, B_45), C_46)=k2_xboole_0(A_44, k2_xboole_0(B_45, C_46)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.76/2.09  tff(c_82, plain, (![A_17, B_18, C_46]: (k2_xboole_0(k1_tarski(A_17), k2_xboole_0(k1_tarski(B_18), C_46))=k2_xboole_0(k2_tarski(A_17, B_18), C_46))), inference(superposition, [status(thm), theory('equality')], [c_10, c_67])).
% 5.76/2.09  tff(c_204, plain, (![C_70, D_67, B_68, A_17, E_71, A_69]: (k2_xboole_0(k2_tarski(A_17, A_69), k2_enumset1(B_68, C_70, D_67, E_71))=k2_xboole_0(k1_tarski(A_17), k3_enumset1(A_69, B_68, C_70, D_67, E_71)))), inference(superposition, [status(thm), theory('equality')], [c_198, c_82])).
% 5.76/2.09  tff(c_1175, plain, (![E_177, A_178, C_180, D_175, A_179, B_176]: (k2_xboole_0(k2_tarski(A_178, A_179), k2_enumset1(B_176, C_180, D_175, E_177))=k4_enumset1(A_178, A_179, B_176, C_180, D_175, E_177))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_204])).
% 5.76/2.09  tff(c_14, plain, (![A_22, B_23, C_24, D_25]: (k2_xboole_0(k1_tarski(A_22), k1_enumset1(B_23, C_24, D_25))=k2_enumset1(A_22, B_23, C_24, D_25))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.76/2.09  tff(c_12, plain, (![A_19, B_20, C_21]: (k2_xboole_0(k1_tarski(A_19), k2_tarski(B_20, C_21))=k1_enumset1(A_19, B_20, C_21))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.76/2.09  tff(c_111, plain, (![A_54, B_55, C_56]: (k2_xboole_0(k1_tarski(A_54), k2_xboole_0(k1_tarski(B_55), C_56))=k2_xboole_0(k2_tarski(A_54, B_55), C_56))), inference(superposition, [status(thm), theory('equality')], [c_10, c_67])).
% 5.76/2.09  tff(c_132, plain, (![A_54, A_19, B_20, C_21]: (k2_xboole_0(k2_tarski(A_54, A_19), k2_tarski(B_20, C_21))=k2_xboole_0(k1_tarski(A_54), k1_enumset1(A_19, B_20, C_21)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_111])).
% 5.76/2.09  tff(c_186, plain, (![A_63, A_64, B_65, C_66]: (k2_xboole_0(k2_tarski(A_63, A_64), k2_tarski(B_65, C_66))=k2_enumset1(A_63, A_64, B_65, C_66))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_132])).
% 5.76/2.09  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_xboole_0(k2_xboole_0(A_1, B_2), C_3)=k2_xboole_0(A_1, k2_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.76/2.09  tff(c_192, plain, (![C_3, A_63, C_66, A_64, B_65]: (k2_xboole_0(k2_tarski(A_63, A_64), k2_xboole_0(k2_tarski(B_65, C_66), C_3))=k2_xboole_0(k2_enumset1(A_63, A_64, B_65, C_66), C_3))), inference(superposition, [status(thm), theory('equality')], [c_186, c_2])).
% 5.76/2.09  tff(c_1181, plain, (![E_177, A_178, C_180, A_63, D_175, A_179, A_64, B_176]: (k2_xboole_0(k2_enumset1(A_63, A_64, A_178, A_179), k2_enumset1(B_176, C_180, D_175, E_177))=k2_xboole_0(k2_tarski(A_63, A_64), k4_enumset1(A_178, A_179, B_176, C_180, D_175, E_177)))), inference(superposition, [status(thm), theory('equality')], [c_1175, c_192])).
% 5.76/2.09  tff(c_1204, plain, (![E_177, A_178, C_180, A_63, D_175, A_179, A_64, B_176]: (k2_xboole_0(k2_tarski(A_63, A_64), k4_enumset1(A_178, A_179, B_176, C_180, D_175, E_177))=k6_enumset1(A_63, A_64, A_178, A_179, B_176, C_180, D_175, E_177))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_1181])).
% 5.76/2.09  tff(c_20, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), k4_enumset1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'))!=k6_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.76/2.09  tff(c_2869, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1204, c_20])).
% 5.76/2.09  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.76/2.09  
% 5.76/2.09  Inference rules
% 5.76/2.09  ----------------------
% 5.76/2.09  #Ref     : 0
% 5.76/2.09  #Sup     : 722
% 5.76/2.09  #Fact    : 0
% 5.76/2.09  #Define  : 0
% 5.76/2.09  #Split   : 0
% 5.76/2.09  #Chain   : 0
% 5.76/2.09  #Close   : 0
% 5.76/2.09  
% 5.76/2.09  Ordering : KBO
% 5.76/2.09  
% 5.76/2.09  Simplification rules
% 5.76/2.09  ----------------------
% 5.76/2.09  #Subsume      : 0
% 5.76/2.09  #Demod        : 1398
% 5.76/2.09  #Tautology    : 336
% 5.76/2.09  #SimpNegUnit  : 0
% 5.76/2.09  #BackRed      : 1
% 5.76/2.09  
% 5.76/2.09  #Partial instantiations: 0
% 5.76/2.09  #Strategies tried      : 1
% 5.76/2.09  
% 5.76/2.10  Timing (in seconds)
% 5.76/2.10  ----------------------
% 5.76/2.10  Preprocessing        : 0.29
% 5.76/2.10  Parsing              : 0.16
% 5.76/2.10  CNF conversion       : 0.02
% 5.76/2.10  Main loop            : 1.04
% 5.76/2.10  Inferencing          : 0.36
% 5.76/2.10  Reduction            : 0.49
% 5.76/2.10  Demodulation         : 0.42
% 5.76/2.10  BG Simplification    : 0.08
% 5.76/2.10  Subsumption          : 0.08
% 5.76/2.10  Abstraction          : 0.10
% 5.76/2.10  MUC search           : 0.00
% 5.76/2.10  Cooper               : 0.00
% 5.76/2.10  Total                : 1.36
% 5.76/2.10  Index Insertion      : 0.00
% 5.76/2.10  Index Deletion       : 0.00
% 5.76/2.10  Index Matching       : 0.00
% 5.76/2.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
