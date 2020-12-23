%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:01 EST 2020

% Result     : Theorem 2.02s
% Output     : CNFRefutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :   41 (  51 expanded)
%              Number of leaves         :   23 (  29 expanded)
%              Depth                    :    7
%              Number of atoms          :   24 (  34 expanded)
%              Number of equality atoms :   23 (  33 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k4_enumset1 > k3_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

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

tff(f_35,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k2_tarski(A,B),k4_enumset1(C,D,E,F,G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_enumset1)).

tff(f_29,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k1_tarski(F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_tarski(A),k3_enumset1(B,C,D,E,F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_enumset1)).

tff(f_38,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k4_enumset1(A,B,C,D,E,F),k2_tarski(G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_enumset1)).

tff(c_10,plain,(
    ! [H_25,E_22,G_24,D_21,F_23,A_18,C_20,B_19] : k2_xboole_0(k2_tarski(A_18,B_19),k4_enumset1(C_20,D_21,E_22,F_23,G_24,H_25)) = k6_enumset1(A_18,B_19,C_20,D_21,E_22,F_23,G_24,H_25) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4,plain,(
    ! [A_4,B_5] : k2_xboole_0(k1_tarski(A_4),k1_tarski(B_5)) = k2_tarski(A_4,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_22,plain,(
    ! [A_28,B_29,C_30] : k2_xboole_0(k2_xboole_0(A_28,B_29),C_30) = k2_xboole_0(A_28,k2_xboole_0(B_29,C_30)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_37,plain,(
    ! [A_4,B_5,C_30] : k2_xboole_0(k1_tarski(A_4),k2_xboole_0(k1_tarski(B_5),C_30)) = k2_xboole_0(k2_tarski(A_4,B_5),C_30) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_22])).

tff(c_8,plain,(
    ! [E_16,D_15,F_17,C_14,A_12,B_13] : k2_xboole_0(k3_enumset1(A_12,B_13,C_14,D_15,E_16),k1_tarski(F_17)) = k4_enumset1(A_12,B_13,C_14,D_15,E_16,F_17) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_77,plain,(
    ! [B_39,D_37,F_42,E_41,C_38,A_40] : k2_xboole_0(k1_tarski(A_40),k3_enumset1(B_39,C_38,D_37,E_41,F_42)) = k4_enumset1(A_40,B_39,C_38,D_37,E_41,F_42) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_xboole_0(k2_xboole_0(A_1,B_2),C_3) = k2_xboole_0(A_1,k2_xboole_0(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_164,plain,(
    ! [E_72,F_70,C_73,C_74,D_68,B_71,A_69] : k2_xboole_0(k1_tarski(A_69),k2_xboole_0(k3_enumset1(B_71,C_74,D_68,E_72,F_70),C_73)) = k2_xboole_0(k4_enumset1(A_69,B_71,C_74,D_68,E_72,F_70),C_73) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_2])).

tff(c_188,plain,(
    ! [E_16,D_15,F_17,C_14,A_12,B_13,A_69] : k2_xboole_0(k4_enumset1(A_69,A_12,B_13,C_14,D_15,E_16),k1_tarski(F_17)) = k2_xboole_0(k1_tarski(A_69),k4_enumset1(A_12,B_13,C_14,D_15,E_16,F_17)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_164])).

tff(c_92,plain,(
    ! [B_43,A_44,C_48,D_46,E_45,F_47] : k2_xboole_0(k3_enumset1(A_44,B_43,C_48,D_46,E_45),k1_tarski(F_47)) = k4_enumset1(A_44,B_43,C_48,D_46,E_45,F_47) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_142,plain,(
    ! [D_63,E_61,B_62,A_65,F_67,C_64,C_66] : k2_xboole_0(k3_enumset1(A_65,B_62,C_64,D_63,E_61),k2_xboole_0(k1_tarski(F_67),C_66)) = k2_xboole_0(k4_enumset1(A_65,B_62,C_64,D_63,E_61,F_67),C_66) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_2])).

tff(c_160,plain,(
    ! [D_63,E_61,B_5,B_62,A_65,A_4,C_64] : k2_xboole_0(k4_enumset1(A_65,B_62,C_64,D_63,E_61,A_4),k1_tarski(B_5)) = k2_xboole_0(k3_enumset1(A_65,B_62,C_64,D_63,E_61),k2_tarski(A_4,B_5)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_142])).

tff(c_248,plain,(
    ! [B_107,A_110,D_108,A_111,E_105,B_109,C_106] : k2_xboole_0(k3_enumset1(A_110,B_109,C_106,D_108,E_105),k2_tarski(A_111,B_107)) = k2_xboole_0(k1_tarski(A_110),k4_enumset1(B_109,C_106,D_108,E_105,A_111,B_107)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_160])).

tff(c_86,plain,(
    ! [B_39,D_37,C_3,F_42,E_41,C_38,A_40] : k2_xboole_0(k1_tarski(A_40),k2_xboole_0(k3_enumset1(B_39,C_38,D_37,E_41,F_42),C_3)) = k2_xboole_0(k4_enumset1(A_40,B_39,C_38,D_37,E_41,F_42),C_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_2])).

tff(c_254,plain,(
    ! [B_107,A_110,D_108,A_111,E_105,B_109,C_106,A_40] : k2_xboole_0(k1_tarski(A_40),k2_xboole_0(k1_tarski(A_110),k4_enumset1(B_109,C_106,D_108,E_105,A_111,B_107))) = k2_xboole_0(k4_enumset1(A_40,A_110,B_109,C_106,D_108,E_105),k2_tarski(A_111,B_107)) ),
    inference(superposition,[status(thm),theory(equality)],[c_248,c_86])).

tff(c_262,plain,(
    ! [B_107,A_110,D_108,A_111,E_105,B_109,C_106,A_40] : k2_xboole_0(k4_enumset1(A_40,A_110,B_109,C_106,D_108,E_105),k2_tarski(A_111,B_107)) = k6_enumset1(A_40,A_110,B_109,C_106,D_108,E_105,A_111,B_107) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_37,c_254])).

tff(c_12,plain,(
    k2_xboole_0(k4_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k2_tarski('#skF_7','#skF_8')) != k6_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_267,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_262,c_12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:45:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.02/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.31  
% 2.02/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.31  %$ k6_enumset1 > k4_enumset1 > k3_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 2.02/1.31  
% 2.02/1.31  %Foreground sorts:
% 2.02/1.31  
% 2.02/1.31  
% 2.02/1.31  %Background operators:
% 2.02/1.31  
% 2.02/1.31  
% 2.02/1.31  %Foreground operators:
% 2.02/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.02/1.31  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.02/1.31  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.02/1.31  tff('#skF_7', type, '#skF_7': $i).
% 2.02/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.02/1.31  tff('#skF_5', type, '#skF_5': $i).
% 2.02/1.31  tff('#skF_6', type, '#skF_6': $i).
% 2.02/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.02/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.02/1.31  tff('#skF_1', type, '#skF_1': $i).
% 2.02/1.31  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.02/1.31  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.02/1.31  tff('#skF_8', type, '#skF_8': $i).
% 2.02/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.02/1.31  tff('#skF_4', type, '#skF_4': $i).
% 2.02/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.02/1.31  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.02/1.31  
% 2.02/1.32  tff(f_35, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k2_tarski(A, B), k4_enumset1(C, D, E, F, G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_enumset1)).
% 2.02/1.32  tff(f_29, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 2.02/1.32  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 2.02/1.32  tff(f_33, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k1_tarski(F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_enumset1)).
% 2.02/1.32  tff(f_31, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_tarski(A), k3_enumset1(B, C, D, E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_enumset1)).
% 2.02/1.32  tff(f_38, negated_conjecture, ~(![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k4_enumset1(A, B, C, D, E, F), k2_tarski(G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_enumset1)).
% 2.02/1.32  tff(c_10, plain, (![H_25, E_22, G_24, D_21, F_23, A_18, C_20, B_19]: (k2_xboole_0(k2_tarski(A_18, B_19), k4_enumset1(C_20, D_21, E_22, F_23, G_24, H_25))=k6_enumset1(A_18, B_19, C_20, D_21, E_22, F_23, G_24, H_25))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.02/1.32  tff(c_4, plain, (![A_4, B_5]: (k2_xboole_0(k1_tarski(A_4), k1_tarski(B_5))=k2_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.02/1.32  tff(c_22, plain, (![A_28, B_29, C_30]: (k2_xboole_0(k2_xboole_0(A_28, B_29), C_30)=k2_xboole_0(A_28, k2_xboole_0(B_29, C_30)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.02/1.32  tff(c_37, plain, (![A_4, B_5, C_30]: (k2_xboole_0(k1_tarski(A_4), k2_xboole_0(k1_tarski(B_5), C_30))=k2_xboole_0(k2_tarski(A_4, B_5), C_30))), inference(superposition, [status(thm), theory('equality')], [c_4, c_22])).
% 2.02/1.32  tff(c_8, plain, (![E_16, D_15, F_17, C_14, A_12, B_13]: (k2_xboole_0(k3_enumset1(A_12, B_13, C_14, D_15, E_16), k1_tarski(F_17))=k4_enumset1(A_12, B_13, C_14, D_15, E_16, F_17))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.02/1.32  tff(c_77, plain, (![B_39, D_37, F_42, E_41, C_38, A_40]: (k2_xboole_0(k1_tarski(A_40), k3_enumset1(B_39, C_38, D_37, E_41, F_42))=k4_enumset1(A_40, B_39, C_38, D_37, E_41, F_42))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.02/1.32  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_xboole_0(k2_xboole_0(A_1, B_2), C_3)=k2_xboole_0(A_1, k2_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.02/1.32  tff(c_164, plain, (![E_72, F_70, C_73, C_74, D_68, B_71, A_69]: (k2_xboole_0(k1_tarski(A_69), k2_xboole_0(k3_enumset1(B_71, C_74, D_68, E_72, F_70), C_73))=k2_xboole_0(k4_enumset1(A_69, B_71, C_74, D_68, E_72, F_70), C_73))), inference(superposition, [status(thm), theory('equality')], [c_77, c_2])).
% 2.02/1.32  tff(c_188, plain, (![E_16, D_15, F_17, C_14, A_12, B_13, A_69]: (k2_xboole_0(k4_enumset1(A_69, A_12, B_13, C_14, D_15, E_16), k1_tarski(F_17))=k2_xboole_0(k1_tarski(A_69), k4_enumset1(A_12, B_13, C_14, D_15, E_16, F_17)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_164])).
% 2.02/1.32  tff(c_92, plain, (![B_43, A_44, C_48, D_46, E_45, F_47]: (k2_xboole_0(k3_enumset1(A_44, B_43, C_48, D_46, E_45), k1_tarski(F_47))=k4_enumset1(A_44, B_43, C_48, D_46, E_45, F_47))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.02/1.32  tff(c_142, plain, (![D_63, E_61, B_62, A_65, F_67, C_64, C_66]: (k2_xboole_0(k3_enumset1(A_65, B_62, C_64, D_63, E_61), k2_xboole_0(k1_tarski(F_67), C_66))=k2_xboole_0(k4_enumset1(A_65, B_62, C_64, D_63, E_61, F_67), C_66))), inference(superposition, [status(thm), theory('equality')], [c_92, c_2])).
% 2.02/1.32  tff(c_160, plain, (![D_63, E_61, B_5, B_62, A_65, A_4, C_64]: (k2_xboole_0(k4_enumset1(A_65, B_62, C_64, D_63, E_61, A_4), k1_tarski(B_5))=k2_xboole_0(k3_enumset1(A_65, B_62, C_64, D_63, E_61), k2_tarski(A_4, B_5)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_142])).
% 2.02/1.32  tff(c_248, plain, (![B_107, A_110, D_108, A_111, E_105, B_109, C_106]: (k2_xboole_0(k3_enumset1(A_110, B_109, C_106, D_108, E_105), k2_tarski(A_111, B_107))=k2_xboole_0(k1_tarski(A_110), k4_enumset1(B_109, C_106, D_108, E_105, A_111, B_107)))), inference(demodulation, [status(thm), theory('equality')], [c_188, c_160])).
% 2.02/1.32  tff(c_86, plain, (![B_39, D_37, C_3, F_42, E_41, C_38, A_40]: (k2_xboole_0(k1_tarski(A_40), k2_xboole_0(k3_enumset1(B_39, C_38, D_37, E_41, F_42), C_3))=k2_xboole_0(k4_enumset1(A_40, B_39, C_38, D_37, E_41, F_42), C_3))), inference(superposition, [status(thm), theory('equality')], [c_77, c_2])).
% 2.02/1.32  tff(c_254, plain, (![B_107, A_110, D_108, A_111, E_105, B_109, C_106, A_40]: (k2_xboole_0(k1_tarski(A_40), k2_xboole_0(k1_tarski(A_110), k4_enumset1(B_109, C_106, D_108, E_105, A_111, B_107)))=k2_xboole_0(k4_enumset1(A_40, A_110, B_109, C_106, D_108, E_105), k2_tarski(A_111, B_107)))), inference(superposition, [status(thm), theory('equality')], [c_248, c_86])).
% 2.02/1.32  tff(c_262, plain, (![B_107, A_110, D_108, A_111, E_105, B_109, C_106, A_40]: (k2_xboole_0(k4_enumset1(A_40, A_110, B_109, C_106, D_108, E_105), k2_tarski(A_111, B_107))=k6_enumset1(A_40, A_110, B_109, C_106, D_108, E_105, A_111, B_107))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_37, c_254])).
% 2.02/1.32  tff(c_12, plain, (k2_xboole_0(k4_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k2_tarski('#skF_7', '#skF_8'))!=k6_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.02/1.32  tff(c_267, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_262, c_12])).
% 2.02/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.32  
% 2.02/1.32  Inference rules
% 2.02/1.32  ----------------------
% 2.02/1.32  #Ref     : 0
% 2.02/1.32  #Sup     : 63
% 2.02/1.32  #Fact    : 0
% 2.02/1.32  #Define  : 0
% 2.02/1.32  #Split   : 0
% 2.02/1.32  #Chain   : 0
% 2.02/1.32  #Close   : 0
% 2.02/1.32  
% 2.02/1.32  Ordering : KBO
% 2.02/1.32  
% 2.02/1.32  Simplification rules
% 2.02/1.32  ----------------------
% 2.02/1.32  #Subsume      : 0
% 2.02/1.32  #Demod        : 37
% 2.02/1.32  #Tautology    : 41
% 2.02/1.32  #SimpNegUnit  : 0
% 2.02/1.32  #BackRed      : 2
% 2.02/1.32  
% 2.02/1.32  #Partial instantiations: 0
% 2.02/1.32  #Strategies tried      : 1
% 2.02/1.32  
% 2.02/1.32  Timing (in seconds)
% 2.02/1.32  ----------------------
% 2.39/1.32  Preprocessing        : 0.29
% 2.39/1.32  Parsing              : 0.16
% 2.39/1.32  CNF conversion       : 0.02
% 2.39/1.32  Main loop            : 0.23
% 2.39/1.32  Inferencing          : 0.11
% 2.39/1.32  Reduction            : 0.07
% 2.39/1.32  Demodulation         : 0.06
% 2.39/1.32  BG Simplification    : 0.02
% 2.39/1.32  Subsumption          : 0.03
% 2.39/1.32  Abstraction          : 0.02
% 2.39/1.32  MUC search           : 0.00
% 2.39/1.32  Cooper               : 0.00
% 2.39/1.32  Total                : 0.55
% 2.39/1.32  Index Insertion      : 0.00
% 2.39/1.32  Index Deletion       : 0.00
% 2.39/1.32  Index Matching       : 0.00
% 2.39/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
