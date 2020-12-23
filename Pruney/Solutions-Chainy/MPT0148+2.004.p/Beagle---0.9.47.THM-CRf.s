%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:57 EST 2020

% Result     : Theorem 5.61s
% Output     : CNFRefutation 5.61s
% Verified   : 
% Statistics : Number of formulae       :   47 (  54 expanded)
%              Number of leaves         :   29 (  33 expanded)
%              Depth                    :    7
%              Number of atoms          :   25 (  32 expanded)
%              Number of equality atoms :   24 (  31 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_45,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k2_tarski(A,B),k4_enumset1(C,D,E,F,G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k1_tarski(A),k4_enumset1(B,C,D,E,F,G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_enumset1)).

tff(f_35,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_tarski(A),k3_enumset1(B,C,D,E,F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_48,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k1_enumset1(A,B,C),k3_enumset1(D,E,F,G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_enumset1)).

tff(c_20,plain,(
    ! [E_44,H_47,C_42,G_46,F_45,A_40,D_43,B_41] : k2_xboole_0(k2_tarski(A_40,B_41),k4_enumset1(C_42,D_43,E_44,F_45,G_46,H_47)) = k6_enumset1(A_40,B_41,C_42,D_43,E_44,F_45,G_46,H_47) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_537,plain,(
    ! [C_108,A_106,F_109,D_110,G_111,E_107,B_112] : k2_xboole_0(k1_tarski(A_106),k4_enumset1(B_112,C_108,D_110,E_107,F_109,G_111)) = k5_enumset1(A_106,B_112,C_108,D_110,E_107,F_109,G_111) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_10,plain,(
    ! [A_17,B_18] : k2_xboole_0(k1_tarski(A_17),k1_tarski(B_18)) = k2_tarski(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_41,plain,(
    ! [A_52,B_53,C_54] : k2_xboole_0(k2_xboole_0(A_52,B_53),C_54) = k2_xboole_0(A_52,k2_xboole_0(B_53,C_54)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_56,plain,(
    ! [A_17,B_18,C_54] : k2_xboole_0(k1_tarski(A_17),k2_xboole_0(k1_tarski(B_18),C_54)) = k2_xboole_0(k2_tarski(A_17,B_18),C_54) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_41])).

tff(c_555,plain,(
    ! [C_108,A_106,F_109,A_17,D_110,G_111,E_107,B_112] : k2_xboole_0(k2_tarski(A_17,A_106),k4_enumset1(B_112,C_108,D_110,E_107,F_109,G_111)) = k2_xboole_0(k1_tarski(A_17),k5_enumset1(A_106,B_112,C_108,D_110,E_107,F_109,G_111)) ),
    inference(superposition,[status(thm),theory(equality)],[c_537,c_56])).

tff(c_2512,plain,(
    ! [C_108,A_106,F_109,A_17,D_110,G_111,E_107,B_112] : k2_xboole_0(k1_tarski(A_17),k5_enumset1(A_106,B_112,C_108,D_110,E_107,F_109,G_111)) = k6_enumset1(A_17,A_106,B_112,C_108,D_110,E_107,F_109,G_111) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_555])).

tff(c_18,plain,(
    ! [D_36,G_39,F_38,E_37,A_33,B_34,C_35] : k2_xboole_0(k1_tarski(A_33),k4_enumset1(B_34,C_35,D_36,E_37,F_38,G_39)) = k5_enumset1(A_33,B_34,C_35,D_36,E_37,F_38,G_39) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_298,plain,(
    ! [D_92,A_95,B_94,F_90,C_91,E_93] : k2_xboole_0(k1_tarski(A_95),k3_enumset1(B_94,C_91,D_92,E_93,F_90)) = k4_enumset1(A_95,B_94,C_91,D_92,E_93,F_90) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_304,plain,(
    ! [D_92,A_95,B_94,F_90,C_91,A_17,E_93] : k2_xboole_0(k2_tarski(A_17,A_95),k3_enumset1(B_94,C_91,D_92,E_93,F_90)) = k2_xboole_0(k1_tarski(A_17),k4_enumset1(A_95,B_94,C_91,D_92,E_93,F_90)) ),
    inference(superposition,[status(thm),theory(equality)],[c_298,c_56])).

tff(c_1582,plain,(
    ! [D_201,B_196,C_197,A_198,E_202,A_199,F_200] : k2_xboole_0(k2_tarski(A_198,A_199),k3_enumset1(B_196,C_197,D_201,E_202,F_200)) = k5_enumset1(A_198,A_199,B_196,C_197,D_201,E_202,F_200) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_304])).

tff(c_89,plain,(
    ! [A_58,B_59,C_60] : k2_xboole_0(k1_tarski(A_58),k2_tarski(B_59,C_60)) = k1_enumset1(A_58,B_59,C_60) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_xboole_0(k2_xboole_0(A_1,B_2),C_3) = k2_xboole_0(A_1,k2_xboole_0(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_95,plain,(
    ! [A_58,B_59,C_60,C_3] : k2_xboole_0(k1_tarski(A_58),k2_xboole_0(k2_tarski(B_59,C_60),C_3)) = k2_xboole_0(k1_enumset1(A_58,B_59,C_60),C_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_2])).

tff(c_1609,plain,(
    ! [A_58,D_201,B_196,C_197,A_198,E_202,A_199,F_200] : k2_xboole_0(k1_enumset1(A_58,A_198,A_199),k3_enumset1(B_196,C_197,D_201,E_202,F_200)) = k2_xboole_0(k1_tarski(A_58),k5_enumset1(A_198,A_199,B_196,C_197,D_201,E_202,F_200)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1582,c_95])).

tff(c_2815,plain,(
    ! [A_58,D_201,B_196,C_197,A_198,E_202,A_199,F_200] : k2_xboole_0(k1_enumset1(A_58,A_198,A_199),k3_enumset1(B_196,C_197,D_201,E_202,F_200)) = k6_enumset1(A_58,A_198,A_199,B_196,C_197,D_201,E_202,F_200) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2512,c_1609])).

tff(c_22,plain,(
    k2_xboole_0(k1_enumset1('#skF_1','#skF_2','#skF_3'),k3_enumset1('#skF_4','#skF_5','#skF_6','#skF_7','#skF_8')) != k6_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2818,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2815,c_22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 14:37:41 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.61/2.08  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.61/2.08  
% 5.61/2.08  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.61/2.09  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 5.61/2.09  
% 5.61/2.09  %Foreground sorts:
% 5.61/2.09  
% 5.61/2.09  
% 5.61/2.09  %Background operators:
% 5.61/2.09  
% 5.61/2.09  
% 5.61/2.09  %Foreground operators:
% 5.61/2.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.61/2.09  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.61/2.09  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.61/2.09  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.61/2.09  tff('#skF_7', type, '#skF_7': $i).
% 5.61/2.09  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.61/2.09  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.61/2.09  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.61/2.09  tff('#skF_5', type, '#skF_5': $i).
% 5.61/2.09  tff('#skF_6', type, '#skF_6': $i).
% 5.61/2.09  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.61/2.09  tff('#skF_2', type, '#skF_2': $i).
% 5.61/2.09  tff('#skF_3', type, '#skF_3': $i).
% 5.61/2.09  tff('#skF_1', type, '#skF_1': $i).
% 5.61/2.09  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.61/2.09  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.61/2.09  tff('#skF_8', type, '#skF_8': $i).
% 5.61/2.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.61/2.09  tff('#skF_4', type, '#skF_4': $i).
% 5.61/2.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.61/2.09  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.61/2.09  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.61/2.09  
% 5.61/2.10  tff(f_45, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k2_tarski(A, B), k4_enumset1(C, D, E, F, G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_enumset1)).
% 5.61/2.10  tff(f_43, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k1_tarski(A), k4_enumset1(B, C, D, E, F, G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_enumset1)).
% 5.61/2.10  tff(f_35, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 5.61/2.10  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 5.61/2.10  tff(f_41, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_tarski(A), k3_enumset1(B, C, D, E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_enumset1)).
% 5.61/2.10  tff(f_37, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_enumset1)).
% 5.61/2.10  tff(f_48, negated_conjecture, ~(![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k1_enumset1(A, B, C), k3_enumset1(D, E, F, G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_enumset1)).
% 5.61/2.10  tff(c_20, plain, (![E_44, H_47, C_42, G_46, F_45, A_40, D_43, B_41]: (k2_xboole_0(k2_tarski(A_40, B_41), k4_enumset1(C_42, D_43, E_44, F_45, G_46, H_47))=k6_enumset1(A_40, B_41, C_42, D_43, E_44, F_45, G_46, H_47))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.61/2.10  tff(c_537, plain, (![C_108, A_106, F_109, D_110, G_111, E_107, B_112]: (k2_xboole_0(k1_tarski(A_106), k4_enumset1(B_112, C_108, D_110, E_107, F_109, G_111))=k5_enumset1(A_106, B_112, C_108, D_110, E_107, F_109, G_111))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.61/2.10  tff(c_10, plain, (![A_17, B_18]: (k2_xboole_0(k1_tarski(A_17), k1_tarski(B_18))=k2_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.61/2.10  tff(c_41, plain, (![A_52, B_53, C_54]: (k2_xboole_0(k2_xboole_0(A_52, B_53), C_54)=k2_xboole_0(A_52, k2_xboole_0(B_53, C_54)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.61/2.10  tff(c_56, plain, (![A_17, B_18, C_54]: (k2_xboole_0(k1_tarski(A_17), k2_xboole_0(k1_tarski(B_18), C_54))=k2_xboole_0(k2_tarski(A_17, B_18), C_54))), inference(superposition, [status(thm), theory('equality')], [c_10, c_41])).
% 5.61/2.10  tff(c_555, plain, (![C_108, A_106, F_109, A_17, D_110, G_111, E_107, B_112]: (k2_xboole_0(k2_tarski(A_17, A_106), k4_enumset1(B_112, C_108, D_110, E_107, F_109, G_111))=k2_xboole_0(k1_tarski(A_17), k5_enumset1(A_106, B_112, C_108, D_110, E_107, F_109, G_111)))), inference(superposition, [status(thm), theory('equality')], [c_537, c_56])).
% 5.61/2.10  tff(c_2512, plain, (![C_108, A_106, F_109, A_17, D_110, G_111, E_107, B_112]: (k2_xboole_0(k1_tarski(A_17), k5_enumset1(A_106, B_112, C_108, D_110, E_107, F_109, G_111))=k6_enumset1(A_17, A_106, B_112, C_108, D_110, E_107, F_109, G_111))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_555])).
% 5.61/2.10  tff(c_18, plain, (![D_36, G_39, F_38, E_37, A_33, B_34, C_35]: (k2_xboole_0(k1_tarski(A_33), k4_enumset1(B_34, C_35, D_36, E_37, F_38, G_39))=k5_enumset1(A_33, B_34, C_35, D_36, E_37, F_38, G_39))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.61/2.10  tff(c_298, plain, (![D_92, A_95, B_94, F_90, C_91, E_93]: (k2_xboole_0(k1_tarski(A_95), k3_enumset1(B_94, C_91, D_92, E_93, F_90))=k4_enumset1(A_95, B_94, C_91, D_92, E_93, F_90))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.61/2.10  tff(c_304, plain, (![D_92, A_95, B_94, F_90, C_91, A_17, E_93]: (k2_xboole_0(k2_tarski(A_17, A_95), k3_enumset1(B_94, C_91, D_92, E_93, F_90))=k2_xboole_0(k1_tarski(A_17), k4_enumset1(A_95, B_94, C_91, D_92, E_93, F_90)))), inference(superposition, [status(thm), theory('equality')], [c_298, c_56])).
% 5.61/2.10  tff(c_1582, plain, (![D_201, B_196, C_197, A_198, E_202, A_199, F_200]: (k2_xboole_0(k2_tarski(A_198, A_199), k3_enumset1(B_196, C_197, D_201, E_202, F_200))=k5_enumset1(A_198, A_199, B_196, C_197, D_201, E_202, F_200))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_304])).
% 5.61/2.10  tff(c_89, plain, (![A_58, B_59, C_60]: (k2_xboole_0(k1_tarski(A_58), k2_tarski(B_59, C_60))=k1_enumset1(A_58, B_59, C_60))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.61/2.10  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_xboole_0(k2_xboole_0(A_1, B_2), C_3)=k2_xboole_0(A_1, k2_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.61/2.10  tff(c_95, plain, (![A_58, B_59, C_60, C_3]: (k2_xboole_0(k1_tarski(A_58), k2_xboole_0(k2_tarski(B_59, C_60), C_3))=k2_xboole_0(k1_enumset1(A_58, B_59, C_60), C_3))), inference(superposition, [status(thm), theory('equality')], [c_89, c_2])).
% 5.61/2.10  tff(c_1609, plain, (![A_58, D_201, B_196, C_197, A_198, E_202, A_199, F_200]: (k2_xboole_0(k1_enumset1(A_58, A_198, A_199), k3_enumset1(B_196, C_197, D_201, E_202, F_200))=k2_xboole_0(k1_tarski(A_58), k5_enumset1(A_198, A_199, B_196, C_197, D_201, E_202, F_200)))), inference(superposition, [status(thm), theory('equality')], [c_1582, c_95])).
% 5.61/2.10  tff(c_2815, plain, (![A_58, D_201, B_196, C_197, A_198, E_202, A_199, F_200]: (k2_xboole_0(k1_enumset1(A_58, A_198, A_199), k3_enumset1(B_196, C_197, D_201, E_202, F_200))=k6_enumset1(A_58, A_198, A_199, B_196, C_197, D_201, E_202, F_200))), inference(demodulation, [status(thm), theory('equality')], [c_2512, c_1609])).
% 5.61/2.10  tff(c_22, plain, (k2_xboole_0(k1_enumset1('#skF_1', '#skF_2', '#skF_3'), k3_enumset1('#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'))!=k6_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.61/2.10  tff(c_2818, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2815, c_22])).
% 5.61/2.10  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.61/2.10  
% 5.61/2.10  Inference rules
% 5.61/2.10  ----------------------
% 5.61/2.10  #Ref     : 0
% 5.61/2.10  #Sup     : 704
% 5.61/2.10  #Fact    : 0
% 5.61/2.10  #Define  : 0
% 5.61/2.10  #Split   : 0
% 5.61/2.10  #Chain   : 0
% 5.61/2.10  #Close   : 0
% 5.61/2.10  
% 5.61/2.10  Ordering : KBO
% 5.61/2.10  
% 5.61/2.10  Simplification rules
% 5.61/2.10  ----------------------
% 5.61/2.10  #Subsume      : 0
% 5.61/2.10  #Demod        : 1432
% 5.61/2.10  #Tautology    : 332
% 5.61/2.10  #SimpNegUnit  : 0
% 5.61/2.10  #BackRed      : 1
% 5.61/2.10  
% 5.61/2.10  #Partial instantiations: 0
% 5.61/2.10  #Strategies tried      : 1
% 5.61/2.10  
% 5.61/2.10  Timing (in seconds)
% 5.61/2.10  ----------------------
% 5.61/2.10  Preprocessing        : 0.30
% 5.61/2.10  Parsing              : 0.16
% 5.61/2.10  CNF conversion       : 0.02
% 5.61/2.10  Main loop            : 1.08
% 5.61/2.10  Inferencing          : 0.40
% 5.61/2.10  Reduction            : 0.49
% 5.61/2.10  Demodulation         : 0.43
% 5.61/2.10  BG Simplification    : 0.06
% 5.61/2.10  Subsumption          : 0.09
% 5.61/2.10  Abstraction          : 0.12
% 5.61/2.10  MUC search           : 0.00
% 5.61/2.10  Cooper               : 0.00
% 5.61/2.10  Total                : 1.41
% 5.61/2.10  Index Insertion      : 0.00
% 5.61/2.10  Index Deletion       : 0.00
% 5.61/2.10  Index Matching       : 0.00
% 5.61/2.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
